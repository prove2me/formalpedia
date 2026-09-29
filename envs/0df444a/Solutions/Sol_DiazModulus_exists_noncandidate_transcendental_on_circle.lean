-- Prove2me | solution 1 for DiazModulus.exists_noncandidate_transcendental_on_circle
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T04:58:28.921996+00:00
-- url     : https://prove2.me/submissions/a88da9a7-cf7f-4e2a-8619-798a1c8119fc

import Mathlib

open ComplexConjugate

namespace P14Count

/-- Each fibre of `Complex.exp` is countable: two of its points differ by an integer
multiple of `2πi`. -/
theorem countable_exp_preimage (a : ℂ) : (Complex.exp ⁻¹' {a}).Countable := by
  rcases (Complex.exp ⁻¹' {a}).eq_empty_or_nonempty with h | ⟨z0, hz0⟩
  · rw [h]
    exact Set.countable_empty
  · refine (Set.countable_range (fun n : ℤ => z0 + n * (2 * Real.pi * Complex.I))).mono ?_
    intro z hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz hz0
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hz.trans hz0.symm)
    exact ⟨n, hn.symm⟩

/-- The set of `z` with `exp z` algebraic over `ℚ` is countable. -/
theorem countable_exp_algebraic : {z : ℂ | IsAlgebraic ℚ (Complex.exp z)}.Countable := by
  have hU : (⋃ a ∈ {a : ℂ | IsAlgebraic ℚ a}, Complex.exp ⁻¹' {a}).Countable :=
    (Algebraic.countable ℚ ℂ).biUnion (fun a _ => countable_exp_preimage a)
  refine hU.mono ?_
  intro z hz
  exact Set.mem_biUnion (x := Complex.exp z) hz rfl

end P14Count

open P14Count in
theorem solution (K : Subfield ℂ) (hK : Countable ↥K)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t : ℂ, t * conj t = (ρ : ℂ) ∧ Transcendental (↥K) t ∧
      Transcendental ℚ (Complex.exp t) := by
  -- the countable set of points to avoid
  let S : Set ℂ := {z : ℂ | IsAlgebraic (↥K) z} ∪ {z : ℂ | IsAlgebraic ℚ (Complex.exp z)}
  have hSc : S.Countable := (Algebraic.countable (↥K) ℂ).union countable_exp_algebraic
  -- the upper half of the circle `|t|^2 = ρ`, parametrised by the real part
  let T : ℝ → ℂ := fun x => ⟨x, Real.sqrt (ρ - x ^ 2)⟩
  have hT : Function.Injective T := by
    intro x y hxy
    have h := congrArg Complex.re hxy
    simpa [T] using h
  have hpre : (T ⁻¹' S).Countable := hSc.preimage hT
  have hr : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hIoo : ¬ (Set.Ioo (-Real.sqrt ρ) (Real.sqrt ρ)).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]
    linarith
  have hnsub : ¬ Set.Ioo (-Real.sqrt ρ) (Real.sqrt ρ) ⊆ T ⁻¹' S :=
    fun h => hIoo (hpre.mono h)
  obtain ⟨x, hx, hxS⟩ := Set.not_subset.mp hnsub
  have hx2 : x ^ 2 < ρ := by
    have h := sq_lt_sq' hx.1 hx.2
    rwa [Real.sq_sqrt hρ.le] at h
  refine ⟨T x, ?_, fun h => hxS (Or.inl h), fun h => hxS (Or.inr h)⟩
  rw [Complex.mul_conj, Complex.normSq_mk]
  have hs : Real.sqrt (ρ - x ^ 2) * Real.sqrt (ρ - x ^ 2) = ρ - x ^ 2 :=
    Real.mul_self_sqrt (sub_nonneg.mpr hx2.le)
  have h : x * x + Real.sqrt (ρ - x ^ 2) * Real.sqrt (ρ - x ^ 2) = ρ := by
    rw [hs]
    ring
  exact_mod_cast h

#print axioms solution
