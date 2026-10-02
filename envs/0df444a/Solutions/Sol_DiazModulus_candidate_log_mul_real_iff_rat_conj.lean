-- Prove2me | solution 1 for DiazModulus.candidate_log_mul_real_iff_rat_conj
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T08:45:06.691947+00:00
-- url     : https://prove2.me/submissions/4ede0a1c-5cb4-47d7-99ba-c4da3ba93fb5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin
import Theorems.Thm_DiazModulus_log_mul_real_trichotomy_of_trdeg_one
import Theorems.Thm_DiazModulus_log_mul_imaginary_mixed_of_trdeg_one

open Complex ComplexConjugate

namespace R2_candidate_log_mul_real_iff_rat_conj

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem rho_eq (u : ℂ) : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

/-- A candidate lies on neither axis: there `ū = ±u`, so `u² = ±|u|²` would be algebraic, and so
would `u`, against Hermite–Lindemann. -/
theorem cand_off_axes {u : ℂ} (hu : DiazModulus.IsCandidate u) : u.im ≠ 0 ∧ u.re ≠ 0 := by
  obtain ⟨hu0, hnorm, hexp⟩ := hu
  have hρ : IsAlgebraic ℚ (u * conj u) := by rw [rho_eq]; exact hnorm.pow 2
  have key : ∀ s : ℂ, (s = 1 ∨ s = -1) → conj u = s * u → False := by
    intro s hs hc
    have hsq : IsAlgebraic ℚ (u ^ 2) := by
      rcases hs with rfl | rfl
      · rw [hc, one_mul] at hρ; rw [sq]; exact hρ
      · have : u ^ 2 = -(u * conj u) := by rw [hc]; ring
        rw [this]; exact hρ.neg
    exact DiazModulus.hermite_lindemann_holds u hu0 (hsq.of_pow (by norm_num)) hexp
  refine ⟨fun h => key 1 (Or.inl rfl) ?_, fun h => key (-1) (Or.inr rfl) ?_⟩
  · rw [one_mul]; exact Complex.conj_eq_iff_im.2 h
  · apply Complex.ext <;> simp [h]

theorem self_alg (u : ℂ) : IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) u :=
  isAlgebraic_algebraMap (⟨u, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin ℚ ({u} : Set ℂ)))

theorem alg_of_alg {u z : ℂ} (h : IsAlgebraic ℚ z) :
    IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) z :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({u} : Set ℂ))).injective

/-- Conjugation carries "algebraic over `ℚ[u]`" to "algebraic over `ℚ[ū]`". -/
theorem conj_alg_adjoin {u μ : ℂ} (h : IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) μ) :
    IsAlgebraic ↥(Algebra.adjoin ℚ ({conj u} : Set ℂ)) (conj μ) := by
  have hmap : (Algebra.adjoin ℚ ({u} : Set ℂ)).map cjQ = Algebra.adjoin ℚ ({conj u} : Set ℂ) :=
    AlgHom.map_adjoin_singleton cjQ u
  let e := (Subalgebra.equivMapOfInjective (Algebra.adjoin ℚ ({u} : Set ℂ)) cjQ
    (RingHom.injective (cjQ : ℂ →+* ℂ))).trans (Subalgebra.equivOfEq _ _ hmap)
  exact IsAlgebraic.ringHom_of_comp_eq (f := e) (g := cjQ) h e.injective (by ext c; rfl)

/-- If `ū` is algebraic over `ℚ[u]`, so is `μ̄` for every `μ` algebraic over `ℚ[u]`. -/
theorem conj_alg_of_alg {u μ : ℂ} (hcu : IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) (conj u))
    (h : IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) μ) :
    IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) (conj μ) :=
  IsAlgebraic.adjoin_of_forall_isAlgebraic (fun x hx => by
    obtain ⟨hx1, -⟩ := hx; rw [Set.mem_singleton_iff.1 hx1]; exact hcu) (conj_alg_adjoin h)

/-- `u, μ, ū, μ̄` are all algebraic over `ℚ[u]`, so they generate an algebra of trdeg `≤ 1`. -/
theorem trdeg_le_one {u μ : ℂ} (hu : DiazModulus.IsCandidate u)
    (hμu : IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) μ) :
    Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, μ, conj u, conj μ} : Set ℂ)) ≤ 1 := by
  obtain ⟨hu0, hnorm, -⟩ := hu
  have hρ : IsAlgebraic ℚ (u * conj u) := by rw [rho_eq]; exact hnorm.pow 2
  have hu' := self_alg u
  -- `ū = |u|² / u`
  have hcu : IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) (conj u) :=
    IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hu0) hu' (alg_of_alg hρ)
  have hcμ := conj_alg_of_alg hcu hμu
  refine Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin u _ fun s hs => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h <;> rw [h] <;> assumption

end R2_candidate_log_mul_real_iff_rat_conj

open R2_candidate_log_mul_real_iff_rat_conj in
theorem solution (u : ℂ) (hu : DiazModulus.IsCandidate u) (μ : ℂ) (hμ : μ ≠ 0)
    (heμ : IsAlgebraic ℚ (Complex.exp μ))
    (hμu : IsAlgebraic (↥(Algebra.adjoin ℚ ({u} : Set ℂ))) μ) :
    ((u * μ).im = 0 ↔ ∃ q : ℚ, μ = (q : ℂ) * conj u) ∧ (u * μ).re ≠ 0 := by
  obtain ⟨him, hre⟩ := cand_off_axes hu
  have htr := trdeg_le_one hu hμu
  refine ⟨⟨fun h => ?_, ?_⟩, fun h => ?_⟩
  · -- `u μ` real: the two axis branches are excluded
    rcases DiazModulus.log_mul_real_trichotomy_of_trdeg_one u μ hu.1 hμ hu.2.2 heμ htr h with
      ⟨h1, -⟩ | ⟨h1, -⟩ | hq
    · exact absurd h1 him
    · exact absurd h1 hre
    · exact hq
  · -- `u (q ū) = q |u|²` is real
    rintro ⟨q, rfl⟩
    simp only [Complex.mul_im, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
      Complex.conj_re, Complex.conj_im]
    ring
  · -- `u μ` purely imaginary would put `u` on an axis
    rcases DiazModulus.log_mul_imaginary_mixed_of_trdeg_one u μ hu.1 hμ hu.2.2 heμ htr h with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact him h1
    · exact hre h1

#print axioms solution
