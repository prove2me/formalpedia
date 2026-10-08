-- Prove2me | solution 1 for DiazModulus.candidate_mixed_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-04T18:33:59.991356+00:00
-- url     : https://prove2.me/submissions/533b1018-8563-47c6-bc6a-bb17be463c55

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_two_algebraically_independent_of_exp_column
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin
import Theorems.Thm_Transcendence_isAlgebraic_adjoin_of_not_algebraicIndependent_pair

open Complex ComplexConjugate

namespace R4_candidate_mixed_rigidity

/-- Two algebraically independent elements of `S` force `trdeg ℚ ℚ[S] ≥ 2`. -/
theorem two_le_trdeg {S : Set ℂ} {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (h : AlgebraicIndependent ℚ ![a, b]) : 2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ S) := by
  have hv : AlgebraicIndependent ℚ (![⟨a, Algebra.subset_adjoin ha⟩,
      ⟨b, Algebra.subset_adjoin hb⟩] : Fin 2 → ↥(Algebra.adjoin ℚ S)) :=
    .of_comp (Algebra.adjoin ℚ S).val (by convert h using 1; funext i; fin_cases i <;> rfl)
  simpa using hv.cardinalMk_le_trdeg

end R4_candidate_mixed_rigidity

/- Waldschmidt's theorem of 1973 with `x = (u, μ)` and `y = (ū/μ, 1)`: both pairs are
`ℚ`-independent because `μ ∉ ℚ u ∪ ℚ ū`, and the column `y₂ = 1` gives `e^u`, `e^μ`, algebraic.
So two of `u, μ, ū/μ, 1, e^{uū/μ}, e^u, e^ū, e^μ` are algebraically independent. If
`trdeg ℚ(u, μ, e^{uū/μ}) ≤ 1`, then (`u` being transcendental by Hermite–Lindemann) neither `u, μ`
nor `u, e^{uū/μ}` is an independent pair, so `μ` and `e^{uū/μ}` are algebraic over `ℚ[u]`; and so
are `ū = |u|²/u` and the three algebraic exponentials. All eight numbers then generate an algebra
of transcendence degree at most one, which cannot hold two independent elements. -/
open DiazModulus R4_candidate_mixed_rigidity in
theorem solution (u : ℂ) (hu : IsCandidate u) (μ : ℂ)
    (hμ : IsAlgebraic ℚ (Complex.exp μ))
    (hne : ∀ q : ℚ, μ ≠ (q : ℂ) * u ∧ μ ≠ (q : ℂ) * conj u) :
    2 ≤ Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({u, μ, Complex.exp (u * conj u / μ)} : Set ℂ)) := by
  obtain ⟨hu0, hun, hue⟩ := hu
  have hμ0 : μ ≠ 0 := by simpa using (hne 0).1
  have hcu0 : conj u ≠ 0 := (map_ne_zero _).2 hu0
  -- the two rows `x = (u, μ)` and `y = (ū/μ, 1)` are `ℚ`-independent
  have hx : LinearIndependent ℚ ![u, μ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Rat.smul_def, Rat.smul_def] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [Rat.cast_zero, zero_mul, add_zero, mul_eq_zero, Rat.cast_eq_zero] at hst
      exact ⟨hst.resolve_right hu0, rfl⟩
    · have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      refine absurd ?_ (hne (-s / t)).1
      push_cast; field_simp; linear_combination hst
  have hy : LinearIndependent ℚ ![conj u / μ, 1] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
    have hst' : (s : ℂ) * conj u + (t : ℂ) * μ = 0 := by
      field_simp at hst; linear_combination hst
    by_cases ht : t = 0
    · subst ht
      simp only [Rat.cast_zero, zero_mul, add_zero, mul_eq_zero, Rat.cast_eq_zero] at hst'
      exact ⟨hst'.resolve_right hcu0, rfl⟩
    · have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      refine absurd ?_ (hne (-s / t)).2
      push_cast; field_simp; linear_combination hst'
  obtain ⟨a, ha, b, hb, hab⟩ := two_algebraically_independent_of_exp_column u μ (conj u / μ) 1
    hx hy (by rwa [mul_one]) (by rwa [mul_one])
  by_contra hlt
  -- `u` is transcendental; `μ` and `e^{uū/μ}` are algebraic over `ℚ[u]`
  have hut : Transcendental ℚ u := fun h => hermite_lindemann_holds u hu0 h hue
  have hdep : ∀ w ∈ ({μ, Complex.exp (u * conj u / μ)} : Set ℂ),
      IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) w := fun w hw =>
    Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair hut
      (fun h => hlt (two_le_trdeg (Set.mem_insert u _) (Set.mem_insert_of_mem u hw) h))
  have hext : ∀ z : ℂ, IsAlgebraic ℚ z → IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) z :=
    fun z hz => hz.extendScalars (algebraMap ℚ _).injective
  have huu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) u :=
    isAlgebraic_algebraMap (⟨u, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin ℚ ({u} : Set ℂ))
  have hμu := hdep μ (by simp)
  -- `ū = |u|² / u` is algebraic over `ℚ[u]`, hence so is `ū / μ`
  have hcuu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) (conj u) := by
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hu0) huu (hext _ ?_)
    have h : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [h]; exact hun.pow 2
  have hecu : IsAlgebraic ℚ (Complex.exp (conj u)) := by
    rw [Complex.exp_conj]
    exact hue.algHom ((Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ)
  have h8 := Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin (K := ℚ) u
    ({u, μ, conj u / μ, 1, Complex.exp (u * (conj u / μ)), Complex.exp (u * 1),
      Complex.exp (μ * (conj u / μ)), Complex.exp (μ * 1)} : Set ℂ) (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huu
    · exact hμu
    · exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hμ0) hμu
        (by rwa [mul_div_cancel₀ _ hμ0])
    · exact isAlgebraic_one
    · rw [← mul_div_assoc]; exact hdep _ (by simp)
    · rw [mul_one]; exact hext _ hue
    · rw [mul_div_cancel₀ _ hμ0]; exact hext _ hecu
    · rw [mul_one]; exact hext _ hμ)
  have := (two_le_trdeg ha hb hab).trans h8
  norm_num at this

#print axioms solution
