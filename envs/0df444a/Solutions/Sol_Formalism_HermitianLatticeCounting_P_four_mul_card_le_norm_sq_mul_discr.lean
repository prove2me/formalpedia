-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.four_mul_card_le_norm_sq_mul_discr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:11.713011+00:00
-- url     : https://prove2.me/submissions/ca370781-4341-4617-a3de-c5b5244ed498

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_abs_norm_mul_abs_discr
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bLat_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_inner_placeEmbedding_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hc : ∀ w : InfinitePlace E, w.IsComplex) (y : s5bV E) (hy : y ≠ 0)
    (hint : ∀ x ∈ integerEmbeddingLattice hc, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) :
    4 * (Fintype.card (InfinitePlace E) : ℝ) ≤
      ‖y‖ ^ 2 * |(discr E : ℝ)| ^ (1 / (Fintype.card (InfinitePlace E) : ℝ)) := by
  classical
  have hL : ∀ x ∈ integerEmbeddingLattice hc, ∃ n : ℤ, inner ℝ x y = (n : ℝ) := by assumption
  have hr0 : (0 : ℝ) < Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
  have hmem : ∀ a : 𝓞 E, complexEmbeddingVector (a : E) ∈ integerEmbeddingLattice hc := fun a => (s5bLat_mem hc _).mpr ⟨a, rfl⟩
  have hn0 : ∀ i, ∃ n : ℤ, inner ℝ (complexEmbeddingVector (integralBasis E i)) y = (n : ℝ) := by
    intro i
    have hi : integralBasis E i = ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
      first
      | (rw [NumberField.integralBasis_apply]; rfl)
      | exact NumberField.integralBasis_apply E i
      | simp [NumberField.integralBasis_apply]
    rw [hi]
    exact hL _ (hmem _)
  choose n hn using hn0
  obtain ⟨z, hzB⟩ : ∃ z : E, ∀ j, Algebra.trace ℚ E (z * integralBasis E j) = (n j : ℚ) := by
    have hnd : (Algebra.traceForm ℚ E).Nondegenerate := by
      first
      | exact traceForm_nondegenerate ℚ E
      | exact Algebra.traceForm_nondegenerate ℚ E
      | exact traceForm_nondegenerate _ _
    refine ⟨∑ i, (n i : ℚ) • LinearMap.BilinForm.dualBasis (Algebra.traceForm ℚ E) hnd
      (integralBasis E) i, fun j => ?_⟩
    have h : ∀ i, Algebra.trace ℚ E (LinearMap.BilinForm.dualBasis (Algebra.traceForm ℚ E) hnd
        (integralBasis E) i * integralBasis E j) = if j = i then 1 else 0 := by
      intro i
      rw [← Algebra.traceForm_apply]
      first
      | rw [LinearMap.BilinForm.apply_dualBasis_left]
      | exact LinearMap.BilinForm.apply_dualBasis_left _ _ _ _ _
    rw [Finset.sum_mul, map_sum]
    have h' : ∀ i, Algebra.trace ℚ E ((n i : ℚ) • LinearMap.BilinForm.dualBasis (Algebra.traceForm ℚ E) hnd
        (integralBasis E) i * integralBasis E j) = if j = i then (n i : ℚ) else 0 := by
      intro i
      rw [smul_mul_assoc, map_smul, h i, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => h' i]
    simp
  obtain ⟨yz, hyzdef⟩ : ∃ yz : s5bV E,
      yz = (WithLp.toLp 2 (fun w : InfinitePlace E => 2 * conj (w.embedding z)) : s5bV E) :=
    ⟨_, rfl⟩
  have hsig : ∀ t : E, (complexSpaceMixedLinearEquiv hc).symm (mixedEmbedding E t) = complexEmbeddingVector t := by
    intro t
    ext w
    rfl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : mixedEmbedding.mixedSpace E →ₗ[ℝ] ℝ,
      ∀ v, ψ v = inner ℝ ((complexSpaceMixedLinearEquiv hc).symm v) (y - yz) :=
    ⟨{ toFun := fun v => inner ℝ ((complexSpaceMixedLinearEquiv hc).symm v) (y - yz)
       map_add' := fun a b => by simp [inner_add_left]
       map_smul' := fun c a => by simp [real_inner_smul_left] }, fun v => rfl⟩
  have hψ0 : ψ = 0 := by
    refine (mixedEmbedding.latticeBasis E).ext fun i => ?_
    rw [hψ, LinearMap.zero_apply, mixedEmbedding.latticeBasis_apply, hsig, inner_sub_right, hn,
      hyzdef, inner_placeEmbedding_eq_trace hc, hzB]
    simp
  have hyz : y = yz := by
    have h0 := hψ ((complexSpaceMixedLinearEquiv hc) (y - yz))
    rw [hψ0, LinearMap.zero_apply, LinearEquiv.symm_apply_apply] at h0
    first
    | exact sub_eq_zero.mp (inner_self_eq_zero.mp h0.symm)
    | exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp h0.symm)
    | (have h1 : ‖y - yz‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact h0.symm
       exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)))
  have hcod : ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * (a : E)) = m := by
    intro a
    obtain ⟨m, hm⟩ := hL _ (hmem a)
    refine ⟨m, ?_⟩
    rw [hyz, hyzdef, inner_placeEmbedding_eq_trace hc] at hm
    exact_mod_cast hm
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hy
    rw [hyz, hyzdef]
    ext w
    simp
  have cod := one_le_abs_norm_mul_abs_discr z hz0 hcod
  have cod' : (1 : ℝ) ≤ |((Algebra.norm ℚ z : ℚ) : ℝ)| * |(discr E : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr cod
    push_cast at h
    exact h
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := by
    intro w
    first
    | exact NumberField.InfinitePlace.mult_isComplex ⟨w, hc w⟩
    | simp [NumberField.InfinitePlace.mult, NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hc w)]
  have hprod : |((Algebra.norm ℚ z : ℚ) : ℝ)| = ∏ w : InfinitePlace E, ‖w.embedding z‖ ^ 2 := by
    have h := NumberField.InfinitePlace.prod_eq_abs_norm z
    have h2 : ∏ w : InfinitePlace E, w z ^ w.mult = ∏ w : InfinitePlace E, ‖w.embedding z‖ ^ 2 :=
      Finset.prod_congr rfl fun w _ => by rw [hm w, NumberField.InfinitePlace.norm_embedding_eq]
    rw [h2] at h
    first
    | (push_cast at h ⊢; linarith)
    | exact_mod_cast h.symm
    | simp [h]
  have hnorm : ‖y‖ ^ 2 = 4 * ∑ w : InfinitePlace E, ‖w.embedding z‖ ^ 2 := by
    rw [hyz, hyzdef, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [norm_mul, mul_pow] <;> norm_num
  have hamgm : (∏ w : InfinitePlace E, ‖w.embedding z‖ ^ 2) ^ (1 / (Fintype.card (InfinitePlace E) : ℝ)) ≤
      (∑ w : InfinitePlace E, ‖w.embedding z‖ ^ 2) / (Fintype.card (InfinitePlace E) : ℝ) := by
    have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : InfinitePlace E => (1 : ℝ))
      (fun w => ‖w.embedding z‖ ^ 2) (fun _ _ => zero_le_one) (by simpa using hr0)
      (fun _ _ => sq_nonneg _)
    simpa [one_div] using h
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ w : InfinitePlace E, ‖w.embedding z‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∏ w : InfinitePlace E, ‖w.embedding z‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Fintype.card (InfinitePlace E) : ℝ) := ⟨_, rfl⟩
  rw [← hS] at hnorm hamgm
  rw [← hP] at hamgm hprod
  rw [← hr] at hamgm hr0 ⊢
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hD0 : 0 ≤ |(discr E : ℝ)| := abs_nonneg _
  have hDr : 0 ≤ |(discr E : ℝ)| ^ (1 / r) := Real.rpow_nonneg hD0 _
  have h1 : 1 ≤ P ^ (1 / r) * |(discr E : ℝ)| ^ (1 / r) := by
    rw [← Real.mul_rpow hP0 hD0, ← hprod]
    exact Real.one_le_rpow cod' (div_nonneg zero_le_one hr0.le)
  have h2 : 1 ≤ S / r * |(discr E : ℝ)| ^ (1 / r) :=
    h1.trans (mul_le_mul_of_nonneg_right hamgm hDr)
  have hr' : r ≠ 0 := hr0.ne'
  calc 4 * r = 4 * (r * 1) := by ring
    _ ≤ 4 * (r * (S / r * |(discr E : ℝ)| ^ (1 / r))) := by gcongr
    _ = ‖y‖ ^ 2 * |(discr E : ℝ)| ^ (1 / r) := by
        rw [hnorm]
        first
        | (field_simp; ring)
        | field_simp
        | (rw [← mul_assoc r, mul_div_cancel₀ _ hr']; ring)
end Formalism.HermitianLatticeCounting.P
