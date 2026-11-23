-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.scalar_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:03.809418+00:00
-- url     : https://prove2.me/submissions/0106440d-1b40-4282-a150-f2cb32b29bc8

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_valuation_pow_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
private theorem vw_mul_lemma (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply FractionalIdeal.count_mul <;> rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
example : ⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (15 - 1) + 1))⌉ = (1 : ℤ) * (((3 : ℕ) : ℤ) + 1) := by
  rw [Int.ceil_eq_iff]; constructor <;> norm_num
example : ¬ (⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (2 - 1) + 1))⌉ ≤ (1 : ℤ) * (((3 : ℕ) : ℤ) + 1)) := by
  rw [Int.ceil_le]; norm_num
example : (1 : ℝ) * 1 * (1 * 1 ^ 3) / (4 * 1) + 2 * (1 * 1 ^ 3) * 1 ^ 2 / 1 ≤ 1 * 3 * 1 ^ 2 / 1 :=
  constant_b_bound 1 3 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
example (Mt : Submodule ℤ (ℤ × ℤ)) :
    ((Mt.map (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ)).map
      ((LinearMap.inl ℤ ℤ ℤ) ∘ₗ (LinearMap.fst ℤ ℤ ℤ))).map (LinearMap.fst ℤ ℤ ℤ) =
      (Mt.map (LinearMap.fst ℤ ℤ ℤ)).map (LinearMap.id : ℤ →ₗ[ℤ] ℤ) :=
  theta_identity ℤ (ℤ × ℤ) ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id _ LinearMap.id rfl
    (by intro x _; simp [LinearMap.mem_ker]) Mt
example : (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) ∘ₗ (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) =
    (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) ∘ₗ (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) :=
  (theta_identity_orthogonal ℤ (ℤ × ℤ) ℤ ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id
    (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) LinearMap.id (fun x y => x.1 * y.1 + x.2 * y.2) rfl
    (fun _ _ => rfl) (by ext <;> simp)
    (by ext x; simp [LinearMap.mem_ker])
    (by
      intro x
      constructor
      · rintro ⟨y, rfl⟩ k hk
        have : k.1 = 0 := by simpa [LinearMap.mem_ker] using hk
        simp [this]
      · intro hx
        have := hx (0, 1) (by simp [LinearMap.mem_ker])
        refine ⟨x, ?_⟩
        ext <;> simp at this ⊢
        exact this.symm)).1
example : ((8 : ℝ) + 0 + 2) * (8 + 0 + 2 + 2 * 2) ≤ 3.75 * 8 ^ 2 :=
  (gapConditions_of_largeGaps 8 0 2 2 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
example : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ < 2 * ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ := by
  have a : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 3 := by rw [Int.ceil_eq_iff]; norm_num
  have b : ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 2 := by rw [Int.ceil_eq_iff]; norm_num
  rw [a, b]; norm_num
section Instance
variable (K : Type) [Field K] [NumberField K] [StarRing K]
end Instance
end Formalism.EigenvalueLevelCeiling
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : ScalarLevel := by
  intro K _ _ _ w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2
  rw [vw_mul_lemma K w _ _ (pow_ne_zero _ (mul_ne_zero h1 h4)) (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h3)) h5),
    valuation_pow_alt K w _ (mul_ne_zero h1 h4), vw_mul_lemma K w _ _ h1 h4,
    vw_mul_lemma K w _ _ (mul_ne_zero h2 (pow_ne_zero _ h3)) h5, vw_mul_lemma K w _ _ h2 (pow_ne_zero _ h3),
    valuation_pow_alt K w _ h3, vw_mul_lemma K w _ _ (pow_ne_zero _ h1) h2, valuation_pow_alt K w _ h1, z1, z2]
  ring
end Formalism.EigenvalueLevelCeiling
