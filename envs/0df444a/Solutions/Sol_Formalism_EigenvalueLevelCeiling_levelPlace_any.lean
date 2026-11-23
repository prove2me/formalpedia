-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.levelPlace_any
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:53.349804+00:00
-- url     : https://prove2.me/submissions/5205ed3c-0be0-4376-8611-2f0a81784975

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_scalar_level
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
private theorem ramw_nonneg_lemma_2 (K : Type) [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ ramw w := by
  unfold ramw vw
  have e : ((plc w : ℕ) : K) = algebraMap (𝓞 K) K ((plc w : ℕ) : 𝓞 K) := by simp
  rw [e, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg
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
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (E : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0) (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0)
    (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (hE : E ≤ ramw w * ((T : ℤ) + 1)) :
    E - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤ ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by
  rw [scalar_level K w nnL nnF q Z1 Z2 T c h1 h2 h3 h4 h5 z1 z2]
  have hR := ramw_nonneg_lemma_2 K w
  have hA : 0 ≤ ramw w * ((T : ℤ) - 1) := mul_nonneg hR (by omega)
  have hB : 0 ≤ (c : ℤ) * vw w q := mul_nonneg (by omega) hq
  linarith
end Formalism.EigenvalueLevelCeiling
