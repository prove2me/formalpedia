-- Prove2me | solution 1 for Formalism.DivisionValues.shift_smul_mem_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.103478+00:00
-- url     : https://prove2.me/submissions/ff63b21a-2032-440c-9c2d-95cdcaf85e25

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_mem_smulLat
import Theorems.Thm_Formalism_DivisionValues_shift_int_of_nonneg
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP
import Theorems.Thm_Formalism_DivisionValues_valuation_basic_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    {a b : K} (ha : a ≠ 0) (hab : b = 0 ∨ vw w a ≤ vw w b) {x : Fin d → K} (hx : x ∈ N) :
    b • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by
  rcases hab with rfl | hab
  · rw [zero_smul]
    exact Submodule.zero_mem _
  · by_cases hb : b = 0
    · subst hb
      rw [zero_smul]
      exact Submodule.zero_mem _
    · have hv : 0 ≤ vw w (b / a) := by
        rw [div_eq_mul_inv, (valuation_basic_properties K w).1 b a⁻¹ hb (inv_ne_zero ha),
          (valuation_basic_properties K w).2.2.2.2.2.1]
        linarith
      obtain ⟨t, y, ht, hty⟩ := shift_int_of_nonneg w (b / a) (div_ne_zero hb ha) hv
      have key : a * (y : K) = (t : K) * b := by
        rw [← hty]
        field_simp
      rw [imageLcv_mem_locP]
      refine ⟨t, ht, ?_⟩
      rw [shift_mem_smulLat]
      refine ⟨y • x, N.smul_mem y hx, ?_⟩
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      have hc : ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = (c : K) := fun c => rfl
      rw [hc, hc]
      linear_combination (x i) * key
end Formalism.DivisionValues
