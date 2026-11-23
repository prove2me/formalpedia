-- Prove2me | solution 1 for Formalism.DivisionValues.localizationAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:24.198212+00:00
-- url     : https://prove2.me/submissions/8d41ec86-c7cb-4148-917d-5fe8d45ca74d

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
import Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP


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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0)
    (N : Submodule (𝓞 K) (Fin d → K)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) = smulLat a (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N) := by
  ext x
  rw [imageLcv_mem_locP, shift_mem_smulLat]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [shift_mem_smulLat] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨a⁻¹ • x, ?_, by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]⟩
    rw [imageLcv_mem_locP]
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, ← hyx, smul_smul, inv_mul_cancel₀ ha, one_smul]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    rw [imageLcv_mem_locP] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨s, hs, ?_⟩
    rw [shift_mem_smulLat]
    exact ⟨s • y, hsy, smul_comm a s y⟩
end Formalism.DivisionValues
