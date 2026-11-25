-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.assembleOneStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:21.350517+00:00
-- url     : https://prove2.me/submissions/dfae77b4-29f9-48a4-83fe-4f95f63c0578

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lintegral_nu
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_conc
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution : AssembleOneStep := by
  intro HU HIv hG HA HI OM OC CI CF SD SH k r' μG μG₁ hμG h₁
  obtain ⟨hP, hμP⟩ := SH k r' μG₁ h₁
  have := sigmaFinite_of_haar h₁
  obtain ⟨c, hc⟩ := HU k (1 + r') (GV k (1 + r')) μG (nu μG₁) (hG _ _) hμG (nu_conc HIv hG HI OM μG₁ h₁ hP hμP)
    (fun a ha => nu_left HIv hG HA HI OM OC CI SD μG₁ h₁ hP hμP a ha)
    (fun K hK => nu_fin HIv hG HA HI OM CF μG₁ h₁ hP hμP K hK)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact nu_ne μG₁ h₁.ne_zero hc
  refine ⟨c⁻¹, inv_pos.2 (pos_iff_ne_zero.2 hc0), fun f hf => ?_⟩
  have h2 : II μG₁ f = (c : ℝ≥0∞) * ∫⁻ g, f g ∂μG := by
    rw [← lintegral_nu μG₁ f hf, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  show _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * II μG₁ f
  rw [h2, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0, ENNReal.coe_one, one_mul]
end Formalism.FourierDecayAlt.P.B2x9
