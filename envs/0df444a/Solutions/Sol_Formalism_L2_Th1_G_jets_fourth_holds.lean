-- Prove2me | solution 1 for Formalism.L2.Th1.G.jets_fourth_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:25.035773+00:00
-- url     : https://prove2.me/submissions/ed59b014-248c-4b92-9442-049d1e3afe5e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_mfact_rep
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_coeff_prod_inBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
namespace Formalism.L2.Th1.G
theorem _root_.solution : JetsFourth := by
  intro K _ R ι _ f h4 hf κ
  apply h4
  have h := hf (HurwitzJetIntegrality.rep (Fin 4) fun _ => κ)
  unfold tens4 at h
  rw [HurwitzJetIntegrality.coeff_prod_inBlock, HurwitzJetIntegrality.mfact_rep] at h
  simpa [mul_pow] using h
end Formalism.L2.Th1.G
