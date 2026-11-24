-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.p1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:33:25.910331+00:00
-- url     : https://prove2.me/submissions/bcb9fe2a-521d-4081-8193-2890f11cc15e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_normW_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_p1aBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_plane_wave_word_identity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas
theorem _root_.solution : PlaneWaveNormBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ f fi s nn w x hW hWQ hnd hP hnn
  have hV := (Formalism.FourierDecayAlt.P.plane_wave_word_identity ℂ A S QQ f fi s w hW hWQ hnd).2.2.1
  have hb := p1aBound A S V ρ (RRw QQ w) (Vw f s w) x hP hV
  unfold N0
  exact div_le_div_of_nonneg_right hb (normW_pos nn w hnn).le
end Formalism.FourierDecayAlt.P.DualKernelLemmas
