-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.dkStep1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:27.742407+00:00
-- url     : https://prove2.me/submissions/197b59d4-bc67-435a-bfa5-1847c143a9d1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_dkDualOK
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_duality_list_holds
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act__bf313f925fd6


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
theorem _root_.solution : DKStep1 := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L hS hD X₁ X₂
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 (dkDualOK S q w L hD)
  simp only [frm]
  rw [pair_act', ← act_mul, hdl.2.2.1]
end Formalism.FourierDecayAlt.P.DualKernelLemmas
