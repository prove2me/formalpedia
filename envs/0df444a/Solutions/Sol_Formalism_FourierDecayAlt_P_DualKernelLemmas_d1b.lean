-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.d1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:55.869367+00:00
-- url     : https://prove2.me/submissions/cd7fe474-abd5-412a-8149-aceda928fd70

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_pair_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_star_ofReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_duality_plus
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
theorem _root_.solution : DualityIsometry := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD X₂ X₂'
  obtain ⟨hM, hFR, hFT, hY, hY1, hq⟩ := hD
  have hd := Formalism.FourierDecayAlt.P.duality_plus ℂ A S Ω RR TT q a (Y : ℂ) hM hFR hFT hY hY1
    (star_ofReal Y) hq
  simp only [frm]
  rw [pair_act', ← act_mul, ← act_mul, hd.2.2.2.2.1, act_csmul, pair_smul_left]
end Formalism.FourierDecayAlt.P.DualKernelLemmas
