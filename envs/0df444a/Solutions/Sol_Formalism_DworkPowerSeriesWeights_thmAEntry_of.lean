-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAEntry_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:24.587555+00:00
-- url     : https://prove2.me/submissions/6d46ffc8-934f-4f1c-adbf-1f36ee84d008

import Definitions.Def_Formalism_GaussJetBounds_StatementV
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_pos
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_le_rpow_of_forall_norm

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hW : ThmAWeyl) : ThmAEntry := by
  intro l _ d N0 N1 _ hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size
    hnu1 hnu2 hsize a ha hsa hN0 hsat δ hδ
  refine le_rpow_of_forall_norm l _ _ (norm_nonneg _) fun c hc => ?_
  have hmem := hW l d N0 N1 hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2
    size hnu1 hnu2 hsize a ha hsa hN0 hsat c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  have h1 := hδ _ hmem
  rw [map_smul, norm_smul, norm_inv] at h1
  rwa [inv_mul_le_iff₀ hcpos, mul_one] at h1
end Formalism.DworkPowerSeriesWeights
