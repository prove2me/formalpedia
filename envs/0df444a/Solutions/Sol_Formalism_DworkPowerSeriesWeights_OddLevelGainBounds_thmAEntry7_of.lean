-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAEntry7_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:05.550167+00:00
-- url     : https://prove2.me/submissions/cf04763b-8b66-4053-973d-cb3f582a219e

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementF
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_le_rpow_of_forall_norm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_pos


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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (hW : ThmAWeyl7) : ThmAEntry7 := by
  intro l _ d N0 N1 _ hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize hJ δ hδ
  refine le_rpow_of_forall_norm l _ _ (norm_nonneg _) fun c hc => ?_
  have hmem := hW l d N0 N1 hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize hJ c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  have h1 := hδ _ hmem
  rw [map_smul, norm_smul, norm_inv] at h1
  rwa [inv_mul_le_iff₀ hcpos, mul_one] at h1
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
