-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAWeyl7_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.831999+00:00
-- url     : https://prove2.me/submissions/5ae33777-a8cf-4447-be02-babe89665585

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementF
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coefficient_bound_membership
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_pos
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_slope_bound_saturation


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
theorem _root_.solution (hG : ThmAGauss7) : ThmAWeyl7 := by
  intro l _ d N0 N1 _ hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size h1 h2 h3 hJ c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  refine slope_bound_saturation ℂ_[l] d N0 colN p hp _
    (Submodule.smul_mem _ _ (coefficient_bound_membership ℂ_[l] d N0 N1 colN p hp I _)) fun n => ?_
  rw [MvPolynomial.coeff_smul, norm_smul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]
  exact (hG l d N0 N1 hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size h1 h2 h3 hJ n).trans hc
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
