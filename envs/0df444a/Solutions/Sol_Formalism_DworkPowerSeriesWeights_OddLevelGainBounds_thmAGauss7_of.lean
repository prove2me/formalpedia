-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGauss7_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:14:48.044017+00:00
-- url     : https://prove2.me/submissions/0a8f850f-5da0-4acb-9925-9782d7d6cf7c

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementF
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_TwoFormsOfTheoremA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_gauss7_labels
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_admissibleTransfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_cc_be
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frame_jet_evaluation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gauss_sum_powers
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_lt_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_residuallyGenericExists
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (hA0 : ThmAGeneric7.{0}) : ThmAGauss7 := by
  intro l _ d N0 N1 _ hl3 hd hde hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize hJ n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (ZMod d × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one l
  obtain ⟨lab, m, hinj, hlab, hm⟩ := gauss7_labels l d hlp.two_le TT nu1 size
  obtain ⟨hT1, hT2, hT3, hT4⟩ := admissibleTransfer ℂ_[l] K φ hφ l d N0 N1 K0 ζ be
  obtain ⟨hg0', hg'⟩ := hT3 g hg0 hg
  have hA := hA0 K l d N0 N1 hlp hl3 hd hde (hnl ▸ hl1) hN0 (K0.map φ) (hT1 hK0)
    (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) _ hg0' hg' _ (hT4 U hU) (φ ε)
    (by rcases hε with rfl | rfl <;> simp) TT colN p hp hp1 I Y hgen nu1 nu2 size hnu1 hnu2 hsize
    (JnumOneLetter l d TT nu1 size) lab hinj hlab hJ m hm
  rw [← frame_jet_evaluation ℂ_[l] K φ d N0 N1 g U ε be hg0 (asmS_cc_be hbe.2.2.1) colN p hp I
    (genFrame TT l m Y), hnl] at hA
  refine le_trans ?_ hA
  have hk : genFrame TT l m Y =
      fun y => Y y ^ (if y.1 ∈ TT ∧ y.2.1.val = 0 then l ^ m else 1) := by
    funext y
    unfold genFrame
    split_ifs <;> simp
  rw [hk]
  refine gauss_sum_powers ℂ_[l] K φ _ Y hgauss _ (fun y => ?_) _ n
  split_ifs
  · exact pow_ne_zero _ hlp.ne_zero
  · exact one_ne_zero
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
