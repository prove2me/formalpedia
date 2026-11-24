-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GaussB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:57.163908+00:00
-- url     : https://prove2.me/submissions/4a75b40a-af98-47e2-9e04-48502d01ad3b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_norm_p_complex
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_reduce

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open EGauss
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hE : EntryB) : GaussB := by
  intro p _ ν r0 r1 i _ u F TT colN hts hp I hp2 hi hu hF n
  obtain ⟨K, instK, hult, C, u', F', ξ, e, l, sf, T, I', hyp, hco, hal, hcap, hls, hB⟩ :=
    reduce p ν r0 r1 u F TT colN hts hp I hp2 hu hF
  have h := hE K p ν r0 r1 C u' F' TT ξ e l sf T I' (univ.filter (fun b : Fin r1 => b.val < i)) hyp
  rw [hal, hcap, hls] at h
  refine le_trans ?_ h
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := hyp.2.2.1
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hnp, norm_p_complex]
  exact mul_le_mul (pow_le_pow_of_le_one hp0.le hp1 (hB _ i hi)) (hco n) (norm_nonneg _)
    (pow_nonneg hp0.le _)
end Formalism.InvariantFactorPaths.G7
