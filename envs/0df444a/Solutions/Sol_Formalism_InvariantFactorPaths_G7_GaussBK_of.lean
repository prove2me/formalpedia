-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GaussBK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:35:15.372396+00:00
-- url     : https://prove2.me/submissions/165561ae-ec67-4041-ba5c-3ead83b5fc25

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGaussK_reduce
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open EGaussK DeterminantJetScaling ScaledSeriesSubstitution
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hE : EntryB) : GaussBK := by
  intro K _ _ _ p _ ν r0 r1 i _ u F TT colN hts hp I hp2 hn hi hu hF n
  obtain ⟨K', iK, hU, C, u', F', ξ, e, l, sf, T, I', hH, hb, hal, hcap, hls, hJ⟩ :=
    EGaussK.reduce K p ν r0 r1 u F TT colN hts hp I hp2 hn hu hF
  have h1 := hE K' p ν r0 r1 C u' F' TT ξ e l sf T I'
    (univ.filter (fun b : Fin r1 => b.val < i)) hH
  rw [hal, hcap, hls] at h1
  have h2 := hJ (univ.filter (fun b : Fin r1 => b.val < i)) i hi
  have hn' : ‖(p : K')‖ = (p : ℝ)⁻¹ := hH.2.2.1
  rw [norm_mul, norm_pow, hn'] at h1
  rw [norm_mul, norm_pow, hn]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hinv : (p : ℝ)⁻¹ ≤ 1 := by
    first
      | exact inv_le_one_of_one_le₀ hp1
      | exact inv_le_one hp1
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  refine le_trans ?_ h1
  exact mul_le_mul (pow_le_pow_of_le_one hinv0 hinv h2) (hb n) (norm_nonneg _) (by positivity)
end Formalism.InvariantFactorPaths.G7
