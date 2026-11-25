-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.kernel_bounds_generic_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:16.57412+00:00
-- url     : https://prove2.me/submissions/8f450b91-9f3a-4702-a936-6478f3292c43

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_scale_scale
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_norm_lift_le_one


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
theorem _root_.solution (hS : ThmSUniform) (h1 : KernelValuationBoundUltrametric) (h2 : KernelBoundArbitrarySizes) (h3 : KernelBK) :
    KernelBoundsGeneric := by
  intro p _ K0 _ _ _ _ σ hU hζ F hF be hbe K _ _ _ j ν r0 r1 _ hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0
    hΦ0 hΦ TT colN hts hp I n
  obtain ⟨c, hc, -, -, hcl⟩ := hS K0 p σ hU hζ F hF be hbe
  have hin := hcl K j ν r0 r1 hj om oms ϖ μ U0 Φ hϖ hom hμ0 hμ hU0 hΦ0 hΦ
  have hp2 : 2 < p := hU.2.1
  have hn : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [← map_natCast j, hj, hU.2.2.1]
  have hpC : (p : K) ≠ 0 := by exact_mod_cast hU.1.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply hpC
    rw [← hϖ, zero_pow]
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2.le 2
    omega
  have hu : ∀ s : ZMod (2 * ν), ‖uS (j c) (j (σ c)) s‖ ≤ 1 := by
    intro s
    unfold uS
    split_ifs
    · rw [norm_neg, hj]
      exact norm_lift_le_one hU hc
    · rw [hj]
      exact hc
  have hin' : InClass (p : K) (hhS p (uS (j c) (j (σ c)))) (MvPowerSeries.subst
      (fun x => MvPowerSeries.C ϖ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K))
      (thetaLog om oms ϖ μ (mvExp (-Φ) * U0))) := by
    unfold thetaLog
    rw [scale_scale hϖ0]
    exact hin
  exact ⟨h1 K p ν r0 r1 _ ϖ _ TT colN hts hp I hp2 hn hϖ hu hin' n,
    h2 K p ν r0 r1 _ ϖ _ TT colN hts hp I hp2 hn hϖ hu hin' n,
    fun i hi => h3 K p ν r0 r1 i _ ϖ _ TT colN hts hp I hp2 hn hi hϖ hu hin' n⟩
end Formalism.InvariantFactorPaths.G7
