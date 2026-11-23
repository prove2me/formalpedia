-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.congW_of_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:28.520799+00:00
-- url     : https://prove2.me/submissions/d93c0160-c2c0-45d3-8b85-83bc38b31642

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_zpow_sum_of_ne

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {d : ℕ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {l : ℕ} [NeZero d] {ζ : K} (hN : l ^ d - 1 ≠ 0)
    (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) {be : MvPowerSeries (ZMod d) K}
    (hbe : MvPowerSeries.subst (torus l ζ) be = be) :
    CongW ((l ^ d - 1 : ℕ) : ℤ) (lw l) be := by
  classical
  intro n hn
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have ht : torus (d := d) l ζ = (fun s : ZMod d => ζ ^ lw l s) • (MvPowerSeries.X : ZMod d → MvPowerSeries (ZMod d) K) := by
    funext s
    simp [torus, MvPowerSeries.smul_eq_C_mul]
  rw [ht, ← MvPowerSeries.rescale_eq_subst] at hbe
  have hc := congrArg (MvPowerSeries.coeff n) hbe
  rw [MvPowerSeries.coeff_rescale] at hc
  have hprod : (n.prod fun s m => (ζ ^ lw l s) ^ m) = ζ ^ wsum (lw l) n := by
    unfold wsum Finsupp.prod Finsupp.sum
    rw [zpow_sum_of_ne _ hζ0]
    refine Finset.prod_congr rfl fun s _ => ?_
    beta_reduce
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hprod] at hc
  have hu : ζ ^ wsum (lw l) n = 1 := by
    have h2 : (ζ ^ wsum (lw l) n - 1) * MvPowerSeries.coeff n be = 0 := by
      rw [sub_mul, hc, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hn
  exact (hζ.zpow_eq_one_iff_dvd _).mp hu
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
