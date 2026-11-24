-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.good_logpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:25.9278+00:00
-- url     : https://prove2.me/submissions/71a569a0-6a62-4f83-aa7c-a34a7036cced

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Theorems.Thm_Formalism_landauIteratedDerivatives_meas_rpow
import Theorems.Thm_Formalism_landauIteratedDerivatives_logpow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives
namespace Formalism.landauIteratedDerivatives
theorem _root_.solution {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {τ σ : ℝ} (hτ : Good H τ) (hlt : τ < σ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-σ - 1))) (Ioi 1) := by
  set K : ℝ := (((n : ℝ) + 1) / (σ - τ)) ^ n
  have hK : 0 ≤ K := by
    have : 0 < σ - τ := by linarith
    positivity
  refine Integrable.mono' (hτ.norm.const_mul K) ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ => Real.log x ^ n).aestronglyMeasurable.mul
      (meas_rpow H hH σ)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hb := logpow_le n (sub_pos.2 hlt) hx1
  rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg hlog0 n),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hsplit : x ^ (-τ - 1) = x ^ (σ - τ) * x ^ (-σ - 1) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [hsplit]
  calc Real.log x ^ n * (‖H x‖ * x ^ (-σ - 1))
      ≤ (K * x ^ (σ - τ)) * (‖H x‖ * x ^ (-σ - 1)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = K * (‖H x‖ * (x ^ (σ - τ) * x ^ (-σ - 1))) := by ring
end Formalism.landauIteratedDerivatives
