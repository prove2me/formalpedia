-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.integrable_of_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:27.268804+00:00
-- url     : https://prove2.me/submissions/c12bb021-5d1e-4d4d-a1d1-c62a34a4bf21

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Theorems.Thm_Formalism_landauIteratedDerivatives_meas_rpow

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
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x) {cr t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => Real.log x ^ n * (H x * x ^ (-cr - 1))) (Ioi 1))
    (hsum : Summable (fun n : ℕ =>
      ∫ x in Ioi (1:ℝ), t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1))))) :
    Good H (cr - t) := by
  set f : ℕ → ℝ → ℝ := fun n x => t ^ n / n.factorial * (Real.log x ^ n * (H x * x ^ (-cr - 1)))
    with hf
  have hfi : ∀ n, Integrable (f n) (volume.restrict (Ioi 1)) := fun n => (hint n).const_mul _
  have hf0 : ∀ n, ∀ x ∈ Ioi (1:ℝ), 0 ≤ f n x := by
    intro n x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have := hpos x hx
    have := Real.log_nonneg hx1
    have := Real.rpow_nonneg hx0 (-cr - 1)
    simp only [hf]
    positivity
  have hsumx : ∀ x ∈ Ioi (1:ℝ), HasSum (fun n => f n x) (H x * x ^ (-(cr - t) - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have he := NormedSpace.expSeries_div_hasSum_exp (t * Real.log x)
    rw [← Real.exp_eq_exp_ℝ] at he
    have := he.mul_left (H x * x ^ (-cr - 1))
    have e1 : (fun n => f n x) =
        fun i => H x * x ^ (-cr - 1) * ((t * Real.log x) ^ i / i.factorial) := by
      funext n
      simp only [hf]
      rw [mul_pow]
      ring
    have e2 : H x * x ^ (-(cr - t) - 1) = H x * x ^ (-cr - 1) * Real.exp (t * Real.log x) := by
      rw [show Real.exp (t * Real.log x) = x ^ t by rw [Real.rpow_def_of_pos hx0]; ring_nf,
        mul_assoc, ← Real.rpow_add hx0]
      ring_nf
    rw [e1, e2]
    exact this
  unfold Good IntegrableOn
  rw [← lintegral_ofReal_ne_top_iff_integrable (meas_rpow H hH _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      (hsumx x hx).nonneg (fun n => hf0 n x hx)))]
  have h1 : ∫⁻ x in Ioi (1:ℝ), ENNReal.ofReal (H x * x ^ (-(cr - t) - 1)) =
      ∫⁻ x in Ioi (1:ℝ), ∑' n, ENNReal.ofReal (f n x) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [← (hsumx x hx).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun n => hf0 n x hx) (hsumx x hx).summable]
  rw [h1, lintegral_tsum (fun n => (hfi n).aemeasurable.ennreal_ofReal)]
  have h2 : ∀ n, ∫⁻ x in Ioi (1:ℝ), ENNReal.ofReal (f n x) =
      ENNReal.ofReal (∫ x in Ioi (1:ℝ), f n x) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hfi n)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hf0 n)))).symm
  rw [tsum_congr h2, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => setIntegral_nonneg measurableSet_Ioi (hf0 n)) hsum]
  exact ENNReal.ofReal_ne_top
end Formalism.landauIteratedDerivatives
