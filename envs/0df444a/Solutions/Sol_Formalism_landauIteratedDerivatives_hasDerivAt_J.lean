-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.hasDerivAt_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:07.481263+00:00
-- url     : https://prove2.me/submissions/9592a442-9a1f-4139-9edd-081e7213132c

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Theorems.Thm_Formalism_landauIteratedDerivatives_good_logpow

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
theorem _root_.solution (hMD : MellinDeriv) {H : ℝ → ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1))) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    {σc : ℝ} (hgood : ∀ σ, σc < σ → Good H σ) (n : ℕ) {z : ℂ} (hz : σc < z.re) :
    HasDerivAt (J H n) (J H (n + 1) z) z := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (((-Real.log x) ^ n * H x : ℝ) : ℂ))
      (volume.restrict (Ioi 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (((by fun_prop : Measurable fun x : ℝ => (-Real.log x) ^ n).aestronglyMeasurable).mul hH)
  have hint : ∀ σ : ℝ, σc < σ → IntegrableOn
      (fun x : ℝ => ‖(((-Real.log x) ^ n * H x : ℝ) : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    have := good_logpow hH (hgood ((σc + σ) / 2) (by linarith))
      (show (σc + σ) / 2 < σ by linarith) n
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    simp only
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (hpos x hx)]
    ring
  have := hMD _ σc hmeas hint z hz
  unfold J
  convert this using 2
  funext x
  push_cast
  ring
end Formalism.landauIteratedDerivatives
