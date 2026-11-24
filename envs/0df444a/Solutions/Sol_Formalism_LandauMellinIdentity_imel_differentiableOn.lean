-- Prove2me | solution 1 for Formalism.LandauMellinIdentity.imel_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:49.7595+00:00
-- url     : https://prove2.me/submissions/38757503-73a6-4bc7-b386-6c837dcc02ba

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Theorems.Thm_Formalism_mellinDeriv


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
open Formalism.LandauMellinIdentity
namespace Formalism.LandauMellinIdentity
theorem _root_.solution {H : ℝ → ℝ} {a : ℝ}
    (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    (hpos : ∀ x : ℝ, 1 < x → 0 ≤ H x)
    (hint : ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) :
    DifferentiableOn ℂ (Imel H) {s : ℂ | a < s.re} := by
  intro s hs
  have hHc : AEStronglyMeasurable (fun x : ℝ => (H x : ℂ)) (volume.restrict (Ioi 1)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hH)
  have hnorm : ∀ σ : ℝ, a < σ →
      IntegrableOn (fun x : ℝ => ‖(H x : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    refine (hint σ hσ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos x hx)]
  exact (mellinDeriv (fun x => (H x : ℂ)) a hHc hnorm s hs).differentiableAt
    |>.differentiableWithinAt
end Formalism.LandauMellinIdentity
