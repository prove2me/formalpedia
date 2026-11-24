-- Prove2me | solution 1 for Formalism.ZF.rdp_horiz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:09.9321+00:00
-- url     : https://prove2.me/submissions/f2ac99f8-b368-436d-9e1c-9780cf66aa47

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Theorems.Thm_Formalism_ZF_rdp_hasDerivAt_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (a p : ℂ) (y x0 x1 : ℝ) (hy : y ≠ p.im) :
    ∫ x in x0..x1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x1 : ℂ) + y * I - p)⁻¹) - (-a * ((x0 : ℂ) + y * I - p)⁻¹) := by
  have hne : ∀ x : ℝ, (x : ℂ) + y * I ≠ p := by
    intro x h
    apply hy
    have := congrArg Complex.im h
    simpa using this
  have hder : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -a * ((t : ℂ) + y * I - p)⁻¹)
      (a / ((x : ℂ) + y * I - p) ^ 2) x := by
    intro x
    have hh : HasDerivAt (fun t : ℝ => (t : ℂ) + y * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
    have h2 := (rdp_hasDerivAt_prim a p ((x : ℂ) + y * I) (hne x)).comp x hh
    simpa [Function.comp_def] using h2
  have hcont : Continuous (fun x : ℝ => a / ((x : ℂ) + y * I - p) ^ 2) := by
    refine Continuous.div continuous_const (by fun_prop) (fun x => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hne x))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hcont.intervalIntegrable _ _)
end Formalism.ZF
