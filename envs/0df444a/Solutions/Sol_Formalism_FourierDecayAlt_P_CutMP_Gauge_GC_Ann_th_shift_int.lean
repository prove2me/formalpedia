-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.th_shift_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:51.208854+00:00
-- url     : https://prove2.me/submissions/788d3c47-40d8-4fc2-9e55-bdf29a2f3649

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_Hh_add_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_th_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (k : ℤ) :
    ∀ w ∈ Hh TT, th TT α (w + (k : ℂ) * (2 * Real.pi * I)) = th TT α w + k * (2 * (circleIntegral α 0 (TT + 1)).im) := by
  intro w hw
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    have hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int (n : ℤ)).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring,
      h1, ih]
    ring
  · intro n ih
    have hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int _).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring,
      ih] at h1
    linarith
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
