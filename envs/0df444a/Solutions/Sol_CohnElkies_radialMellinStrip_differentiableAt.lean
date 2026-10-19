-- Prove2me | solution 1 for CohnElkies.radialMellinStrip_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/7d0c3aed-312e-4f55-8f46-9c1fa3b507b4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_mellin_differentiableAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (z : ℂ) (hz : -(d : ℝ) / 2 - 2 < z.im) :
    DifferentiableAt ℂ (radialMellinStrip hd f) z := by
  have hs :
      -2 < (((d : ℂ) / 2 - Complex.I * z).re) := by
    norm_num
    linarith
  change
    DifferentiableAt ℂ
      (fun w : ℂ =>
        mellin (radialProfile hd f)
          ((d : ℂ) / 2 - Complex.I * w)) z
  let F : ℂ → ℂ := mellin (radialProfile hd f)
  let A : ℂ → ℂ := fun w => (d : ℂ) / 2 - Complex.I * w
  have houter : DifferentiableAt ℂ F (A z) :=
    radialProfile_mellin_differentiableAt
      hd f hf hzero
      ((d : ℂ) / 2 - Complex.I * z) hs
  have hinner : DifferentiableAt ℂ A z := by
    try dsimp [A]
    fun_prop
  have hcomp : DifferentiableAt ℂ (F ∘ A) z :=
    houter.comp z hinner
  exact hcomp
end CohnElkies
