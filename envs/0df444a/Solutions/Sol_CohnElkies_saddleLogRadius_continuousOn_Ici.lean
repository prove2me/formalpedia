-- Prove2me | solution 1 for CohnElkies.saddleLogRadius_continuousOn_Ici
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/3fa61884-a478-4501-a240-8fc391eff125

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleLogRadius_eq_digamma_add_shellDerivative
import Theorems.Thm_CohnElkies_saddleSourceShellDerivative_contDiff_one
import Theorems.Thm_CohnElkies_saddleDigamma_continuousOn_Ioi

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {d : ℕ} (hd : 0 < d)
    {u₀ : ℝ} (hu₀ : -1 < u₀) :
    ContinuousOn (saddleLogRadius ε d) (Ici u₀) := by
  let g : ℝ → ℝ := fun u =>
    ((d : ℝ) / 2) * (1 + u) / 2
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hg : Continuous g := by
    try dsimp [g]
    fun_prop
  have hmap : MapsTo g (Ici u₀) (Ioi (0 : ℝ)) := by
    intro u hu
    try dsimp [g]
    have hu' : u₀ ≤ u := hu
    have hupositive : 0 < 1 + u := by
      linarith
    change 0 < ((d : ℝ) / 2) * (1 + u) / 2
    positivity
  have hdigamma :
      ContinuousOn (fun u => saddleDigamma (g u)) (Ici u₀) :=
    saddleDigamma_continuousOn_Ioi.comp
      hg.continuousOn hmap
  have hshell :
      ContinuousOn (saddleSourceShellDerivative ε)
        (Ici u₀) :=
    (saddleSourceShellDerivative_contDiff_one
      hε horder).continuous.continuousOn
  have hsum :
      ContinuousOn
        (fun u : ℝ =>
          -(Real.log Real.pi) / 2 +
            saddleDigamma (g u) / 2 +
              saddleSourceShellDerivative ε u)
        (Ici u₀) :=
    (continuousOn_const.add
      (hdigamma.div_const 2)).add hshell
  apply hsum.congr
  intro u hu
  simpa [g] using!
    saddleLogRadius_eq_digamma_add_shellDerivative
      ε d u
end CohnElkies
