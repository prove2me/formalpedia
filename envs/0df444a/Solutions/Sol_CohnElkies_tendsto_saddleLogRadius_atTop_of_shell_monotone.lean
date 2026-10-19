-- Prove2me | solution 1 for CohnElkies.tendsto_saddleLogRadius_atTop_of_shell_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/d0263cbd-025d-4085-a373-156b26f7444e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleLogRadius_eq_digamma_add_shellDerivative
import Theorems.Thm_CohnElkies_tendsto_saddleDigamma_atTop
import Theorems.Thm_CohnElkies_tendsto_saddleGammaArgument_atTop

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
    (hmono : MonotoneOn (saddleSourceShellDerivative ε)
      (Ici (1 + ε / 2))) :
    Tendsto (saddleLogRadius ε d) atTop atTop := by
  have _hε : 0 < ε := hε
  have _horder : shortCutoff ε ≤ shortEndpoint ε := horder
  let U : ℝ := 1 + ε / 2
  let C : ℝ := saddleSourceShellDerivative ε U
  have hargument := tendsto_saddleDigamma_atTop.comp
    (tendsto_saddleGammaArgument_atTop hd)
  have hhalf :=
    hargument.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hbaseline :=
    hhalf.atTop_add
      (tendsto_const_nhds
        (x := -(Real.log Real.pi) / 2 + C))
  have hcomparison :
      (fun u : ℝ =>
        saddleDigamma
          (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
          (-(Real.log Real.pi) / 2 + C)) ≤ᶠ[atTop]
        saddleLogRadius ε d := by
    filter_upwards [eventually_ge_atTop U]
      with u hu
    have hshell : C ≤ saddleSourceShellDerivative ε u := by
      apply hmono
      · change 1 + ε / 2 ≤ U
        try dsimp [U]
        exact le_rfl
      · simpa [U] using! hu
      · exact hu
    rw [saddleLogRadius_eq_digamma_add_shellDerivative]
    try dsimp [C]
    linarith
  exact tendsto_atTop_mono' atTop hcomparison hbaseline
end CohnElkies
