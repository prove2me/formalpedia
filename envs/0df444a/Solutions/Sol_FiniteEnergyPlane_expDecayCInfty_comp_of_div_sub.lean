-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInfty_comp_of_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T21:58:12.773377+00:00
-- url     : https://prove2.me/submissions/e2bda1cf-6f65-43a3-aaf9-d65f52d72b0c

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_logCoords_of_div_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_shift
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_congr



/-! # B2: decay is preserved by composition with a map asymptotic to `z ↦ κ z`. -/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Real

noncomputable section

theorem expDecayCInfty_comp_of_div_sub_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b)
    (f : ℂ → F) (b' : ℝ) (hf : ExpDecayCInfty (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) b') :
    ExpDecayCInfty (fun p : ℝ × ℝ => f (χ (cylInf p.1 p.2))) b' := by
  obtain ⟨E, S, hE, hS⟩ := exists_logCoords_of_div_sub χ κ hκ b hb has
  have h := expDecayCInfty_comp_shift (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) b' hf E b hb hE
    (Real.log ‖κ‖ / (2 * π), Complex.arg κ / (2 * π))
  exact expDecayCInfty_congr h (s₀ := S) fun s hs t => by
    simp only
    rw [hS s hs.le t]

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric
open scoped ContDiff Real

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (b : ℝ) (hb : 0 < b)
    (has : ExpDecayCInfty (fun p : ℝ × ℝ => χ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b)
    (f : ℂ → F) (b' : ℝ) (hf : ExpDecayCInfty (fun p : ℝ × ℝ => f (cylInf p.1 p.2)) b') :
    ExpDecayCInfty (fun p : ℝ × ℝ => f (χ (cylInf p.1 p.2))) b' :=
  expDecayCInfty_comp_of_div_sub_aux χ κ hκ b hb has f b' hf
