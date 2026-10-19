-- Prove2me | solution 1 for ContWeatherall.homotopyOp_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T21:08:46.684954+00:00
-- url     : https://prove2.me/submissions/c14591a2-37cc-4fe4-8cf0-6c92722209af

import Mathlib
import Definitions.Def_ContWeatherall_defs
import Theorems.Thm_ContWeatherall_contDiff_parametric_intervalIntegral

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

theorem hoc_main {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (homotopyOp w) := by
  have hc : ContDiff ℝ ∞ (fun p : E × ℝ =>
      p.2 ^ k • (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k) (w (p.2 • p.1))) p.1) := by
    have h1 : ContDiff ℝ ∞ (fun p : E × ℝ => w (p.2 • p.1)) :=
      hw.comp (contDiff_snd.smul contDiff_fst)
    have h2 := ((curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.contDiff.comp
      h1).clm_apply contDiff_fst
    exact (contDiff_snd.pow k).smul h2
  exact contDiff_parametric_intervalIntegral (f := fun x t => t ^ k • (w (t • x)).curryLeft x) hc 0 1

end ContWeatherall

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (ContWeatherall.homotopyOp w) :=
  ContWeatherall.hoc_main hw
