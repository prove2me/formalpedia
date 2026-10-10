-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.norm_derivL2_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:06:02.905672+00:00
-- url     : https://prove2.me/submissions/92688125-41b3-4363-a67b-4ae147b68e07

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.StrichartzWave
open BookProof.ScalaronFiberFL

open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

theorem solution (W : WallPot) (s : ℝ) (hs : 0 ≤ s) (f : ccSchwartz ℝ) :
    ‖derivL2 f‖ ^ 2 ≤ quadForm (W.ham s) (ccEquiv ℝ f) := by
  have hn : ‖derivL2 f‖ ^ 2 = ∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 := by
    have h1 : (‖derivL2 f‖ ^ 2 : ℝ) = RCLike.re (inner ℂ (derivL2 f) (derivL2 f)) :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    rw [h1, MeasureTheory.L2.inner_def]
    have h2 : (fun x => (inner ℂ ((derivL2 f : ℝ → ℂ) x) ((derivL2 f : ℝ → ℂ) x) : ℂ))
        =ᵐ[volume] fun x => (((‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 : ℝ)) : ℂ) := by
      filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.derivCLM ℂ ℂ (f : 𝓢(ℝ, ℂ))) 2
        (volume : Measure ℝ)] with x hx
      simp only [derivL2]
      rw [hx, SchwartzMap.derivCLM_apply, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [integral_congr_ae h2, integral_complex_ofReal]
    simp
  rw [hn, ham_quadForm]
  have h2 : (0 : ℝ) ≤ ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (W.pot_nonneg s hs x) (by positivity)
  linarith
