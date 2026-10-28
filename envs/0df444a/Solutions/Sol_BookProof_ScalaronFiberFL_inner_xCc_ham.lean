-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.inner_xCc_ham
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:42:22.062517+00:00
-- url     : https://prove2.me/submissions/9d8a5180-bc8c-47af-ac8d-0b5c74785485

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterQgOuterFockFlow
import Theorems.Thm_BookProof_ScalaronFiberFL_ham_eq_toLp
import Theorems.Thm_BookProof_ScalaronFiberFL_hamS_apply
-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.inner_xCc_ham
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL



open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (W : WallPot) (s : ℝ)
theorem solution (W : WallPot) (s : ℝ) (f g : ccSchwartz ℝ) :
    (inner ℂ (xCc (ccEquiv ℝ g)) (W.ham s (ccEquiv ℝ f)) : ℂ)
      = ∫ y : ℝ, (y : ℂ) * ((starRingEnd ℂ) ((g : 𝓢(ℝ, ℂ)) y)
          * (-deriv (deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) y
            + (W.pot s y : ℂ) * (f : 𝓢(ℝ, ℂ)) y)) := by
  have hx : xCc (ccEquiv ℝ g) =
      (mulCc (fun x : ℝ => x) contDiff_id g).toLp 2 (volume : Measure ℝ) := by
    simp [xCc, opCc]
  rw [hx, BookProof.ScalaronFiberFL.ham_eq_toLp, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp (mulCc (fun x : ℝ => x) contDiff_id g) 2 volume,
    SchwartzMap.coeFn_toLp (hamS W s f) 2 volume] with y hy1 hy2
  rw [hy1, hy2, BookProof.ScalaronFiberFL.hamS_apply]
  have hm : (mulCc (fun x : ℝ => x) contDiff_id g) y = (y : ℂ) * (g : 𝓢(ℝ, ℂ)) y := rfl
  rw [hm]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring
