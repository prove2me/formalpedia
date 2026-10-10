-- Prove2me | solution 1 for BookProof.ScalaronFiberFL.ham_eq_toLp
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:07:13.51228+00:00
-- url     : https://prove2.me/submissions/c9a8a79d-f910-4be5-8979-355b24b40048

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

theorem solution (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) :
    W.ham s (ccEquiv ℝ f) = (hamS W s f).toLp 2 (volume : Measure ℝ) := by
  have hsch : (schwartzEquiv ℝ).symm
      (Submodule.inclusion (ccDomain_le_schwartzDomain (E := ℝ)) (ccEquiv ℝ f))
        = (f : 𝓢(ℝ, ℂ)) := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  simp only [WallPot.ham, wallHam, LinearMap.add_apply, kinCcR, opCc, opL2,
    LinearMap.comp_apply, LinearEquiv.coe_coe, hsch, LinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_coe, hamS]
  rw [← map_add]
  rfl
