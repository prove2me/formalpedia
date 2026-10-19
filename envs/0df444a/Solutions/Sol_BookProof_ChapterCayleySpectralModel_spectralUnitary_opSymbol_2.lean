-- Prove2me | solution 2 for BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:42:39.23241+00:00
-- url     : https://prove2.me/submissions/bc38a629-9e82-400c-a376-6688c4c000ff

import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCayleySpectralModel
import Definitions.Def_ChapterStoneResolvent
-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
open BookProof.ChapterCayleySpectralModel


open scoped InnerProductSpace
open MeasureTheory


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable (xi : H)
theorem h44_cfcHom_opSymbol {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (y : H) :
    cfcHom (BookProof.ChapterCayleySpectralModel.isStarNormal_cayleyCLM T)
      (BookProof.ChapterCayleySpectralModel.opSymbol T) y = T.op (T.res (-1) y) := by
  rw [BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol_eq]
  have hy : T.shift (-1) (T.res (-1) y) = y := T.shift_res (by norm_num) y
  rw [BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.shift_apply] at hy
  have hr := BookProof.ChapterCayleySpectralModel.res_neg_one_eq_cayley T y
  have hI : Complex.I * (2 * Complex.I)⁻¹ = 2⁻¹ := by field_simp
  have hr' : Complex.I • ((T.res (-1) y : _) : H)
      = (2⁻¹ : ℂ) • (y - BookProof.ChapterCayleyTransform.cayley T y) := by
    rw [hr, smul_smul, hI]
  have hc : (((-1 : ℝ) : ℂ) * Complex.I) = -Complex.I := by push_cast; ring
  rw [hc] at hy
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, BookProof.ChapterCayleySpectralModel.cayleyCLM_apply]
  linear_combination (norm := module) -hy + hr'

theorem solution
    (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi))
    (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) :
    spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc
        (mulRep (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi) (opSymbol T) u)
      = T.op (T.res (-1) (spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc u)) := by
  rw [BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines_cfc]
  exact h44_cfcHom_opSymbol T _

