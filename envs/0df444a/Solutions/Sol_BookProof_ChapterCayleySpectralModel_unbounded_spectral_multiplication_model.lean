-- Prove2me | solution 1 for BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:43:47.618441+00:00
-- url     : https://prove2.me/submissions/615df994-2019-45eb-9dd5-c2926f777aaa

import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCayleySpectralModel
import Definitions.Def_ChapterStoneResolvent
-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model
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
theorem h44_cfcHom_resSymbol {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint H) (y : H) :
    cfcHom (BookProof.ChapterCayleySpectralModel.isStarNormal_cayleyCLM T)
      (BookProof.ChapterCayleySpectralModel.resSymbol T) y = ((T.res (-1) y : T.domain) : H) := by
  rw [BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol_eq,
    BookProof.ChapterCayleySpectralModel.res_neg_one_eq_cayley]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, BookProof.ChapterCayleySpectralModel.cayleyCLM_apply]

theorem solution (hxi : ‖xi‖ = 1)
    (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) :
    ∃ (mu : Measure (spectrum ℂ (cayleyCLM T))) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ u : Lp ℂ 2 mu, ∃ hmem : U (mulRep mu (resSymbol T) u) ∈ T.domain,
        T.op ⟨U (mulRep mu (resSymbol T) u), hmem⟩ = U (mulRep mu (opSymbol T) u)) ∧
      (∀ x : T.domain, ∃ u : Lp ℂ 2 mu, U (mulRep mu (resSymbol T) u) = (x : H)) := by
  have hT := isStarNormal_cayleyCLM T
  refine ⟨BookProof.ChapterSpectralMultiplication.spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi,
    BookProof.ChapterSpectralMultiplication.isProbabilityMeasure_spectralMeasure _ _ xi hxi,
    BookProof.ChapterSpectralMultiplication.spectralUnitary _ (isStarNormal_cayleyCLM T) xi hcyc, ?_, ?_⟩
  · intro u
    have hres : BookProof.ChapterSpectralMultiplication.spectralUnitary _ (isStarNormal_cayleyCLM T) xi hcyc
        (mulRep _ (resSymbol T) u) = ((T.res (-1) (BookProof.ChapterSpectralMultiplication.spectralUnitary _ (isStarNormal_cayleyCLM T) xi hcyc u) : T.domain) : H) := by
      rw [BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines_cfc]
      exact h44_cfcHom_resSymbol T _
    refine ⟨hres ▸ (T.res (-1) _).2, ?_⟩
    refine (congrArg T.op (Subtype.ext hres : (⟨_, hres ▸ (T.res (-1) _).2⟩ : T.domain) = T.res (-1) _)).trans ?_
    rw [BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines_cfc, h44_cfcHom_opSymbol]
  · intro x
    refine ⟨(BookProof.ChapterSpectralMultiplication.spectralUnitary _ (isStarNormal_cayleyCLM T) xi hcyc).symm
      (T.shift (-1) x), ?_⟩
    rw [BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines_cfc, h44_cfcHom_resSymbol,
      LinearIsometryEquiv.apply_symm_apply, T.res_shift (by norm_num)]

