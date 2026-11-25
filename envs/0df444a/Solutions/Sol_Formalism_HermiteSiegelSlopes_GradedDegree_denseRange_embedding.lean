-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.GradedDegree.denseRange_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:09.489868+00:00
-- url     : https://prove2.me/submissions/97f166c2-60ac-403e-bc3d-1edaab2703d2

import Mathlib
import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SubmoduleSlopeLowerOfFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open Formalism.HermiteSiegelSlopes.GradedDegree
namespace Formalism.HermiteSiegelSlopes.GradedDegree
theorem _root_.solution {K : Type} [Field K] [NumberField K] (v : InfinitePlace K)
    (hv : v.IsComplex) : DenseRange (v.embedding : K → ℂ) := by
  have hcl := Complex.subfield_eq_of_closed
    (Subfield.isClosed_topologicalClosure (v.embedding.fieldRange))
  rcases hcl with h | h
  · exfalso
    have hreal : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ (v.embedding.fieldRange).topologicalClosure :=
        Subfield.le_topologicalClosure _ ⟨x, rfl⟩
      rw [h] at hx
      obtain ⟨r, hr⟩ := hx
      simp only [ComplexEmbedding.conjugate_coe_eq]
      rw [← hr]
      exact Complex.conj_ofReal r
    exact (InfinitePlace.not_isReal_iff_isComplex.2 hv)
      ((InfinitePlace.isReal_iff).2 hreal)
  · intro z
    have hz : z ∈ (v.embedding.fieldRange).topologicalClosure := by rw [h]; trivial
    have hz' : z ∈ _root_.closure ((v.embedding.fieldRange : Subfield ℂ) : Set ℂ) := hz
    rwa [RingHom.coe_fieldRange] at hz'
end Formalism.HermiteSiegelSlopes.GradedDegree
