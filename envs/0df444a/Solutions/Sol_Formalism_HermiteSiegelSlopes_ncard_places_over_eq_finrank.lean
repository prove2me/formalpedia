-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.ncard_places_over_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:13.252828+00:00
-- url     : https://prove2.me/submissions/c4d42a1b-af3a-4132-996c-33fc1ddb2e14

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_infinitePlace_liesOver_comap

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
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution [IsTotallyComplex F] (v : InfinitePlace F) :
    {w : InfinitePlace E | w.comap (algebraMap F E) = v}.ncard = finrank F E := by
  have h := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank E v
  have hr : InfinitePlace.ramifiedPlacesOver E v = ∅ := by
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    have h3 := (InfinitePlace.isRamified_iff.1 h2).2
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h3
  have hu : InfinitePlace.unramifiedPlacesOver E v =
      {w : InfinitePlace E | w.comap (algebraMap F E) = v} := by
    ext w
    constructor
    · rintro ⟨h1, -⟩
      exact InfinitePlace.LiesOver.comap_eq w v
    · intro hw
      have hw' : w.comap (algebraMap F E) = v := hw
      refine ⟨hw' ▸ infinitePlace_liesOver_comap w, ?_⟩
      by_contra hc
      have h3 := (InfinitePlace.isRamified_iff.1 hc).2
      exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h3
  rw [hr, hu] at h
  simpa using h
end Formalism.HermiteSiegelSlopes
