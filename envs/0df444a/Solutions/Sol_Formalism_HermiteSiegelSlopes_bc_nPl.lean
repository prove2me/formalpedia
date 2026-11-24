-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.bc_nPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:29.663977+00:00
-- url     : https://prove2.me/submissions/3750b37a-8c67-428b-9d82-910587a35313

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_ncard_places_over_eq_finrank

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
theorem _root_.solution [IsTotallyComplex F] [IsTotallyComplex E] :
    nPl E = finrank F E * nPl F := by
  classical
  have hfib : ∀ v : InfinitePlace F,
      (Finset.univ.filter fun w : InfinitePlace E => w.comap (algebraMap F E) = v).card = finrank F E := by
    intro v
    rw [← ncard_places_over_eq_finrank v, ← Set.ncard_coe_finset]
    congr 1
    ext w
    simp
  unfold nPl
  rw [← Finset.card_univ (α := InfinitePlace E),
    Finset.card_eq_sum_card_fiberwise (f := fun w : InfinitePlace E => w.comap (algebraMap F E))
      (t := Finset.univ) (by intro x _; exact Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun v _ => hfib v, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring
end Formalism.HermiteSiegelSlopes
