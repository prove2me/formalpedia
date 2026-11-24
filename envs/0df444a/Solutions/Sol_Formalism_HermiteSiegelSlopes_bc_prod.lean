-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.bc_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:26.557017+00:00
-- url     : https://prove2.me/submissions/a2d4c165-c676-4b9d-b1c7-b4742c732794

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
theorem _root_.solution [IsTotallyComplex F] [IsTotallyComplex E] (g : InfinitePlace F → ℝ) :
    ∏ w : InfinitePlace E, g (w.comap (algebraMap F E)) = (∏ v, g v) ^ finrank F E := by
  classical
  have hfib : ∀ v : InfinitePlace F,
      (Finset.univ.filter fun w : InfinitePlace E => w.comap (algebraMap F E) = v).card = finrank F E := by
    intro v
    rw [← ncard_places_over_eq_finrank v, ← Set.ncard_coe_finset]
    congr 1
    ext w
    simp
  rw [← Finset.prod_fiberwise_of_maps_to (g := fun w : InfinitePlace E => w.comap (algebraMap F E))
    (t := Finset.univ) (by intro x _; exact Finset.mem_univ _), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_congr rfl (fun w hw => by rw [(Finset.mem_filter.1 hw).2]), Finset.prod_const, hfib v]
end Formalism.HermiteSiegelSlopes
