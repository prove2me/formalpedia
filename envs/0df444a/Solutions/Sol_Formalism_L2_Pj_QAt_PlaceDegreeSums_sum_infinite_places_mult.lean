-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.PlaceDegreeSums.sum_infinite_places_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:25.982641+00:00
-- url     : https://prove2.me/submissions/a10c0a9c-4639-4eaa-82b6-65afdc97abb2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DegreeInfimum_PlaceDegreeSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.PlaceDegreeSums
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.Pj.QAt.PlaceDegreeSums
theorem _root_.solution (f : InfinitePlace K → ℝ) :
    ∑ σ : InfinitePlace K, (σ.mult : ℝ) * f σ = ∑ τ : K →+* ℂ, f (InfinitePlace.mk τ) := by
  classical
  refine Eq.trans ?_ (Finset.sum_fiberwise Finset.univ (fun τ : K →+* ℂ => InfinitePlace.mk τ)
    (fun τ => f (InfinitePlace.mk τ)))
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f w) (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
    Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
end Formalism.L2.Pj.QAt.PlaceDegreeSums
