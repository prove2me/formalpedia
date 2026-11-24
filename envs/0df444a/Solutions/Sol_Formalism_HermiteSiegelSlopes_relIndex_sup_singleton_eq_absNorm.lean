-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.relIndex_sup_singleton_eq_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:09.479906+00:00
-- url     : https://prove2.me/submissions/043d5ed2-2d08-441e-ad88-04581ca522d0

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (A : Submodule (𝓞 K) V) (m : V) :
    A.toAddSubgroup.relIndex (A ⊔ Submodule.span (𝓞 K) {m}).toAddSubgroup =
      Ideal.absNorm (A.comap (LinearMap.toSpanSingleton (𝓞 K) V m) : Ideal (𝓞 K)) := by
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, Ideal.absNorm_apply]
  unfold Submodule.cardQuot
  rw [← AddSubgroup.relIndex_top_right]
  have h1 : (Submodule.span (𝓞 K) {m}).toAddSubgroup =
      (⊤ : AddSubgroup (𝓞 K)).map (LinearMap.toSpanSingleton (𝓞 K) V m).toAddMonoidHom := by
    ext x
    simp [Submodule.mem_span_singleton]
  rw [h1, ← AddSubgroup.relIndex_comap]
  rfl
end Formalism.HermiteSiegelSlopes
