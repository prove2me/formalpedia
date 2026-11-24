-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclint_degreeOf_none_rename_some
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:58.913741+00:00
-- url     : https://prove2.me/submissions/df35d3b2-abbf-436c-8e0a-2688ad963cd2

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LeadInterlaced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {B : Type*} [CommRing B] {σ : Type*}
    (p : MvPolynomial σ B) : degreeOf none (rename (some : σ → Option σ) p) = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero ((degreeOf_le_iff).2 ?_)
  intro m hm
  rw [support_rename_of_injective (Option.some_injective σ)] at hm
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.1 hm
  exact (Finsupp.mapDomain_notin_range m' none (by simp)).le
end Formalism.GradedWeylDivisibility
