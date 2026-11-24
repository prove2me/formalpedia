-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lcdeg_degreeOf_X_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:52.668264+00:00
-- url     : https://prove2.me/submissions/f6a5678a-5211-4080-804f-b9bf139fddd3

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCdegLemmas

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
theorem _root_.solution {σ R : Type*} [CommRing R] [DecidableEq σ] (i j : σ) :
    degreeOf i (X j : MvPolynomial σ R) ≤ if j = i then 1 else 0 := by
  rw [degreeOf_eq_sup]
  refine Finset.sup_le fun m hm => ?_
  have hm' : m ∈ (monomial (Finsupp.single j 1) (1 : R)).support := hm
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hm')
  rw [Finsupp.single_apply]
end Formalism.GradedWeylDivisibility
