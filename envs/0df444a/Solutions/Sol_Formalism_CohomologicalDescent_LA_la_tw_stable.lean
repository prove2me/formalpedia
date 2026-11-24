-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_tw_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:42.762253+00:00
-- url     : https://prove2.me/submissions/74c2fd92-fa66-4de7-97c8-1695dd260e2a

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_tw_ne
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_tw_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] (L : Submodule R (MvPolynomial (Fin 2 × Fin 2) R))
    (hs : ∀ (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) R), f ∈ L →
      rowDiv R a b k f ∈ L) (c : ℕ) (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) R)
    (hf : f ∈ L.map (LinearMap.mulLeft R (la_det R ^ c))) :
    rowDiv R a b k f ∈ L.map (LinearMap.mulLeft R (la_det R ^ c)) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  simp only [LinearMap.mulLeft_apply]
  by_cases hab : a = b
  · subst hab
    rw [la_rowDiv_tw_eq]
    refine Submodule.mem_map.mpr ⟨_, Submodule.sum_mem _ (fun x _ => ?_), rfl⟩
    rw [← nsmul_eq_mul]
    exact nsmul_mem (hs _ _ _ _ hg) _
  · rw [la_rowDiv_tw_ne R a b hab]
    exact Submodule.mem_map.mpr ⟨_, hs _ _ _ _ hg, rfl⟩
end Formalism.CohomologicalDescent.LA
