-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lctwo_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:35.673964+00:00
-- url     : https://prove2.me/submissions/34686765-a8e5-49d9-ab3f-9c7afde7b189

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
import Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_le_weight

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
theorem _root_.solution {B : Type*} [CommRing B] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    {ω : Fin r × Fin n →₀ ℕ} {p : MvPolynomial (Fin r × Fin n) B}
    (hp : IsWeightedHomogeneous (pairW l j) p ω) {m : Fin r × Fin n →₀ ℕ} (hm : m ∈ p.support) (b : Fin r) :
    m (b, l) ≤ ω (b, l) ∧ m (b, j) ≤ ω (b, l) := by
  have h := hp (MvPolynomial.mem_support_iff.mp hm)
  rw [← h]
  exact lctwo_le_weight hlj m b
end Formalism.GradedWeylDivisibility
