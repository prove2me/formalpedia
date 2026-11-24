-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_mem_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:10.959429+00:00
-- url     : https://prove2.me/submissions/77ea343d-b485-4ef4-a28a-b2f068e7223b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {n : ℕ} (s : Fin n) {d p q N : ℕ} (h : p + q = d)
    (hN : (p + q).choose q ∣ N) :
    (N : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q ∈ la_binLat R s d := by
  obtain ⟨c, rfl⟩ := hN
  have hmem : ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q ∈
      la_binLat R s d := Submodule.subset_span ⟨p, q, h, rfl⟩
  have h2 := Submodule.smul_mem _ (c : R) hmem
  rw [MvPolynomial.smul_eq_C_mul, map_natCast] at h2
  rw [Nat.cast_mul, mul_comm ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R), mul_assoc]
  exact h2
end Formalism.CohomologicalDescent.LA
