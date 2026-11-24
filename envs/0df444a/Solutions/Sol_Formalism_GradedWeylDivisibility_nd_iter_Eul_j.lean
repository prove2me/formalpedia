-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_iter_Eul_j
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:08.447856+00:00
-- url     : https://prove2.me/submissions/3e7f022e-7d6f-4659-8548-acbac7a19e6b

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_comm_EulF_j


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
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {c : R}
    (hf : ndEul R r n j f = c • f) (k : ℕ) :
    ndEul R r n j ((ndF R r n l j)^[k] f) = (c + k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_j hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c + ((k : R) + 1) = (c + k) + 1 by ring, add_smul (c + k) 1, one_smul]
end Formalism.GradedWeylDivisibility
