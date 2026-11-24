-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_iter_Eul_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:45.562163+00:00
-- url     : https://prove2.me/submissions/ec9a7f5c-eca4-45ef-bdd5-c1a97f59c691

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_comm_EulF_l


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
    (hf : ndEul R r n l f = c • f) (k : ℕ) :
    ndEul R r n l ((ndF R r n l j)^[k] f) = (c - k) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply', nd_comm_EulF_l hlj, ih, Derivation.map_smul, Nat.cast_succ,
      show c - ((k : R) + 1) = (c - k) - 1 by ring, sub_smul (c - k) 1, one_smul]
end Formalism.GradedWeylDivisibility
