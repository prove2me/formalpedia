-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nd_iter_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:50.546013+00:00
-- url     : https://prove2.me/submissions/81d65b32-5944-404a-bcc2-975e197b7fa9

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_Eul_l
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_Eul_j
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_comm_EF


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
theorem _root_.solution {l j : Fin n} (hlj : l ≠ j) {f : MvPolynomial (Fin r × Fin n) R} {cl cj : R}
    (hl : ndEul R r n l f = cl • f) (hj : ndEul R r n j f = cj • f) (hE : ndE R r n l j f = 0)
    (k : ℕ) :
    ndE R r n l j ((ndF R r n l j)^[k + 1] f) =
      (((k : R) + 1) * (cl - cj - k)) • (ndF R r n l j)^[k] f := by
  induction k with
  | zero =>
    rw [zero_add, Function.iterate_one, nd_comm_EF hlj, hE, map_zero, hl, hj]
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add, one_mul, sub_zero]
    rw [sub_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply' (ndF R r n l j) (k + 1) f, nd_comm_EF hlj, ih,
      Derivation.map_smul, nd_iter_Eul_l hlj hl, nd_iter_Eul_j hlj hj,
      ← Function.iterate_succ_apply' (ndF R r n l j) k f, ← sub_smul, ← add_smul]
    congr 1
    push_cast; ring
end Formalism.GradedWeylDivisibility
