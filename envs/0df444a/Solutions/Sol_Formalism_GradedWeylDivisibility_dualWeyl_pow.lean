-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeyl_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:18.915486+00:00
-- url     : https://prove2.me/submissions/ef6252d9-816c-40dc-ac2f-001022b743c1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeyl_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_one_mem_dualWeyl

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
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν) (k : ℕ) :
    f ^ k ∈ dualWeyl R r n (k • ν) := by
  induction k with
  | zero => simpa using (one_mem_dualWeyl (R := R) (r := r) (n := n))
  | succ k ih => rw [pow_succ, succ_nsmul]; exact dualWeyl_mul ih hf
end Formalism.GradedWeylDivisibility
