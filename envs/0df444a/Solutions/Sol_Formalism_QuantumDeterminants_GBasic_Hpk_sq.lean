-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.Hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:52.024337+00:00
-- url     : https://prove2.me/submissions/6f80dee9-7e81-4d53-b704-eb02d09641dd

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sgn_sig
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.GBasic
namespace Formalism.QuantumDeterminants.GBasic
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sig_sig,
    sgn_sig, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    unfold sgn
    split_ifs <;> norm_num
  · rw [if_neg (fun e => h e.symm), if_neg h]
    exact mul_zero _
end Formalism.QuantumDeterminants.GBasic
