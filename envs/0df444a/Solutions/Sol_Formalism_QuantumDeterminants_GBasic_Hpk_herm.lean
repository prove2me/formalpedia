-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.Hpk_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:52.028591+00:00
-- url     : https://prove2.me/submissions/2e180415-c201-47ec-b776-798b9c60f2e4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sgn_sig
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_eq_sig_iff

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
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_eq, Hpk_eq]
  by_cases h : j = sig k r i
  · rw [if_pos ((eq_sig_iff k r i j).2 h), if_pos h, h, sgn_sig]
    unfold sgn
    split_ifs <;> simp
  · rw [if_neg (fun e => h ((eq_sig_iff k r i j).1 e)), if_neg h, star_zero]
end Formalism.QuantumDeterminants.GBasic
