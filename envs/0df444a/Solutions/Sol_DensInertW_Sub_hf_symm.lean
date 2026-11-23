-- Prove2me | solution 1 for DensInertW.Sub.hf_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:38.167027+00:00
-- url     : https://prove2.me/submissions/65da5cec-328c-4b86-80b5-91a29b717cdc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Theorems.Thm_DensInertW_Sub_q_ne_zero_of_inv
import Theorems.Thm_DensInertW_Sub_sig_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : ∀ k l, M l k = M k l ^ q) (x y : Fin n → L) : hf q M y x = (hf q M x y) ^ q := by
  have hq := q_ne_zero_of_inv hinv
  have e : (hf q M x y) ^ q = sig q hq hadd (hf q M x y) := rfl
  rw [e]
  simp only [hf, map_sum, map_mul, map_pow, sig_apply, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hM]
  ring
end DensInertW.Sub
