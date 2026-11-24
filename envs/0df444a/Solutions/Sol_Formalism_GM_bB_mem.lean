-- Prove2me | solution 1 for Formalism.GM.bB_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:10.08383+00:00
-- url     : https://prove2.me/submissions/652aaed0-7bbb-4d3d-916a-1d3846fae2cb

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
import Theorems.Thm_Formalism_GM_C_mem_zpT
import Theorems.Thm_Formalism_GM_X_mem_zpT
import Theorems.Thm_Formalism_GM_div_mem_zpS
import Theorems.Thm_Formalism_GM_bB_zero
import Theorems.Thm_Formalism_GM_bB_pascal
import Theorems.Thm_Formalism_GM_bB_succ_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial
namespace Formalism.GM
theorem _root_.solution (p k : ℕ) [Fact p.Prime] : ∀ i, i ≤ p ^ k → ∀ t : ℤ, bB ((p : ℚ) ^ k) i t ∈ zpT p := by
  intro i
  induction i with
  | zero => intro _ t; rw [bB_zero]; exact Subring.one_mem _
  | succ i ih =>
    intro hi t
    have ih' := ih (by omega)
    have h0 : bB ((p : ℚ) ^ k) (i + 1) 0 ∈ zpT p := by
      rw [bB_succ_zero]
      refine Subring.mul_mem _ (Subring.mul_mem _ (C_mem_zpT p ?_) (X_mem_zpT p)) (ih' _)
      exact div_mem_zpS p k (i + 1) (by omega) hi
    induction t using Int.induction_on with
    | zero => exact h0
    | succ n hn => rw [bB_pascal]; exact Subring.add_mem _ hn (ih' _)
    | pred n hn =>
      have e := bB_pascal ((p : ℚ) ^ k) i (-(n : ℤ) - 1)
      rw [sub_add_cancel] at e
      rw [show bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ) - 1) = bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ)) - bB ((p : ℚ) ^ k) i (-(n : ℤ) - 1) by
        rw [e]; ring]
      exact Subring.sub_mem _ hn (ih' _)
end Formalism.GM
