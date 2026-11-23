-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.choose_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:13.152855+00:00
-- url     : https://prove2.me/submissions/73aa1cf9-55a7-42de-9719-6752a140e4a8

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_norm_natCast_le_one__a9d2d1dd10a2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
namespace IVP
theorem _root_.solution (c k : ℕ) : IVP p k (fun m => (((m + c).choose k : ℕ) : ℚ_[p])) := by
  refine ⟨⟨Polynomial.C ((k.factorial : ℚ_[p])⁻¹) * (descPochhammer ℚ_[p] k).comp (X + Polynomial.C (c : ℚ_[p])),
    ?_, fun m => ?_⟩, fun m => norm_natCast_le_one' _⟩
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_comp_le).trans ?_
    rw [descPochhammer_natDegree]
    have : (X + Polynomial.C (c : ℚ_[p])).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans ?_; simp
    nlinarith
  · simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X]
    have h1 : ((m : ℚ_[p]) + c) = ((m + c : ℕ) : ℚ_[p]) := by push_cast; ring
    rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    have : (k.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    push_cast
    field_simp
end IVP
end Formalism.GM.gammaIntegralityLemmas
