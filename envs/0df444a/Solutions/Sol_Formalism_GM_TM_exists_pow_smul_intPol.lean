-- Prove2me | solution 1 for Formalism.GM.TM.exists_pow_smul_intPol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:24.648377+00:00
-- url     : https://prove2.me/submissions/29f9c7e9-e8c0-4e59-9ab1-c8444f4cacd8

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.TM
theorem _root_.solution {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • x ∈ IntPol p σ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (∑ m ∈ x.support, ‖x.coeff m‖) hp
  refine ⟨k, mem_intPol_of_norm _ fun m => ?_⟩
  rw [coeff_smul, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p]
  by_cases hm : m ∈ x.support
  · have h1 : ‖x.coeff m‖ ≤ ∑ m ∈ x.support, ‖x.coeff m‖ :=
      Finset.single_le_sum (f := fun m => ‖x.coeff m‖) (fun _ _ => norm_nonneg _) hm
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    rw [inv_pow, inv_mul_le_iff₀ hpk, mul_one]
    linarith
  · rw [notMem_support_iff.mp hm, norm_zero, mul_zero]; exact zero_le_one
end Formalism.GM.TM
