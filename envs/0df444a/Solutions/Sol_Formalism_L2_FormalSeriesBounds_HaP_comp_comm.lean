-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:22.234003+00:00
-- url     : https://prove2.me/submissions/e527e636-ad85-41ef-87bc-b71b27c8dac8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_smul_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (lam : K →ₗ[ℚ] ℚ) (Φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (Ψ : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ)
    (h : ∀ m, Φ (monomial m 1) = map (algebraMap ℚ K) (Ψ (monomial m 1))) (P : MvPolynomial σ K) :
    comp lam (Φ P) = Ψ (comp lam P) := by
  have hP : P = ∑ m ∈ P.support, coeff m P • monomial m (1 : K) := by
    conv_lhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hc : comp lam P = ∑ m ∈ P.support, lam (coeff m P) • monomial m (1 : ℚ) := by
    unfold comp
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_sum]
  conv_lhs => rw [hP]
  rw [map_sum, comp_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul Φ, h, comp_smul_map, map_smul Ψ]
end Formalism.L2.FormalSeriesBounds.HaP
