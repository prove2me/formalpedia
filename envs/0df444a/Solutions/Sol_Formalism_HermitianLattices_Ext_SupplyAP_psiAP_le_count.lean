-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.psiAP_le_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:34.2987+00:00
-- url     : https://prove2.me/submissions/58902f47-5897-421f-936a-be7912337663

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (m a : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    psiAP m a x ≤ Real.log x * ((primesAP m a x).card : ℝ) + 2 * Real.sqrt x * Real.log x := by
  classical
  unfold psiAP
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun n : ℕ => n.Prime)]
  refine add_le_add ?_ ?_
  · have hset : ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD m])).filter (fun n : ℕ => n.Prime)
        = primesAP m a x := by
      ext n
      simp only [primesAP, Finset.mem_filter]
      tauto
    rw [hset]
    calc ∑ n ∈ primesAP m a x, ArithmeticFunction.vonMangoldt n
        ≤ ∑ _n ∈ primesAP m a x, Real.log x := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [primesAP, Finset.mem_filter, Finset.mem_Icc] at hn
          rw [ArithmeticFunction.vonMangoldt_apply_prime hn.2.1]
          have h1 : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).1 hn.1.2
          have h0 : (0 : ℝ) < n := by exact_mod_cast hn.1.1
          exact Real.log_le_log h0 h1
      _ = Real.log x * ((primesAP m a x).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · refine le_trans ?_ (Chebyshev.psi_sub_theta_le hx)
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1.1, hn.1.1.2⟩, hn.2⟩
end Formalism.HermitianLattices.Ext.SupplyAP
