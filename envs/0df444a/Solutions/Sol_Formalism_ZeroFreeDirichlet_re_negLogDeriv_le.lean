-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.re_negLogDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:47.027453+00:00
-- url     : https://prove2.me/submissions/0d6a6354-d44d-4cc0-91bd-85cb5a01bab6

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_EulerFactorLogDerivBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_euler_factor_logDeriv_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (negLD (1 : DirichletCharacter ℂ q) s).re ≤
      (-(deriv riemannZeta s / riemannZeta s)).re + Real.log q := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hfac : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
      ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p :=
    fun p hp => euler_factor_logDeriv_bound p (Nat.prime_of_mem_primeFactors hp) s hs
  have heq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q)
      (Set.mem_compl_singleton_iff.mp hz)
  have hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hfac p hp).1
  have hPd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd fun p hp => (hfac p hp).2.1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hmul : logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s =
      logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s +
        logDeriv riemannZeta s :=
    logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)))
      (g := riemannZeta) s hPne hζ hPd hζd
  have hprod : logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s =
      ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z))
      (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2.1)
  have hneg : negLD (1 : DirichletCharacter ℂ q) s =
      -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s) := rfl
  have hS : ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤
      Real.log q := by
    calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := Finset.sum_le_sum fun p hp => (hfac p hp).2.2
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log q := by
          apply Real.log_le_log
          · exact Finset.prod_pos fun p hp => by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
  have hre := RCLike.abs_re_le_norm
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s)
  have hre' := neg_abs_le
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s).re
  rw [hneg, (logDeriv_congr_nhds heq).eq_of_nhds, hmul, hprod, logDeriv_apply]
  simp only [Complex.neg_re, Complex.add_re]
  simp only [RCLike.re_to_complex] at hre
  linarith
end Formalism.ZeroFreeDirichlet
