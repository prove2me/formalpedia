-- Prove2me | solution 1 for DerivativeChainContinuation.tower_holomorphic_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:37:34.427682+00:00
-- url     : https://prove2.me/submissions/5c650327-bdbe-4391-9bd8-f0706b9673ec

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_derivative_centered_second_moment
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial





theorem monicDerivative_natDegree (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (monicDerivative p).natDegree = p.natDegree - 1 := by
  rw [monicDerivative, natDegree_C_mul (inv_ne_zero (by exact_mod_cast hn)),
    natDegree_derivative]






end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial









theorem derivative_holomorphic_rescaling (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    rootHolomorphicMoment (monicDerivative p) / (n+1 : ℂ) =
      rootHolomorphicMoment p / (n+2 : ℂ) := by
  have hn : p.natDegree ≠ 0 := by omega
  have hqd : (monicDerivative p).natDegree = n+2 := by
    rw [monicDerivative_natDegree p hn, hdeg]; omega
  have h := derivative_centered_second_moment p hp n hdeg hcenter
  have h1 : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  have h2 : (n+2 : ℂ) ≠ 0 := by exact_mod_cast (show n+2 ≠ 0 by omega)
  have h3 : (n+3 : ℂ) ≠ 0 := by exact_mod_cast (show n+3 ≠ 0 by omega)
  simp only [rootHolomorphicMoment, hqd, hdeg, Nat.cast_add, Nat.cast_ofNat]
  field_simp
  linear_combination h




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (P : ℕ → Polynomial ℂ) (n : ℕ)
    (hmonic : ∀ k ≤ n, (P (k+2)).Monic)
    (hdegree : ∀ k ≤ n, (P (k+2)).natDegree = k+2)
    (hcenter : ∀ k ≤ n, (P (k+2)).roots.sum = 0)
    (hstep : ∀ k < n, monicDerivative (P (k+3)) = P (k+2)) :
    rootHolomorphicMoment (P 2) = rootHolomorphicMoment (P (n+2))/(n+1 : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun k hk => hmonic k (by omega))
      (fun k hk => hdegree k (by omega)) (fun k hk => hcenter k (by omega))
      (fun k hk => hstep k (by omega))
    have hs := derivative_holomorphic_rescaling (P (n+3))
      (hmonic (n+1) (by omega)) n (hdegree (n+1) (by omega))
      (hcenter (n+1) (by omega))
    rw [hstep n (by omega)] at hs
    convert hi.trans hs using 1 <;>
      simp [Nat.succ_eq_add_one, Nat.add_assoc, add_assoc] <;> norm_num
