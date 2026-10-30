-- Prove2me | solution 1 for DerivativeChainPrefixLaws.linear_row_root_eq_centroid
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:17:13.509981+00:00
-- url     : https://prove2.me/submissions/e9a169f0-f18a-4ec1-9878-ec4a91e6474a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
import Theorems.Thm_DerivativeChainPrefixLaws_uniform_step_centroid
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
noncomputable section



theorem uniform_row_centroid (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n, UniformPolynomialStep r k) (h : ℕ) (hh : h ≤ n) :
    complexCentroid (r h)=r 0 0 := by
  induction h with
  | zero => simp [complexCentroid]
  | succ h ih =>
    rw [uniform_step_centroid r h (hstep h (by omega)),ih (by omega)]













end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainPrefixLaws








theorem solution {n : ℕ} (a : Fin (n+1) → ℂ) (v : ℂ)
    (hv : (_root_.DerivativeChainPrivate.row a 1).eval v=0) : v=_root_.DerivativeChainContinuation.complexCentroid a := by
  obtain ⟨r,htop,hstep⟩ := _root_.DerivativeChainContinuation.uniform_polynomial_tower n a
  obtain ⟨c,hc,he⟩ := _root_.DerivativeChainContinuation.complex_tower_factor r n hstep 0 (by omega)
  have hp : _root_.DerivativeChainContinuation.complexRowProduct r n=_root_.DerivativeChainPrivate.fromRoots a := by
    simp only [_root_.DerivativeChainContinuation.complexRowProduct,htop,_root_.DerivativeChainPrivate.fromRoots]
  rw [hp,Nat.sub_zero] at he
  change ((derivative^[n+1-1]) (_root_.DerivativeChainPrivate.fromRoots a)).eval v=0 at hv
  rw [show n+1-1=n by omega,he,eval_mul,eval_C] at hv
  have hz : (_root_.DerivativeChainContinuation.complexRowProduct r 0).eval v=0 := (mul_eq_zero.mp hv).resolve_left hc
  have hv' : v=r 0 0 := by simpa [_root_.DerivativeChainContinuation.complexRowProduct,sub_eq_zero] using hz
  have hm := _root_.DerivativeChainPrefixLaws.uniform_row_centroid r n hstep n le_rfl
  rw [htop] at hm
  exact hv'.trans hm.symm
