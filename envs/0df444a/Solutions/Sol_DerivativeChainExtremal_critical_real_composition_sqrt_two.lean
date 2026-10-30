-- Prove2me | solution 1 for DerivativeChainExtremal.critical_real_composition_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:18:24.834016+00:00
-- url     : https://prove2.me/submissions/f93a9962-2715-4624-a6b9-a4584eab0ee7

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_real_quotient_critical_row_sqrt_two
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial





theorem spoke_derivative_zero (k : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) 0 q).derivative =
      spokePoly (k + 1) k (C (k + 1 : ℝ) * q.derivative) := by
  simp only [spokePoly, pow_zero, one_mul, derivative_comp, derivative_pow,
    derivative_X, mul_one, Nat.add_sub_cancel, derivative_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.mul_comp, Polynomial.C_comp]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring











end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation

theorem spoke_real_scalar_mul (k r : ℕ) (q : Polynomial ℝ) (t : ℝ) :
    spokePoly k r (C t*q)=C (t:ℂ)*spokePoly k r q := by
  simp only [spokePoly,Polynomial.map_mul,Polynomial.map_C,Polynomial.mul_comp,Polynomial.C_comp,
    Complex.ofRealHom_eq_coe]
  ring





end DerivativeChainExtremal


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation



theorem solution (p : Polynomial ℂ) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hdegree : p.natDegree=n+1)
    (F : Polynomial ℝ) (hF : F.derivative.Splits) (σ A γ o : ℂ) (R : ℝ)
    (hσ : ‖σ‖=1) (hA : A ≠ 0)
    (hform : p.comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C A*(_root_.DerivativeChainPrivate.spokePoly k 0 F+C γ))
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=_root_.DerivativeChainContinuation.rootCentroid p ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt 2*Real.sqrt (R^2-‖_root_.DerivativeChainContinuation.rootCentroid p-o‖^2) := by
  have hσne : σ ≠ 0 := by intro he; simp [he] at hσ
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hd : C σ*p.derivative.comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=
      C (A*(j+1:ℂ))*_root_.DerivativeChainPrivate.spokePoly (j+1) j F.derivative := by
    calc
      _ = derivative (p.comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)) := by
        rw [derivative_comp]
        simp only [derivative_add,derivative_C,derivative_mul,zero_mul,derivative_X,mul_one,zero_add]
      _ = derivative (C A*(_root_.DerivativeChainPrivate.spokePoly (j+1) 0 F+C γ)) := congrArg derivative hform
      _ = _ := by
        rw [derivative_C_mul,derivative_add,derivative_C,add_zero,_root_.DerivativeChainPrivate.spoke_derivative_zero,
          _root_.DerivativeChainExtremal.spoke_real_scalar_mul]
        push_cast
        rw [←mul_assoc,←map_mul]
  let B := (A*(j+1:ℂ))/σ
  have hB : B ≠ 0 := div_ne_zero (mul_ne_zero hA (by exact_mod_cast (show j+1 ≠ 0 by omega))) hσne
  have hscale : C σ*C B=C (A*(j+1:ℂ)) := by
    rw [←map_mul]
    congr 1
    dsimp only [B]
    field_simp
  have hcore : p.derivative.comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C B*_root_.DerivativeChainPrivate.spokePoly (j+1) j F.derivative := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hσne)
    rw [hd,←mul_assoc,hscale]
  exact _root_.DerivativeChainExtremal.real_quotient_critical_row_sqrt_two p n (j+1) j hn hdegree F.derivative σ B o R
    hk (by omega) hF hB hσ hcore hR ha
