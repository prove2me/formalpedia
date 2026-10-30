-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_triple_normalization_parameters
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:59:46.298641+00:00
-- url     : https://prove2.me/submissions/e5e12267-a200-4b04-b139-1f0933de243e

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (u v w : ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    ∃ c β : ℂ, c ≠ 0 ∧ 0 ≤ β.re ∧
      ((X-C u)*(X-C v)*(X-C w)).comp (C ((u+v+w)/3)+C c*X) =
        C (c^3)*(X^3-C (a:ℂ)*X-C ((b:ℂ)*β)) := by
  let η := (u+v+w)/3
  let A := (u^2+v^2+w^2-u*v-u*w-v*w)/3
  let B := (u-η)*(v-η)*(w-η)
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdepress (t : ℂ) : (η+t-u)*(η+t-v)*(η+t-w)=t^3-A*t-B := by dsimp [η,A,B]; ring
  obtain ⟨c,hc2⟩ := IsAlgClosed.exists_pow_nat_eq (A/(a:ℂ)) (show 0 < 2 by norm_num)
  have hAc : A=(a:ℂ)*c^2 := by rw [hc2]; field_simp
  have hc : c ≠ 0 := by
    intro he
    apply hA
    change A=0
    simpa [he] using hAc
  have hcomp (c : ℂ) (hc : c ≠ 0) (hc2 : c^2=A/(a:ℂ)) :
      ((X-C u)*(X-C v)*(X-C w)).comp (C η+C c*X) =
        C (c^3)*(X^3-C (a:ℂ)*X-C ((b:ℂ)*(B/((b:ℂ)*c^3)))) := by
    have hAc : A=(a:ℂ)*c^2 := by rw [hc2]; field_simp
    apply Polynomial.funext
    intro z
    simp only [eval_comp,eval_mul,eval_C,eval_add,eval_X,eval_sub,eval_pow,eval_ofNat]
    rw [hdepress (c*z),hAc]
    field_simp
  by_cases hβ : 0 ≤ (B/((b:ℂ)*c^3)).re
  · exact ⟨c,B/((b:ℂ)*c^3),hc,hβ,hcomp c hc hc2⟩
  · have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
    have hc2' : (-c)^2=A/(a:ℂ) := by simpa only [neg_sq] using hc2
    have hneg : B/((b:ℂ)*(-c)^3)=-(B/((b:ℂ)*c^3)) := by
      rw [show (-c)^3=-(c^3) by ring,mul_neg,div_neg]
    refine ⟨-c,B/((b:ℂ)*(-c)^3),hc',?_,hcomp (-c) hc' hc2'⟩
    rw [hneg,Complex.neg_re]
    linarith
