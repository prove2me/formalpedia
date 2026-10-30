-- Prove2me | solution 1 for DerivativeChainPrivate.affine_orthonormal_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:56:54.752258+00:00
-- url     : https://prove2.me/submissions/212f4489-8821-452d-a9ee-a30ccd10115a

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution {n : ℕ} (z : Fin n → ℂ) (a b t c : ℂ)
    (hc : c ≠ 0) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : (a*starRingEnd ℂ b).re = 0)
    (hmonoA : Monotone (fun i => (a*z i).re))
    (hmonoB : Monotone (fun i => (b*z i).re)) :
    ∃ A B : ℂ, ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*(t+c*z i)).re) ∧ Monotone (fun i => (B*(t+c*z i)).re) := by
  let d := starRingEnd ℂ c/(‖c‖ : ℂ)
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcast : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcn.ne'
  have hdn : ‖d‖ = 1 := by
    dsimp only [d]
    rw [norm_div,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hcn,div_self hcn.ne']
  have hdc : d*c = (‖c‖ : ℂ) := by
    dsimp only [d]
    rw [div_mul_eq_mul_div,mul_comm (starRingEnd ℂ c) c,Complex.mul_conj,←Complex.sq_norm,Complex.ofReal_pow]
    field_simp
  have hdd : d*starRingEnd ℂ d = 1 := by
    rw [Complex.mul_conj,←Complex.sq_norm,hdn]
    norm_num
  have horth : ((a*d)*starRingEnd ℂ (b*d)).re = 0 := by
    have heq : (a*d)*starRingEnd ℂ (b*d) = (a*starRingEnd ℂ b)*(d*starRingEnd ℂ d) := by
      rw [map_mul]
      ring
    rw [heq,hdd,mul_one]
    exact hab
  have hcoord (u : ℂ) (i : Fin n) : ((u*d)*(t+c*z i)).re =
      ((u*d)*t).re+‖c‖*(u*z i).re := by
    have heq : (u*d)*(t+c*z i) = (u*d)*t+(‖c‖ : ℂ)*(u*z i) := by
      calc
        _ = (u*d)*t+(d*c)*(u*z i) := by ring
        _ = _ := by rw [hdc]
    rw [heq]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨a*d,b*d,by simp only [norm_mul,ha,hdn,mul_one],
    by simp only [norm_mul,hb,hdn,mul_one],horth,?_,?_⟩
  · intro i j hij
    change (a*d*(t+c*z i)).re ≤ (a*d*(t+c*z j)).re
    rw [hcoord,hcoord]
    have h := mul_le_mul_of_nonneg_left (hmonoA hij) hcn.le
    linarith only [h]
  · intro i j hij
    change (b*d*(t+c*z i)).re ≤ (b*d*(t+c*z j)).re
    rw [hcoord,hcoord]
    have h := mul_le_mul_of_nonneg_left (hmonoB hij) hcn.le
    linarith only [h]
