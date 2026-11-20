-- Prove2me | solution 1 for BooleanFun.BV._eq_noise_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:32.191826+00:00
-- url     : https://prove2.me/submissions/16f8be15-1f29-4ea7-b42e-4e256585a78f

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
import Theorems.Thm_BooleanFun_ite_add_ite
import Theorems.Thm_BooleanFun_ite_ite_same
import Theorems.Thm_BooleanFun_multiplier_walsh
import Theorems.Thm_BooleanFun_oneOn_false
import Theorems.Thm_BooleanFun_oneOn_prod
import Theorems.Thm_BooleanFun_oneOn_true
import Theorems.Thm_BooleanFun_walsh_def
import Theorems.Thm_P2M_BooleanFun_ite_ite_not__7b24d63f550e

section
noncomputable section
namespace BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
private lemma filter_univ_not_mem {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    univ.filter (· ∉ s) = sᶜ := by
  ext
  simp only [mem_filter, mem_univ, true_and, mem_compl]
local notation "T" => _Tnae3
end BooleanFun.BV
end
end

set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
local notation "T" => _Tnae3
namespace BooleanFun.BV
theorem _root_.solution : T = @noise_operator n (-1/3) := by
  apply Module.Basis.ext (b := walsh_basis)
  intro S
  rw [walsh_basis, noise_operator, coe_basisOfOrthonormalOfCardEqFinrank,
    LinearMap.coe_mk, AddHom.coe_mk, multiplier_walsh]
  funext x
  rw [Pi.smul_apply, smul_eq_mul]
  have : ∀ y : Fin n → Fin 2, ∑ z : Fin n → Fin 2, oneOn (VoteConsistent x y z)
      =  ∏ i, (1 + oneOn (x i ≠ y i)) := by
    intro y
    unfold VoteConsistent
    simp_rw [← oneOn_prod]
    rw [← Fintype.prod_sum (f := fun i => fun v => oneOn (NAE3 (x i) (y i) v))]
    suffices ∀ i, ∑ v : Fin 2, oneOn (NAE3 (x i) (y i) v) = (1 + oneOn (x i ≠ y i)) by simp_rw [this]
    intro i
    by_cases h : x i = y i
    · simp [h]
      induction y i using Fin.cases with
      | zero => simp
      | succ k => simp [Fin.fin_one_eq_zero]
    · simp [h]; norm_num
  conv => enter [1, 2, 2, y]; rw [this, walshCharacter.eq_def]
          enter [1, 1]; rw [← filter_univ_mem (s := S)]
  conv => enter [1, 2, 2, y]; rw [prod_filter, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun i ↦ fun v ↦ (if i ∈ S then (-1)^v.val else 1) * (1 + oneOn (x i ≠ v)))]
  have haux (w : Fin 2) (g : Fin 2 → ℝ) : ∑ v : Fin 2, g v = g w + g (1-w) := by
    induction w using Fin.cases with -- TODO : tactic macro?
    | zero => simp
    | succ k => simp [Fin.fin_one_eq_zero k]; exact add_comm _ _
  conv => enter [1, 2, 2, i]; rw [haux (x i), oneOn_false (by simp)]
          rw [oneOn_true (by omega), add_zero, mul_one]
  rw [← prod_filter_mul_prod_filter_not (p := fun i ↦ i ∈ S), prod_filter, prod_filter]
  have haux2 (v : Fin 2) : ((-1) : ℝ)^v.val + (-1)^(1-v).val * (1 + 1) = (-1) * (-1)^v.val := by
    induction v using Fin.cases with
    | zero => simp
    | succ k => simp [Fin.fin_one_eq_zero k]
  conv => enter [1, 2, 1, 2, i]; rw [ite_mul, ite_add_ite, ite_ite_same, haux2]
  rw [← prod_filter, filter_univ_mem, prod_mul_distrib, prod_const, ← walsh_def]
  conv => enter [1, 2, 2, 2, i]; rw [ite_mul, ite_add_ite, ite_ite_not']; arg 2; norm_num
  rw [← prod_filter, prod_const, filter_univ_not_mem, card_compl, Fintype.card_fin]
  rw [pow_sub₀ _ (by simp) (card_finset_fin_le _)]
  field_simp -- todo : speedup
  have hpow : (1 / 3 : ℝ) ^ n * 3 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (1 / 3 : ℝ) ^ n * (-1) ^ S.card * 3 ^ n =
        ((1 / 3 : ℝ) ^ n * 3 ^ n) * (-1) ^ S.card := by ring
    _ = (-1) ^ S.card := by rw [hpow]; ring
    _ = (3 * (-(1 / 3 : ℝ))) ^ S.card := by norm_num
    _ = 3 ^ S.card * (-(1 / 3 : ℝ)) ^ S.card := by rw [mul_pow]
end BooleanFun.BV
