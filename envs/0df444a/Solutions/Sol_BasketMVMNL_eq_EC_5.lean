-- Prove2me | solution 1 for BasketMVMNL.eq_EC_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:19:14.841344+00:00
-- url     : https://prove2.me/submissions/cd228bf5-3234-469d-8fbf-5b76a5333ae5

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace Aux_Basket_EC5
open BasketMVMNL Finset

theorem mexp_spec (ε' g : ℝ) (hε : 0 < ε') (hg : 1 ≤ g) :
    1 ≤ mexp ε' g ∧ g ≤ (1 + ε') ^ mexp ε' g ∧ (1 + ε') ^ mexp ε' g ≤ (1 + ε') * g := by
  classical
  have hex : ∃ m : ℕ, 1 ≤ m ∧ g ≤ (1 + ε') ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt g (by linarith : (1 : ℝ) < 1 + ε')
    refine ⟨m + 1, by omega, ?_⟩
    calc g ≤ (1 + ε') ^ m := hm.le
      _ ≤ (1 + ε') ^ (m + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hdef : mexp ε' g = Nat.find hex := by
    unfold mexp; rw [dif_pos hex]
  rw [hdef]
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  refine ⟨h1, h2, ?_⟩
  by_cases hm : Nat.find hex = 1
  · rw [hm, pow_one]; nlinarith
  · have hm2 : 2 ≤ Nat.find hex := by omega
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push_neg at hmin
    have hlt := hmin (by omega)
    have : (1 + ε') ^ Nat.find hex = (1 + ε') * (1 + ε') ^ (Nat.find hex - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    nlinarith

end Aux_Basket_EC5

open BasketMVMNL Finset Aux_Basket_EC5 in
theorem solution {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (ε' : ℝ) (hε' : 0 < ε') (x : Assortment J I) (j : Fin J) :
    Rbarj ε' P x j / (1 + ε') ^ (J - 1) ≤ Rj P x j ∧ Rj P x j ≤ Rbarj ε' P x j * (1 + ε') ^ J := by
  have hbit : ∀ b, 0 ≤ bit b := fun b => by unfold bit; split_ifs <;> norm_num
  have hγ1 : ∀ k, 1 ≤ γ P x k := fun k => by
    unfold γ
    have : 0 ≤ ∑ i, P.v k i * bit (x k i) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hP.v_pos k i).le (hbit _))
    linarith
  have hspec := fun k => mexp_spec ε' (γ P x k) hε' (hγ1 k)
  have hlo : ∀ k, γ P x k ≤ γbar ε' P x k := fun k => (hspec k).2.1
  have hhi : ∀ k, γbar ε' P x k ≤ (1 + ε') * γ P x k := fun k => (hspec k).2.2
  have hγpos : ∀ k, 0 < γ P x k := fun k => by linarith [hγ1 k]
  have hγbpos : ∀ k, 0 < γbar ε' P x k := fun k => lt_of_lt_of_le (hγpos k) (hlo k)
  have hΛ : 0 ≤ Λ P x j := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hP.r_nonneg j i) (hP.v_pos j i).le) (hbit _))
  set Pa := ∏ k ∈ univ.erase j, γ P x k with hPa
  set Pb := ∏ k ∈ univ.erase j, γbar ε' P x k with hPb
  have hPapos : 0 < Pa := Finset.prod_pos (fun k _ => hγpos k)
  have hPbpos : 0 < Pb := Finset.prod_pos (fun k _ => hγbpos k)
  have hPle : Pa ≤ Pb := Finset.prod_le_prod (fun k _ => (hγpos k).le) (fun k _ => hlo k)
  have hcard : (univ.erase j).card = J - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have hPhi2 : Pb ≤ (1 + ε') ^ (J - 1) * Pa := by
    calc Pb ≤ ∏ k ∈ univ.erase j, ((1 + ε') * γ P x k) :=
          Finset.prod_le_prod (fun k _ => (hγbpos k).le) (fun k _ => hhi k)
      _ = (1 + ε') ^ (J - 1) * Pa := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hΓ : Γ P x = γ P x j * Pa := (Finset.mul_prod_erase univ _ (mem_univ j)).symm
  have hΓb : Γbar ε' P x = γbar ε' P x j * Pb := (Finset.mul_prod_erase univ _ (mem_univ j)).symm
  have hv0 : 0 < P.v0 - 1 := by linarith [hP.one_lt_v0]
  have hD : ((P.v0 - 1) / Γ P x + 1) * γ P x j = (P.v0 - 1) / Pa + γ P x j := by
    rw [hΓ]
    have h1 := (hγpos j).ne'
    have h2 := hPapos.ne'
    first | (field_simp; done) | (field_simp; ring)
  have hDb : ((P.v0 - 1) / Γbar ε' P x + 1) * γbar ε' P x j = (P.v0 - 1) / Pb + γbar ε' P x j := by
    rw [hΓb]
    have h1 := (hγbpos j).ne'
    have h2 := hPbpos.ne'
    first | (field_simp; done) | (field_simp; ring)
  have hRj : Rj P x j = Λ P x j / ((P.v0 - 1) / Pa + γ P x j) := by unfold Rj; rw [hD]
  have hRb : Rbarj ε' P x j = Λ P x j / ((P.v0 - 1) / Pb + γbar ε' P x j) := by unfold Rbarj; rw [hDb]
  have hq1 : (1 : ℝ) ≤ 1 + ε' := by linarith
  have hpJ1 : (1 : ℝ) ≤ (1 + ε') ^ (J - 1) := one_le_pow₀ hq1
  have hJ : (1 + ε') ^ J = (1 + ε') * (1 + ε') ^ (J - 1) := by
    rw [← pow_succ']; congr 1; have := hP.one_le_J; omega
  have hpJ : (1 : ℝ) ≤ (1 + ε') ^ J := one_le_pow₀ hq1
  set D := (P.v0 - 1) / Pa + γ P x j with hDdef
  set Db := (P.v0 - 1) / Pb + γbar ε' P x j with hDbdef
  have hDpos : 0 < D := add_pos (div_pos hv0 hPapos) (hγpos j)
  have hDbpos : 0 < Db := add_pos (div_pos hv0 hPbpos) (hγbpos j)
  -- D ≤ q^(J-1) Db and Db ≤ q^J D
  have hA : (P.v0 - 1) / Pa ≤ (1 + ε') ^ (J - 1) * ((P.v0 - 1) / Pb) := by
    rw [mul_div_assoc', div_le_div_iff₀ hPapos hPbpos]
    nlinarith [mul_le_mul_of_nonneg_left hPhi2 hv0.le]
  have hDle : D ≤ (1 + ε') ^ (J - 1) * Db := by
    have h3 : γ P x j ≤ (1 + ε') ^ (J - 1) * γbar ε' P x j := by
      nlinarith [hlo j, hγbpos j, hpJ1]
    calc D = (P.v0 - 1) / Pa + γ P x j := hDdef
      _ ≤ (1 + ε') ^ (J - 1) * ((P.v0 - 1) / Pb) + (1 + ε') ^ (J - 1) * γbar ε' P x j :=
          add_le_add hA h3
      _ = (1 + ε') ^ (J - 1) * Db := by rw [hDbdef]; ring
  have hB : (P.v0 - 1) / Pb ≤ (P.v0 - 1) / Pa := div_le_div_of_nonneg_left hv0.le hPapos hPle
  have hDble : Db ≤ (1 + ε') ^ J * D := by
    have h1 : (P.v0 - 1) / Pa ≤ (1 + ε') ^ J * ((P.v0 - 1) / Pa) :=
      le_mul_of_one_le_left (div_pos hv0 hPapos).le hpJ
    have h2 : γbar ε' P x j ≤ (1 + ε') ^ J * γ P x j := by
      have hm := mul_le_mul_of_nonneg_left hpJ1
        (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + ε') (hγpos j).le)
      rw [hJ]
      calc γbar ε' P x j ≤ (1 + ε') * γ P x j := hhi j
        _ = (1 + ε') * γ P x j * 1 := by ring
        _ ≤ (1 + ε') * γ P x j * (1 + ε') ^ (J - 1) := hm
        _ = (1 + ε') * (1 + ε') ^ (J - 1) * γ P x j := by ring
    calc Db = (P.v0 - 1) / Pb + γbar ε' P x j := hDbdef
      _ ≤ (1 + ε') ^ J * ((P.v0 - 1) / Pa) + (1 + ε') ^ J * γ P x j := add_le_add (hB.trans h1) h2
      _ = (1 + ε') ^ J * D := by rw [hDdef]; ring
  rw [hRj, hRb]
  constructor
  · rw [div_div, div_le_div_iff₀ (by positivity) hDpos]
    nlinarith [mul_le_mul_of_nonneg_left hDle hΛ]
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ hDpos hDbpos]
    nlinarith [mul_le_mul_of_nonneg_left hDble hΛ]
