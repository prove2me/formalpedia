-- Prove2me | solution 1 for ConformalizedQuantileRegression.empQuantile_eq_orderStat
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T15:16:37.2865+00:00
-- url     : https://prove2.me/submissions/8d4d2655-1983-4e2c-9249-c8869b1b82f4

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory
namespace ConformalizedQuantileRegression


theorem empQuantile_eq_orderStat {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    empQuantile Finset.univ z α = (orderStat Finset.univ z ⌈α * n⌉₊ : EReal) := by
  classical
  set σ := Tuple.sort z with hσ
  set w : Fin n → ℝ := z ∘ σ with hw
  have hmono : Monotone w := Tuple.monotone_sort z
  have hL : (Finset.univ.val.map z).sort (· ≤ ·) = List.ofFn w := by
    have hp : List.Perm ((Finset.univ.val.map z).sort (· ≤ ·)) (List.ofFn w) := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_val_map]
      exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm z).symm
    exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _) hmono.sortedLE_ofFn.pairwise
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hαn : 0 < α * n := mul_pos hα0 hnpos
  set k := ⌈α * n⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hαn).ne'
  have hkn : k ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hup : (k:ℝ) < α * n + 1 := Nat.ceil_lt_add_one hαn.le
  have hge : α * n ≤ k := Nat.le_ceil _
  set m : Fin n := ⟨k - 1, by omega⟩ with hm
  have hq : orderStat Finset.univ z k = w m := by
    simp only [orderStat, hL]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [m, show k - 1 < n by omega]
  have hcnt : ∀ y, (Finset.univ.filter fun i => z i ≤ y).card
      = (Finset.univ.filter fun j => w j ≤ y).card := by
    intro y
    rw [Finset.card_filter, Finset.card_filter]
    exact (Equiv.sum_comp σ (fun i => if z i ≤ y then 1 else 0)).symm
  have hcdf : ∀ y, empCDF Finset.univ z y = ((Finset.univ.filter fun j => w j ≤ y).card : ℝ) / n := by
    intro y
    unfold empCDF
    rw [hcnt, Finset.card_univ, Fintype.card_fin]
  rw [hq]
  unfold empQuantile
  apply le_antisymm
  · refine iInf₂_le (w m) ?_
    rw [hcdf, le_div_iff₀ hnpos]
    have h1 : k ≤ (Finset.univ.filter fun j => w j ≤ w m).card := by
      calc k = (Finset.Iic m).card := by simp [m]; omega
        _ ≤ _ := Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_Iic] at hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hmono hj)
    have h2 : (k:ℝ) ≤ ((Finset.univ.filter fun j => w j ≤ w m).card : ℝ) := by exact_mod_cast h1
    linarith
  · refine le_iInf₂ fun y hy => ?_
    rw [EReal.coe_le_coe_iff]
    by_contra hlt
    push_neg at hlt
    rw [hcdf, le_div_iff₀ hnpos] at hy
    have h1 : (Finset.univ.filter fun j => w j ≤ y).card ≤ k - 1 := by
      calc _ ≤ (Finset.Iio m).card := Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              simp only [Finset.mem_Iio]
              by_contra hc
              push_neg at hc
              have := hmono hc
              linarith)
        _ = k - 1 := by simp [m]
    have h2 : ((Finset.univ.filter fun j => w j ≤ y).card : ℝ) ≤ (k:ℝ) - 1 := by
      rw [← Nat.cast_one, ← Nat.cast_sub hk1]
      exact_mod_cast h1
    linarith


end ConformalizedQuantileRegression

open ConformalizedQuantileRegression in
theorem solution {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    empQuantile Finset.univ z α = (orderStat Finset.univ z ⌈α * n⌉₊ : EReal) := by
  classical
  set σ := Tuple.sort z with hσ
  set w : Fin n → ℝ := z ∘ σ with hw
  have hmono : Monotone w := Tuple.monotone_sort z
  have hL : (Finset.univ.val.map z).sort (· ≤ ·) = List.ofFn w := by
    have hp : List.Perm ((Finset.univ.val.map z).sort (· ≤ ·)) (List.ofFn w) := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_val_map]
      exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm z).symm
    exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _) hmono.sortedLE_ofFn.pairwise
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hαn : 0 < α * n := mul_pos hα0 hnpos
  set k := ⌈α * n⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hαn).ne'
  have hkn : k ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hup : (k:ℝ) < α * n + 1 := Nat.ceil_lt_add_one hαn.le
  have hge : α * n ≤ k := Nat.le_ceil _
  set m : Fin n := ⟨k - 1, by omega⟩ with hm
  have hq : orderStat Finset.univ z k = w m := by
    simp only [orderStat, hL]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [m, show k - 1 < n by omega]
  have hcnt : ∀ y, (Finset.univ.filter fun i => z i ≤ y).card
      = (Finset.univ.filter fun j => w j ≤ y).card := by
    intro y
    rw [Finset.card_filter, Finset.card_filter]
    exact (Equiv.sum_comp σ (fun i => if z i ≤ y then 1 else 0)).symm
  have hcdf : ∀ y, empCDF Finset.univ z y = ((Finset.univ.filter fun j => w j ≤ y).card : ℝ) / n := by
    intro y
    unfold empCDF
    rw [hcnt, Finset.card_univ, Fintype.card_fin]
  rw [hq]
  unfold empQuantile
  apply le_antisymm
  · refine iInf₂_le (w m) ?_
    rw [hcdf, le_div_iff₀ hnpos]
    have h1 : k ≤ (Finset.univ.filter fun j => w j ≤ w m).card := by
      calc k = (Finset.Iic m).card := by simp [m]; omega
        _ ≤ _ := Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_Iic] at hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hmono hj)
    have h2 : (k:ℝ) ≤ ((Finset.univ.filter fun j => w j ≤ w m).card : ℝ) := by exact_mod_cast h1
    linarith
  · refine le_iInf₂ fun y hy => ?_
    rw [EReal.coe_le_coe_iff]
    by_contra hlt
    push_neg at hlt
    rw [hcdf, le_div_iff₀ hnpos] at hy
    have h1 : (Finset.univ.filter fun j => w j ≤ y).card ≤ k - 1 := by
      calc _ ≤ (Finset.Iio m).card := Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              simp only [Finset.mem_Iio]
              by_contra hc
              push_neg at hc
              have := hmono hc
              linarith)
        _ = k - 1 := by simp [m]
    have h2 : ((Finset.univ.filter fun j => w j ≤ y).card : ℝ) ≤ (k:ℝ) - 1 := by
      rw [← Nat.cast_one, ← Nat.cast_sub hk1]
      exact_mod_cast h1
    linarith

