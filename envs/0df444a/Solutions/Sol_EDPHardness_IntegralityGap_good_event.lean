-- Prove2me | solution 1 for EDPHardness.IntegralityGap.good_event
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:55:16.637421+00:00
-- url     : https://prove2.me/submissions/d80294cc-f732-4fe7-85ad-988acd875ec8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

import Theorems.Thm_EDPHardness_IntegralityGap_lemma_6
import Theorems.Thm_EDPHardness_IntegralityGap_lemma_7
import Theorems.Thm_EDPHardness_IntegralityGap_lemma_8
open EDPHardness.IntegralityGap Filter

lemma edp_eventually_L :
    ∀ᶠ n : ℕ in atTop, 16 ≤ Real.logb 2 n ∧
      600 * (Real.log (Real.logb 2 n)) ^ 2 ≤ (Real.logb 2 n) ^ ((1:ℝ)/2) := by
  have hT : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ x : ℝ in atTop, 600 * (Real.log x) ^ 2 ≤ x ^ ((1:ℝ)/2) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ) < 1/2)).bound
      (by norm_num : (0:ℝ) < 1/600)
    filter_upwards [ho, eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)] at hx
    have : Real.log x ^ (2:ℝ) = Real.log x ^ 2 := by norm_cast
    rw [this] at hx
    linarith
  exact (hT.eventually (h1.and (eventually_ge_atTop 16))).mono fun n h => ⟨h.2, h.1⟩

lemma edp_params_of_L (n c : ℕ) (hL : 16 ≤ Real.logb 2 n)
    (hL2 : 600 * (Real.log (Real.logb 2 n)) ^ 2 ≤ (Real.logb 2 n) ^ ((1:ℝ)/2))
    (hc : 2 ≤ c)
    (hcα : (c : ℝ) ≤ (1/6) * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n))) :
    2 ≤ beta1 n c ∧ c ≤ n ∧ 1 ≤ Real.logb 2 (Real.logb 2 (Real.logb 2 n)) := by
  set L := Real.logb 2 n with hLdef
  set l := Real.logb 2 L with hldef
  have hL0 : 0 < L := by linarith
  have hl4 : 4 ≤ l := by
    rw [hldef, Real.le_logb_iff_rpow_le (by norm_num) hL0]; norm_num; linarith
  have hl3 : 1 ≤ Real.logb 2 l := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; linarith
  have hlog2 : (1:ℝ)/2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2' : 0 < Real.log 2 := by linarith
  -- c ≤ l / 6
  have hcl : (c : ℝ) ≤ l / 6 := by
    have : (1/6) * l / Real.logb 2 l ≤ l / 6 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  -- bound on l ≤ 2 L
  have hlogle : ∀ x : ℝ, 0 < x → Real.logb 2 x ≤ 2 * x := by
    intro x hx
    rw [Real.logb, div_le_iff₀ hlog2']
    have := Real.log_le_sub_one_of_pos hx
    nlinarith
  have hLn : L ≤ 2 * n := by
    have hn : (0:ℝ) < n := by
      by_contra h
      push Not at h
      have : (n:ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
      rw [hLdef, this] at hL; simp at hL; linarith
    exact hlogle _ hn
  have hcn : c ≤ n := by
    have h1 := hlogle L hL0
    have : (c:ℝ) ≤ n := by linarith
    exact_mod_cast this
  refine ⟨?_, hcn, hl3⟩
  -- β₁ ≥ 2
  have hcpos : (0:ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hX : (8:ℝ) ^ (c:ℝ) ≤ L / (150 * l ^ 2) := by
    -- 8^c = 2^(3c) ≤ 2^(l/2) = L^(1/2)
    have h8 : (8:ℝ) ^ (c:ℝ) = (2:ℝ) ^ (3 * (c:ℝ)) := by
      rw [Real.rpow_mul (by norm_num)]; norm_num
    have h2 : (2:ℝ) ^ (3 * (c:ℝ)) ≤ (2:ℝ) ^ (l / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2:ℝ) ^ (l / 2) = L ^ ((1:ℝ)/2) := by
      rw [hldef, div_eq_mul_one_div, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num)
        (by norm_num) hL0]
    have hsq : l ^ 2 ≤ 4 * (Real.log L) ^ 2 := by
      have : l = Real.log L / Real.log 2 := rfl
      rw [this, div_pow, div_le_iff₀ (by positivity)]
      have hlL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      have h4 : 1 ≤ 4 * Real.log 2 ^ 2 := by nlinarith
      nlinarith [sq_nonneg (Real.log L)]
    have hsqrt : L ^ ((1:ℝ)/2) * L ^ ((1:ℝ)/2) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    have hs0 : 0 < L ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hL0 _
    rw [le_div_iff₀ (by nlinarith), h8]
    calc (2:ℝ) ^ (3 * (c:ℝ)) * (150 * l ^ 2) ≤ L ^ ((1:ℝ)/2) * (150 * (4 * (Real.log L) ^ 2)) := by
          apply mul_le_mul (h2.trans h3.le) (by nlinarith) (by positivity) hs0.le
      _ ≤ L ^ ((1:ℝ)/2) * L ^ ((1:ℝ)/2) := by
          apply mul_le_mul_of_nonneg_left _ hs0.le; nlinarith
      _ = L := hsqrt
  have hX0 : 0 ≤ L / (150 * l ^ 2) := by positivity
  have : (8:ℝ) ≤ (L / (150 * l ^ 2)) ^ ((1:ℝ) / c) := by
    calc (8:ℝ) = ((8:ℝ) ^ (c:ℝ)) ^ ((1:ℝ)/c) := by
          rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hcpos.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hX (by positivity)
  unfold beta1
  rw [← hLdef, ← hldef]
  linarith

lemma edp_beta2_ge (n c : ℕ) (hc : 2 ≤ c) (h : 2 ≤ beta1 n c) : 1 ≤ beta2 n c := by
  unfold beta2
  have h1 : (1:ℝ) ≤ (2 * beta1 n c) ^ (c - 1) := one_le_pow₀ (by linarith)
  have h2 : Real.log 2 ≤ Real.log (beta1 n c) := Real.log_le_log (by norm_num) h
  have := Real.log_two_gt_d9
  nlinarith

lemma edp_gParam_ge (n c : ℕ) (hc : 2 ≤ c) (h : 2 ≤ beta1 n c) : 2 ≤ gParam n c := by
  have hb2 := edp_beta2_ge n c hc h
  have hc' : (2:ℝ) ≤ c := by exact_mod_cast hc
  have hx : (1:ℝ) < 3 * beta1 n c * beta2 n c * (c:ℝ) ^ 2 := by
    have : (4:ℝ) ≤ (c:ℝ)^2 := by nlinarith
    have : (2:ℝ) ≤ beta1 n c * beta2 n c := by nlinarith
    nlinarith
  have := Nat.le_ceil (3 * beta1 n c * beta2 n c * (c:ℝ) ^ 2)
  unfold gParam
  have : (1:ℝ) < (⌈3 * beta1 n c * beta2 n c * (c:ℝ) ^ 2⌉₊ : ℝ) := lt_of_lt_of_le hx this
  have : 1 < ⌈3 * beta1 n c * beta2 n c * (c:ℝ) ^ 2⌉₊ := by exact_mod_cast this
  omega

theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      1 / 4 ≤ hypProb n (numEdges n c) c
        (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H) := by
  classical
  obtain ⟨α₁, hα₁, N₁, h₁⟩ := lemma_6
  obtain ⟨α₂, hα₂, N₂, h₂⟩ := lemma_7
  obtain ⟨N₃, h₃⟩ := Filter.eventually_atTop.mp edp_eventually_L
  have hα : 0 < min (min α₁ α₂) (1/6 : ℝ) := lt_min (lt_min hα₁ hα₂) (by norm_num)
  refine ⟨min (min α₁ α₂) (1/6), hα, max (max N₁ N₂) N₃, ?_⟩
  intro n hn c hc hcα
  set r := Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) with hr
  have hcα' : (c : ℝ) ≤ min (min α₁ α₂) (1/6) * r := by rw [hr, ← mul_div_assoc]; exact hcα
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr0 : 0 < r := by
    by_contra h
    push Not at h
    have : min (min α₁ α₂) (1/6) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα.le h
    linarith
  have key : ∀ β : ℝ, min (min α₁ α₂) (1/6) ≤ β →
      (c : ℝ) ≤ β * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) := by
    intro β hβ
    rw [mul_div_assoc, ← hr]
    exact hcα'.trans (mul_le_mul_of_nonneg_right hβ hr0.le)
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N₃ ≤ n := le_trans (le_max_right _ _) hn
  have p1 := h₁ n hn1 c hc (key α₁ ((min_le_left _ _).trans (min_le_left _ _)))
  have p2 := h₂ n hn2 c hc (key α₂ ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨hL1, hL2⟩ := h₃ n hn3
  obtain ⟨hb1, hcn, -⟩ := edp_params_of_L n c hL1 hL2 hc (key (1/6) (min_le_right _ _))
  have hb2 := edp_beta2_ge n c hc hb1
  have hg := edp_gParam_ge n c hc hb1
  have p3 := lemma_8 n c hc hcn (by linarith) (2 * gParam n c) (by omega)
  unfold hypProb at p1 p2 p3 ⊢
  set U := Fintype.card (Hyp n (numEdges n c) c)
  have hU : 0 < U := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (by simpa using hcn)
    exact ⟨fun _ => ⟨t, ht⟩⟩
  have hUr : (0:ℝ) < U := by exact_mod_cast hU
  rw [le_div_iff₀ hUr]
  rw [div_le_iff₀ hUr] at p1 p2 p3
  have hsub : (Finset.univ : Finset (Hyp n (numEdges n c) c)) ⊆
      ((Finset.univ.filter (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H)) ∪
        Finset.univ.filter (E1 n c)) ∪ Finset.univ.filter (E2 n c) ∪
        Finset.univ.filter (E3 n c (2 * gParam n c)) := by
    intro H _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hcard := Finset.card_le_card hsub
  have u1 := Finset.card_union_le
    (((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H)) ∪
        (Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E1 n c) ∪ (Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E2 n c))
    ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E3 n c (2 * gParam n c)))
  have u2 := Finset.card_union_le
    (((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H)) ∪
        (Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E1 n c)) ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E2 n c))
  have u3 := Finset.card_union_le
    ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H))
    ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E1 n c))
  rw [Finset.card_univ] at hcard
  have hcard' : (U : ℝ) ≤ (((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter
      (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H)).card : ℝ) +
      ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E1 n c)).card + ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E2 n c)).card +
      ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter (E3 n c (2 * gParam n c))).card := by
    exact_mod_cast (by omega)
  push_cast at hcard'
  have fin : 1 / 4 * (U:ℝ) ≤ ((Finset.univ : Finset (Hyp n (numEdges n c) c)).filter
      (fun H => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H)).card := by linarith
  refine fin.trans (le_of_eq ?_)
  congr 2
  ext H
  simp only [Finset.mem_filter]
