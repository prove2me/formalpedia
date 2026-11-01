-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_24_25
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:34:58.236793+00:00
-- url     : https://prove2.me/submissions/8e1dd2d7-88e5-44e0-ae65-e1605cd15f71

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

open BoundedEntropyGames.ConvRate

/-- Sum over functions of a product factorizes. -/
theorem BGE2425_sum_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : ι → κ → ℝ) : ∑ f : ι → κ, ∏ i, w i (f i) = ∏ i, ∑ b, w i b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset κ)), Fintype.piFinset_univ]

theorem BGE2425_sum_rpow_pos {T : Type*} [Fintype T] (p : T → ℝ) (hp : IsPMF p) (β : ℝ) :
    0 < ∑ t, p t ^ β := by
  obtain ⟨hnn, hs⟩ := hp
  obtain ⟨t0, ht0⟩ : ∃ t, 0 < p t := by
    by_contra h
    push Not at h
    have : ∑ t, p t ≤ 0 := Finset.sum_nonpos fun t _ => h t
    linarith
  calc 0 < p t0 ^ β := Real.rpow_pos_of_pos ht0 β
    _ ≤ ∑ t, p t ^ β :=
      Finset.single_le_sum (f := fun t => p t ^ β) (fun t _ => Real.rpow_nonneg (hnn t) β)
        (Finset.mem_univ t0)

theorem BGE2425_renyi_eq {T : Type*} [Fintype T] (p : T → ℝ) (hp : IsPMF p) (β : ℝ)
    (hβ : 0 < β) : renyi β p = 1 / (1 - β) * Real.logb 2 (∑ t, p t ^ β) := by
  unfold renyi
  rw [Real.logb_rpow_eq_mul_logb_of_pos (BGE2425_sum_rpow_pos p hp β)]
  field_simp

theorem BGE2425_part1 {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜]
    (p₁ p₂ : 𝒜 → ℝ) (h₁ : IsPMF p₁) (h₂ : IsPMF p₂) (m N : ℕ) (hmN : m ≤ N)
    (β : ℝ) (hβ : 0 < β) :
    renyi β (idealBlock p₁ p₂ m N) = m * renyi β p₁ + ((N : ℝ) - m) * renyi β p₂ := by
  set S1 := ∑ t, p₁ t ^ β
  set S2 := ∑ t, p₂ t ^ β
  have hS1 : 0 < S1 := BGE2425_sum_rpow_pos p₁ h₁ β
  have hS2 : 0 < S2 := BGE2425_sum_rpow_pos p₂ h₂ β
  have key : ∑ a : Fin N → 𝒜, idealBlock p₁ p₂ m N a ^ β = S1 ^ m * S2 ^ (N - m) := by
    have e : ∀ a : Fin N → 𝒜, idealBlock p₁ p₂ m N a ^ β =
        ∏ t : Fin N, (if (t : ℕ) < m then p₁ (a t) ^ β else p₂ (a t) ^ β) := by
      intro a
      unfold idealBlock
      rw [← Real.finsetProd_rpow]
      · refine Finset.prod_congr rfl fun t _ => ?_
        split_ifs <;> rfl
      · intro t _
        split_ifs
        · exact h₁.1 _
        · exact h₂.1 _
    simp_rw [e]
    rw [BGE2425_sum_prod (fun (t : Fin N) (b : 𝒜) =>
      if (t : ℕ) < m then p₁ b ^ β else p₂ b ^ β)]
    have e2 : ∀ t : Fin N, (∑ b, if (t : ℕ) < m then p₁ b ^ β else p₂ b ^ β) =
        if (t : ℕ) < m then S1 else S2 := by
      intro t; split_ifs <;> rfl
    simp_rw [e2]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Fin.card_filter_val_lt]
    have hc : (Finset.univ.filter (fun t : Fin N => ¬ (t : ℕ) < m)).card = N - m := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin N))) (fun t : Fin N => (t : ℕ) < m)
      rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [hc, min_eq_right hmN]
  have hidb : IsPMF (idealBlock p₁ p₂ m N) := by
    refine ⟨fun a => ?_, ?_⟩
    · unfold idealBlock
      exact Finset.prod_nonneg fun t _ => by split_ifs; exact h₁.1 _; exact h₂.1 _
    · have := key
      unfold idealBlock
      rw [BGE2425_sum_prod (fun (t : Fin N) (b : 𝒜) => if (t : ℕ) < m then p₁ b else p₂ b)]
      refine Finset.prod_eq_one fun t _ => ?_
      split_ifs
      · exact h₁.2
      · exact h₂.2
  rw [BGE2425_renyi_eq _ hidb β hβ, BGE2425_renyi_eq _ h₁ β hβ, BGE2425_renyi_eq _ h₂ β hβ, key,
    Real.logb_mul (pow_ne_zero _ hS1.ne') (pow_ne_zero _ hS2.ne'), Real.logb_pow, Real.logb_pow,
    Nat.cast_sub hmN]
  ring

theorem BGE2425_marg {𝒳 𝒴 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] (pXY : 𝒳 × 𝒴 → ℝ) (N : ℕ)
    (ys : Fin N → 𝒴) : marginalY (iidJoint pXY N) ys = ∏ t, marginalY pXY (ys t) := by
  unfold marginalY iidJoint
  exact BGE2425_sum_prod (fun t x => pXY (x, ys t))

theorem BGE2425_condRenyi_eq {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (α : ℝ)
    (pXY : 𝒳 × 𝒴 → ℝ) :
    condRenyi α pXY = α / (1 - α) * Real.logb 2
      (∑ y, marginalY pXY y * (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α)) := rfl

/-- positivity of the inner sum of the conditional Rényi entropy -/
theorem BGE2425_T_pos {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) (α : ℝ) :
    0 < ∑ y, marginalY pXY y * (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α) := by
  obtain ⟨hnn, hs⟩ := hp
  obtain ⟨⟨x0, y0⟩, h0⟩ : ∃ z, 0 < pXY z := by
    by_contra h
    push Not at h
    have : ∑ t, pXY t ≤ 0 := Finset.sum_nonpos fun t _ => h t
    linarith
  have hYnn : ∀ y, 0 ≤ marginalY pXY y := fun y => Finset.sum_nonneg fun x _ => hnn _
  have hY0 : 0 < marginalY pXY y0 :=
    lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun x => pXY (x, y0)) (fun x _ => hnn _)
      (Finset.mem_univ x0))
  have hin : 0 < ∑ x, (pXY (x, y0) / marginalY pXY y0) ^ α :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (div_pos h0 hY0) α)
      (Finset.single_le_sum (f := fun x => (pXY (x, y0) / marginalY pXY y0) ^ α)
        (fun x _ => Real.rpow_nonneg (div_nonneg (hnn _) (hYnn _)) α) (Finset.mem_univ x0))
  have hterm : ∀ y, 0 ≤ marginalY pXY y *
      (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α) := fun y =>
    mul_nonneg (hYnn y) (Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      Real.rpow_nonneg (div_nonneg (hnn _) (hYnn _)) α) _)
  exact lt_of_lt_of_le (mul_pos hY0 (Real.rpow_pos_of_pos hin _))
    (Finset.single_le_sum (f := fun y => marginalY pXY y *
      (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α)) (fun y _ => hterm y)
      (Finset.mem_univ y0))

theorem BGE2425_iid {𝒳 𝒴 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒴] [DecidableEq 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (N : ℕ) (α : ℝ) :
    condRenyi α (iidJoint pXY N) = N * condRenyi α pXY := by
  have hnn := hp.1
  have hYnn : ∀ y, 0 ≤ marginalY pXY y := fun y => Finset.sum_nonneg fun x _ => hnn _
  set A : 𝒴 → ℝ := fun y => ∑ x, (pXY (x, y) / marginalY pXY y) ^ α with hA
  have hAnn : ∀ y, 0 ≤ A y := fun y => Finset.sum_nonneg fun x _ =>
    Real.rpow_nonneg (div_nonneg (hnn _) (hYnn _)) α
  have inner : ∀ ys : Fin N → 𝒴,
      (∑ xs : Fin N → 𝒳, (iidJoint pXY N (xs, ys) / marginalY (iidJoint pXY N) ys) ^ α)
        = ∏ t, A (ys t) := by
    intro ys
    rw [BGE2425_marg]
    have e : ∀ xs : Fin N → 𝒳,
        (iidJoint pXY N (xs, ys) / ∏ t, marginalY pXY (ys t)) ^ α =
          ∏ t, (pXY (xs t, ys t) / marginalY pXY (ys t)) ^ α := by
      intro xs
      unfold iidJoint
      rw [← Finset.prod_div_distrib, Real.finsetProd_rpow]
      intro t _
      exact div_nonneg (hnn _) (hYnn _)
    simp_rw [e]
    exact BGE2425_sum_prod (fun t x => (pXY (x, ys t) / marginalY pXY (ys t)) ^ α)
  have total : (∑ ys : Fin N → 𝒴, marginalY (iidJoint pXY N) ys *
      (∑ xs : Fin N → 𝒳, (iidJoint pXY N (xs, ys) / marginalY (iidJoint pXY N) ys) ^ α)
        ^ (1 / α)) =
      (∑ y, marginalY pXY y * A y ^ (1 / α)) ^ N := by
    have e : ∀ ys : Fin N → 𝒴, marginalY (iidJoint pXY N) ys *
        (∑ xs : Fin N → 𝒳, (iidJoint pXY N (xs, ys) / marginalY (iidJoint pXY N) ys) ^ α)
          ^ (1 / α) = ∏ t, (marginalY pXY (ys t) * A (ys t) ^ (1 / α)) := by
      intro ys
      rw [inner, BGE2425_marg, ← Real.finsetProd_rpow _ _ (fun t _ => hAnn _),
        ← Finset.prod_mul_distrib]
    simp_rw [e]
    rw [BGE2425_sum_prod (fun (t : Fin N) y => marginalY pXY y * A y ^ (1 / α)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [BGE2425_condRenyi_eq, BGE2425_condRenyi_eq, total, Real.logb_pow]
  ring

theorem BGE2425_condRenyi_nonneg {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) :
    0 ≤ condRenyi α pXY := by
  have hnn := hp.1
  have hYnn : ∀ y, 0 ≤ marginalY pXY y := fun y => Finset.sum_nonneg fun x _ => hnn _
  have hYs : ∑ y, marginalY pXY y = 1 := by
    unfold marginalY
    rw [Finset.sum_comm, ← hp.2, ← Finset.sum_product']
    rfl
  set A : 𝒴 → ℝ := fun y => ∑ x, (pXY (x, y) / marginalY pXY y) ^ α with hA
  -- conditional pmf facts
  have hq1 : ∀ y, 0 < marginalY pXY y → ∀ x, pXY (x, y) / marginalY pXY y ≤ 1 := by
    intro y hy x
    rw [div_le_one hy]
    exact Finset.single_le_sum (f := fun x => pXY (x, y)) (fun x _ => hnn _) (Finset.mem_univ x)
  have hqs : ∀ y, 0 < marginalY pXY y → ∑ x, pXY (x, y) / marginalY pXY y = 1 := by
    intro y hy
    rw [← Finset.sum_div]
    exact div_self hy.ne'
  have hT := BGE2425_T_pos pXY hp α
  rw [BGE2425_condRenyi_eq]
  rcases lt_or_gt_of_ne hα1 with hlt | hgt
  · -- α < 1: show T ≥ 1
    have hA : ∀ y, marginalY pXY y ≤ marginalY pXY y * A y ^ (1 / α) := by
      intro y
      rcases (hYnn y).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have : 1 ≤ A y := by
          rw [← hqs y hpos]
          refine Finset.sum_le_sum fun x _ => ?_
          exact Real.self_le_rpow_of_le_one (div_nonneg (hnn _) (hYnn _)) (hq1 y hpos x) hlt.le
        have : 1 ≤ A y ^ (1 / α) := Real.one_le_rpow this (by positivity)
        nlinarith
    have hT1 : 1 ≤ ∑ y, marginalY pXY y * A y ^ (1 / α) :=
      le_trans (le_of_eq hYs.symm) (Finset.sum_le_sum fun y _ => hA y)
    have : 0 ≤ Real.logb 2 (∑ y, marginalY pXY y * A y ^ (1 / α)) :=
      Real.logb_nonneg (by norm_num) hT1
    have : 0 < α / (1 - α) := div_pos hα (by linarith)
    positivity
  · -- α > 1: T ≤ 1
    have hA : ∀ y, marginalY pXY y * A y ^ (1 / α) ≤ marginalY pXY y := by
      intro y
      rcases (hYnn y).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hA0 : 0 ≤ A y := Finset.sum_nonneg fun x _ =>
          Real.rpow_nonneg (div_nonneg (hnn _) (hYnn _)) α
        have : A y ≤ 1 := by
          rw [← hqs y hpos]
          refine Finset.sum_le_sum fun x _ => ?_
          exact Real.rpow_le_self_of_le_one (div_nonneg (hnn _) (hYnn _)) (hq1 y hpos x) hgt.le
        have : A y ^ (1 / α) ≤ 1 := Real.rpow_le_one hA0 this (by positivity)
        nlinarith
    have hT1 : ∑ y, marginalY pXY y * A y ^ (1 / α) ≤ 1 :=
      le_trans (Finset.sum_le_sum fun y _ => hA y) (le_of_eq hYs)
    have : Real.logb 2 (∑ y, marginalY pXY y * A y ^ (1 / α)) ≤ 0 :=
      Real.logb_nonpos (by norm_num) hT.le hT1
    have : α / (1 - α) < 0 := div_neg_of_pos_of_neg hα (by linarith)
    nlinarith

theorem solution {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype 𝒴] [DecidableEq 𝒴] :
    (∀ (p₁ p₂ : 𝒜 → ℝ), IsPMF p₁ → IsPMF p₂ → ∀ (m N : ℕ), m ≤ N →
      ∀ β : ℝ, 0 < β → β ≠ 1 →
        renyi β (idealBlock p₁ p₂ m N) = m * renyi β p₁ + ((N : ℝ) - m) * renyi β p₂) ∧
    (∀ (pXY : 𝒳 × 𝒴 → ℝ), IsPMF pXY → ∀ (N N' : ℕ), N ≤ N' →
      ∀ α : ℝ, 0 < α → α ≠ 1 →
        condRenyi α (iidJoint pXY N') = N' * condRenyi α pXY ∧
          (N : ℝ) * condRenyi α pXY ≤ N' * condRenyi α pXY) := by
  refine ⟨fun p₁ p₂ h₁ h₂ m N hmN β hβ _ => BGE2425_part1 p₁ p₂ h₁ h₂ m N hmN β hβ, ?_⟩
  intro pXY hp N N' hNN' α hα hα1
  refine ⟨BGE2425_iid pXY hp N' α, ?_⟩
  have := BGE2425_condRenyi_nonneg pXY hp α hα hα1
  have : (N : ℝ) ≤ N' := by exact_mod_cast hNN'
  nlinarith
