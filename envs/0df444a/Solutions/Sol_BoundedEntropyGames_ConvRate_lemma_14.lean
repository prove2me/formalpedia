-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:45:20.292507+00:00
-- url     : https://prove2.me/submissions/eb390dbe-155f-4967-873a-65c7828c9d28

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_A_5

open BoundedEntropyGames.ConvRate

theorem BGE14_sum_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : ι → κ → ℝ) : ∑ f : ι → κ, ∏ i, w i (f i) = ∏ i, ∑ b, w i b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset κ)), Fintype.piFinset_univ]

theorem BGE14_pF_sum {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) : ∑ f : 𝒳 → 𝒜, pF pA f = 1 := by
  unfold pF
  rw [BGE14_sum_prod (fun _ a => pA a)]
  exact Finset.prod_eq_one fun _ _ => hpA.2

theorem BGE14_pF_nonneg {𝒳 𝒜 : Type*} [Fintype 𝒳] [Fintype 𝒜] (pA : 𝒜 → ℝ) (hpA : IsPMF pA)
    (f : 𝒳 → 𝒜) : 0 ≤ pF pA f :=
  Finset.prod_nonneg fun _ _ => hpA.1 _

/-- Jensen: `E|Z| ≤ (E|Z|^α)^{1/α}` for a probability weight. -/
theorem BGE14_jensen {ι : Type*} [Fintype ι] (w z : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hz : ∀ i, 0 ≤ z i) (α : ℝ) (hα : 1 ≤ α) :
    ∑ i, w i * z i ≤ (∑ i, w i * z i ^ α) ^ (1 / α) := by
  have hJ := (convexOn_rpow hα).map_sum_le (t := Finset.univ) (w := w) (p := z)
    (fun i _ => hw i) hw1 (fun i _ => Set.mem_Ici.mpr (hz i))
  simp only [smul_eq_mul] at hJ
  have h0 : 0 ≤ ∑ i, w i * z i := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hz i)
  have hαpos : 0 < α := by linarith
  calc ∑ i, w i * z i = ((∑ i, w i * z i) ^ α) ^ (1 / α) := by
        rw [← Real.rpow_mul h0, mul_one_div_cancel hαpos.ne', Real.rpow_one]
    _ ≤ (∑ i, w i * z i ^ α) ^ (1 / α) :=
        Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hJ (by positivity)

theorem BGE14_tv_le_one {T : Type*} [Fintype T] (P Q : T → ℝ) (hP : IsPMF P) (hQ : IsPMF Q) :
    tv P Q ≤ 1 := by
  unfold tv
  have : ∑ t, |P t - Q t| ≤ ∑ t, (P t + Q t) := Finset.sum_le_sum fun t _ => by
    rw [abs_le]; constructor <;> linarith [hP.1 t, hQ.1 t]
  rw [Finset.sum_add_distrib, hP.2, hQ.2] at this
  linarith

theorem BGE14_tv_nonneg {T : Type*} [Fintype T] (P Q : T → ℝ) : 0 ≤ tv P Q := by
  unfold tv
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- homogeneity of the inner term of the conditional Rényi entropy -/
theorem BGE14_homog {𝒳 : Type*} [Fintype 𝒳] (p : 𝒳 → ℝ) (hp : ∀ x, 0 ≤ p x) (α : ℝ)
    (hα : 0 < α) :
    (∑ x, p x) * (∑ x, (p x / ∑ x, p x) ^ α) ^ (1 / α) = (∑ x, p x ^ α) ^ (1 / α) := by
  set m := ∑ x, p x with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun x _ => hp x
  rcases hm0.eq_or_lt with h0 | hpos
  · have hz : ∀ x, p x = 0 := by
      intro x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp x)).mp h0.symm x
        (Finset.mem_univ x)
      exact this
    simp [hz, ← h0, Real.zero_rpow hα.ne', Real.zero_rpow (inv_pos.mpr hα).ne']
  · have e : ∀ x, (p x / m) ^ α = p x ^ α / m ^ α := fun x =>
      Real.div_rpow (hp x) hpos.le α
    simp_rw [e]
    rw [← Finset.sum_div, Real.div_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hp x) α)
      (Real.rpow_nonneg hpos.le α), ← Real.rpow_mul hpos.le, mul_one_div_cancel hα.ne',
      Real.rpow_one]
    field_simp

theorem solution {𝒳 𝒴 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒴]
    [Fintype 𝒜] [DecidableEq 𝒜]
    (pXY : 𝒳 × 𝒴 → ℝ) (hpXY : IsPMF pXY) (pA : 𝒜 → ℝ) (hpA : IsPMF pA) :
    (∀ α ∈ Set.Icc (1 : ℝ) 2,
      ∑ f : 𝒳 → 𝒜, pF pA f * tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2)
        ≤ (2 : ℝ) ^ (-(1 - 1 / α) * (condRenyi α pXY - renyi (1 / α) pA + 2))) ∧
    ∃ f : 𝒳 → 𝒜, ∀ α ∈ Set.Icc (1 : ℝ) 2,
      tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2)
        ≤ (2 : ℝ) ^ (-(1 - 1 / α) * (condRenyi α pXY - renyi (1 / α) pA + 2)) := by
  have hnn := hpXY.1
  have hpF1 := BGE14_pF_sum (𝒳 := 𝒳) pA hpA
  have hpF0 := BGE14_pF_nonneg (𝒳 := 𝒳) pA hpA
  -- the TV distance as a sum of |Z|
  set Z : (𝒳 → 𝒜) → 𝒜 → 𝒴 → ℝ := fun f a y =>
    ∑ x, pXY (x, y) * ((if f x = a then 1 else 0) - pA a) with hZ
  have tvZ : ∀ f : 𝒳 → 𝒜, tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2) =
      1 / 2 * ∑ a, ∑ y, |Z f a y| := by
    intro f
    unfold tv
    rw [Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    simp only [hZ, pfXY, marginalY, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  -- the main bound: E[TV] ≤ ½ 2^{(2-α)/α} S_A T for α ∈ [1,2]
  have main : ∀ α ∈ Set.Icc (1 : ℝ) 2,
      ∑ f : 𝒳 → 𝒜, pF pA f * tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2) ≤
        1 / 2 * ((2 : ℝ) ^ (2 - α)) ^ (1 / α) * (∑ a, pA a ^ (1 / α)) *
          ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
    intro α hα
    have hα1 := hα.1
    have hαpos : 0 < α := by linarith
    simp_rw [tvZ]
    have e1 : ∑ f : 𝒳 → 𝒜, pF pA f * (1 / 2 * ∑ a, ∑ y, |Z f a y|) =
        1 / 2 * ∑ a, ∑ y, ∑ f : 𝒳 → 𝒜, pF pA f * |Z f a y| := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    rw [e1]
    have e2 : ∀ a y, ∑ f : 𝒳 → 𝒜, pF pA f * |Z f a y| ≤
        ((2 : ℝ) ^ (2 - α)) ^ (1 / α) * pA a ^ (1 / α) * (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
      intro a y
      have hJ := BGE14_jensen (fun f => pF pA f) (fun f => |Z f a y|) hpF0 hpF1
        (fun f => abs_nonneg _) α hα1
      have hA5 := eq_A_5 (𝒳 := 𝒳) pA hpA α hα (fun x => pXY (x, y)) a
      have habs : ∀ x, |pXY (x, y)| ^ α = pXY (x, y) ^ α := fun x => by
        rw [abs_of_nonneg (hnn _)]
      simp_rw [habs] at hA5
      refine le_trans hJ ?_
      have h2p : (0 : ℝ) ≤ 2 ^ (2 - α) := Real.rpow_nonneg (by norm_num) _
      rw [← Real.mul_rpow h2p (hpA.1 a), ← Real.mul_rpow (mul_nonneg h2p (hpA.1 a))
        (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hnn _) α)]
      exact Real.rpow_le_rpow (Finset.sum_nonneg fun f _ =>
        mul_nonneg (hpF0 f) (Real.rpow_nonneg (abs_nonneg _) _)) hA5 (by positivity)
    have e3 : 1 / 2 * ∑ a, ∑ y, ∑ f : 𝒳 → 𝒜, pF pA f * |Z f a y| ≤
        1 / 2 * ∑ a, ∑ y, ((2 : ℝ) ^ (2 - α)) ^ (1 / α) * pA a ^ (1 / α) *
          (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun y _ => e2 a y
    refine le_trans e3 (le_of_eq ?_)
    set C : ℝ := ((2 : ℝ) ^ (2 - α)) ^ (1 / α)
    have : ∑ a, ∑ y, C * pA a ^ (1 / α) * (∑ x, pXY (x, y) ^ α) ^ (1 / α) =
        C * (∑ a, pA a ^ (1 / α)) * ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
      calc ∑ a, ∑ y, C * pA a ^ (1 / α) * (∑ x, pXY (x, y) ^ α) ^ (1 / α)
          = ∑ a, (C * pA a ^ (1 / α)) * ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
            simp_rw [Finset.mul_sum]
        _ = (∑ a, C * pA a ^ (1 / α)) * ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
            rw [Finset.sum_mul]
        _ = C * (∑ a, pA a ^ (1 / α)) * ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
            rw [← Finset.mul_sum]
    rw [this]
    ring
  -- evaluate the right-hand side
  have hT : ∀ α ∈ Set.Icc (1 : ℝ) 2, ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) =
      ∑ y, marginalY pXY y * (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α) := by
    intro α hα
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold marginalY
    rw [BGE14_homog (fun x => pXY (x, y)) (fun x => hnn _) α (by linarith [hα.1])]
  have hTpos : ∀ α ∈ Set.Icc (1 : ℝ) 2, 0 < ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) := by
    intro α hα
    have hαpos : 0 < α := by linarith [hα.1]
    obtain ⟨⟨x0, y0⟩, h0⟩ : ∃ z, 0 < pXY z := by
      by_contra h
      push Not at h
      have : ∑ t, pXY t ≤ 0 := Finset.sum_nonpos fun t _ => h t
      linarith [hpXY.2]
    have hin : 0 < ∑ x, pXY (x, y0) ^ α :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos h0 α)
        (Finset.single_le_sum (f := fun x => pXY (x, y0) ^ α)
          (fun x _ => Real.rpow_nonneg (hnn _) α) (Finset.mem_univ x0))
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hin _)
      (Finset.single_le_sum (f := fun y => (∑ x, pXY (x, y) ^ α) ^ (1 / α))
        (fun y _ => Real.rpow_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hnn _) α) _)
        (Finset.mem_univ y0))
  have hSApos : ∀ β : ℝ, 0 < ∑ a, pA a ^ β := by
    intro β
    obtain ⟨a0, ha0⟩ : ∃ a, 0 < pA a := by
      by_contra h
      push Not at h
      have : ∑ t, pA t ≤ 0 := Finset.sum_nonpos fun t _ => h t
      linarith [hpA.2]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos ha0 β)
      (Finset.single_le_sum (f := fun a => pA a ^ β) (fun a _ => Real.rpow_nonneg (hpA.1 a) β)
        (Finset.mem_univ a0))
  have rhs : ∀ α ∈ Set.Icc (1 : ℝ) 2,
      1 / 2 * ((2 : ℝ) ^ (2 - α)) ^ (1 / α) * (∑ a, pA a ^ (1 / α)) *
          ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) =
        (2 : ℝ) ^ (-(1 - 1 / α) * (condRenyi α pXY - renyi (1 / α) pA + 2)) := by
    intro α hα
    have hαpos : 0 < α := by linarith [hα.1]
    set T := ∑ y, (∑ x, pXY (x, y) ^ α) ^ (1 / α) with hTdef
    set S := ∑ a, pA a ^ (1 / α) with hS
    have hT0 := hTpos α hα
    have hS0 := hSApos (1 / α)
    rcases eq_or_lt_of_le hα.1 with h1 | h1
    · -- α = 1
      subst h1
      have hT1 : T = 1 := by
        rw [hTdef]
        simp only [Real.rpow_one, div_one]
        rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun x y => pXY (x, y))]
        exact hpXY.2
      have hS1 : S = 1 := by rw [hS]; simp [hpA.2]
      rw [hT1, hS1]; norm_num
    · have hα1 : α ≠ 1 := ne_of_gt h1
      have hcR : condRenyi α pXY = α / (1 - α) * Real.logb 2 T := by
        unfold condRenyi; rw [← hT α hα]
      have hR : renyi (1 / α) pA = 1 / (1 - 1 / α) * Real.logb 2 S := by
        unfold renyi
        rw [Real.logb_rpow_eq_mul_logb_of_pos hS0]
        field_simp
        try rfl
      rw [hcR, hR]
      have hden : (1 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
      have hden2 : (1 : ℝ) - 1 / α ≠ 0 := by
        intro h; apply hα1; field_simp at h; linarith
      have hexp : -(1 - 1 / α) * (α / (1 - α) * Real.logb 2 T - 1 / (1 - 1 / α) *
          Real.logb 2 S + 2) = Real.logb 2 T + Real.logb 2 S + (2 / α - 2) := by
        field_simp
        ring
      rw [hexp, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hT0, Real.rpow_logb (by norm_num) (by norm_num) hS0,
        ← Real.rpow_mul (by norm_num)]
      have : (2 : ℝ) ^ (2 / α - 2) = 1 / 2 * (2 : ℝ) ^ ((2 - α) * (1 / α)) := by
        rw [show (2 / α - 2 : ℝ) = (2 - α) * (1 / α) + (-1) by field_simp; ring,
          Real.rpow_add (by norm_num), Real.rpow_neg_one]
        ring
      rw [this]
      ring
  have part1 : ∀ α ∈ Set.Icc (1 : ℝ) 2,
      ∑ f : 𝒳 → 𝒜, pF pA f * tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2)
        ≤ (2 : ℝ) ^ (-(1 - 1 / α) * (condRenyi α pXY - renyi (1 / α) pA + 2)) :=
    fun α hα => (rhs α hα) ▸ main α hα
  refine ⟨part1, ?_⟩
  -- averaging: some f has TV ≤ E[TV]
  set E := ∑ f : 𝒳 → 𝒜, pF pA f * tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2)
  obtain ⟨f, hf⟩ : ∃ f : 𝒳 → 𝒜, tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2) ≤ E := by
    by_contra h
    push Not at h
    obtain ⟨f0, hf0⟩ : ∃ f : 𝒳 → 𝒜, 0 < pF pA f := by
      by_contra h'
      push Not at h'
      have : ∑ f : 𝒳 → 𝒜, pF pA f ≤ 0 := Finset.sum_nonpos fun f _ => h' f
      linarith
    have hpos : 0 < ∑ f : 𝒳 → 𝒜, pF pA f *
        (tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2) - E) :=
      Finset.sum_pos' (fun f _ => mul_nonneg (hpF0 f) (by linarith [h f]))
        ⟨f0, Finset.mem_univ _, mul_pos hf0 (by linarith [h f0])⟩
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hpF1, one_mul] at hpos
    linarith
  exact ⟨f, fun α hα => le_trans hf (part1 α hα)⟩
