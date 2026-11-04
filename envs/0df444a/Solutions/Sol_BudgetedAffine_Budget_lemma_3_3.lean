-- Prove2me | solution 1 for BudgetedAffine.Budget.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:35:52.095188+00:00
-- url     : https://prove2.me/submissions/8c723d07-f023-4ff7-807a-5318271a2430

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Budget_Rescaling
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_LinearOptimization_DualLP
import Theorems.Thm_BudgetedAffine_Budget_claim_3_1
import Theorems.Thm_BudgetedAffine_Budget_claim_3_2
import Theorems.Thm_BudgetedAffine_Budget_claim_3_3
import Theorems.Thm_BudgetedAffine_Budget_coverCost_attained
import Theorems.Thm_LinearOptimization_lp_strong_duality

set_option autoImplicit false
open Matrix

namespace BudLem33

/-- The failure probability of Claim 3.2 plus that of Claim 3.3 is `< 1` for large `n`. -/
theorem tail_small : ∃ N : ℕ, ∀ n ≥ N, 3 ≤ n ∧
    (n : ℝ) * (Real.exp (BudgetedAffine.Budget.beta n / 2 - 2) /
      (1 + (BudgetedAffine.Budget.beta n / 2 - 2)) ^ (1 + (BudgetedAffine.Budget.beta n / 2 - 2)))
      < 1 - Real.exp (-(1 / 8)) := by
  refine ⟨⌈Real.exp (Real.exp 81)⌉₊, fun n hn => ?_⟩
  have hnR : Real.exp (Real.exp 81) ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have he81 : (82 : ℝ) ≤ Real.exp 81 := by linarith [Real.add_one_le_exp (81 : ℝ)]
  have hee : Real.exp 81 + 1 ≤ Real.exp (Real.exp 81) := Real.add_one_le_exp _
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by exact_mod_cast (show (3 : ℝ) ≤ n by linarith), ?_⟩
  set L := Real.log n with hLdef
  have hL : Real.exp 81 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hn0]; exact hnR
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓdef
  have hℓ : 81 ≤ ℓ := by rw [hℓdef, Real.le_log_iff_exp_le hL0]; exact hL
  have hLexp : Real.exp ℓ = L := Real.exp_log hL0
  -- L ≥ 2ℓ + 20
  have hL2 : 2 * ℓ + 20 ≤ L := by
    have h1 : ℓ / 2 + 1 ≤ Real.exp (ℓ / 2) := Real.add_one_le_exp _
    have h2 : Real.exp ℓ = Real.exp (ℓ / 2) * Real.exp (ℓ / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : (ℓ / 2 + 1) * (ℓ / 2 + 1) ≤ Real.exp (ℓ / 2) * Real.exp (ℓ / 2) :=
      mul_le_mul h1 h1 (by linarith) (by positivity)
    nlinarith
  -- a = log ℓ
  set a := Real.log ℓ with hadef
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  have ha : 4 * (a + 1) ≤ ℓ := by
    set s := Real.sqrt ℓ with hs
    have hs9 : 9 ≤ s := by rw [hs, Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have hss : s * s = ℓ := Real.mul_self_sqrt (by linarith)
    have hlog : a = 2 * Real.log s := by
      rw [hadef, hs, Real.log_sqrt (by linarith)]; ring
    have hls : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
    nlinarith
  -- t = L/ℓ, u = 2t - 1
  set t := L / ℓ with htdef
  have hℓ0 : 0 < ℓ := by linarith
  have htl : t * ℓ = L := by rw [htdef]; field_simp
  have ht2 : 2 ≤ t := by rw [htdef, le_div_iff₀ hℓ0]; linarith
  have hβ : BudgetedAffine.Budget.beta n / 2 - 2 = 2 * t - 2 := by
    unfold BudgetedAffine.Budget.beta; rw [htdef, hℓdef, hLdef]; ring
  rw [hβ]
  set u := 1 + (2 * t - 2) with hudef
  have hu : u = 2 * t - 1 := by rw [hudef]; ring
  have hu0 : 0 < u := by rw [hu]; linarith
  have hlogt : Real.log t = ℓ - a := by
    rw [htdef, Real.log_div (by linarith) (by linarith)]
  have hlogu : ℓ - a ≤ Real.log u := by
    rw [← hlogt]; exact Real.log_le_log (by linarith) (by rw [hu]; linarith)
  have hX : L + (2 * t - 2) - Real.log u * u ≤ -12 := by
    have h1 : u * (ℓ - a) ≤ u * Real.log u := mul_le_mul_of_nonneg_left hlogu hu0.le
    have e1 : u * (ℓ - a) = 2 * (t * ℓ) - 2 * (t * a) - ℓ + a := by rw [hu]; ring
    have h2 : t * (4 * (a + 1)) ≤ t * ℓ := mul_le_mul_of_nonneg_left ha (by linarith)
    nlinarith
  have hrpow : u ^ u = Real.exp (Real.log u * u) := Real.rpow_def_of_pos hu0 u
  have hval : (n : ℝ) * (Real.exp (2 * t - 2) / u ^ u) = Real.exp (L + (2 * t - 2) - Real.log u * u) := by
    rw [hrpow, show L + (2 * t - 2) - Real.log u * u = L + ((2 * t - 2) - Real.log u * u) by ring,
      Real.exp_add, Real.exp_sub (2 * t - 2), hLdef, Real.exp_log hn0]
  rw [hval]
  have h12 : Real.exp (L + (2 * t - 2) - Real.log u * u) ≤ Real.exp (-12) := Real.exp_le_exp.2 hX
  have he12 : Real.exp (-12) ≤ 1 / 13 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_le_exp (12 : ℝ)]
  have he8 : Real.exp (-(1 / 8)) ≤ 8 / 9 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.add_one_le_exp (1 / 8 : ℝ)]
  linarith

open SpectralSparsify.Sampling

theorem outcomeProb_nonneg {α : Type} [DecidableEq α] (E : Finset α) (p : α → ℝ)
    (hp : ∀ e ∈ E, 0 ≤ p e ∧ p e ≤ 1) (T : Finset α) (hT : T ⊆ E) : 0 ≤ outcomeProb E p T := by
  unfold outcomeProb
  refine mul_nonneg (Finset.prod_nonneg (fun e he => (hp e (hT he)).1))
    (Finset.prod_nonneg (fun e he => ?_))
  have := (hp e (Finset.mem_sdiff.1 he).1).2
  linarith

theorem sum_outcomeProb {α : Type} [DecidableEq α] (E : Finset α) (p : α → ℝ) :
    ∑ T ∈ E.powerset, outcomeProb E p T = 1 := by
  unfold outcomeProb
  rw [← Finset.prod_add]
  simp

theorem exists_both {α : Type} [DecidableEq α] (E : Finset α) (p : α → ℝ)
    (hp : ∀ e ∈ E, 0 ≤ p e ∧ p e ≤ 1) (P Q : Finset α → Prop)
    (h : 1 < prob E p P + prob E p Q) : ∃ T ∈ E.powerset, P T ∧ Q T := by
  classical
  by_contra hcon
  push_neg at hcon
  apply absurd h
  rw [not_lt]
  unfold prob
  rw [← Finset.sum_add_distrib, ← sum_outcomeProb E p]
  refine Finset.sum_le_sum (fun T hT => ?_)
  have h0 := outcomeProb_nonneg E p hp T (Finset.mem_powerset.1 hT)
  by_cases hP : P T
  · have hQ : ¬ Q T := hcon T hT hP
    simp [hP, hQ]
  · by_cases hQ : Q T <;> simp [hP, hQ, h0]

end BudLem33

namespace BudLem33

open BudgetedAffine.Budget

theorem colMax_nonneg {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1) (j : Fin n) :
    0 ≤ colMax B w J j := by
  unfold colMax
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp [Real.iSup_of_isEmpty]
  · obtain ⟨k⟩ := hJ
    refine le_trans (mul_nonneg (hw k k.2).1.le (hB k j)) ?_
    exact le_ciSup (f := fun k : J => w k * B k j) (Set.finite_range _).bddAbove k

theorem BHat_nonneg {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1) :
    ∀ i j, 0 ≤ BHat B w J i j := by
  intro i j
  unfold BHat
  simp only [Matrix.of_apply]
  split_ifs with hi
  · exact div_nonneg (mul_nonneg (hw i hi).1.le (hB i j)) (colMax_nonneg B w J hB hw j)
  · exact le_rfl

theorem coverCost_nonneg' {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) (hd : 0 ≤ d)
    (h : Fin m → ℝ) : (0 : EReal) ≤ coverCost M d h := by
  refine le_iInf₂ (fun y hy => ?_)
  exact_mod_cast dotProduct_nonneg_of_nonneg hd hy.1

/-- Weak duality for (3.8)/(3.9): a packing vector `u ≥ 0` (on `J`) feasible for (3.7) bounds the
covering value of `W ⊆ J` from below. -/
theorem weak_dual {m n : ℕ} (Bh : Matrix (Fin m) (Fin n) ℝ) (dh : Fin n → ℝ) (hBh : ∀ i j, 0 ≤ Bh i j)
    (J W : Finset (Fin m)) (hWJ : W ⊆ J) (w : Fin m → ℝ) (u : Fin m → ℝ)
    (hu : DualFeasible Bh dh J u) :
    (((∑ i ∈ W, w i * u i : ℝ)) : EReal) ≤ coverCost Bh dh (wIndic w W) := by
  refine le_iInf₂ (fun y hy => ?_)
  obtain ⟨hy0, hycov⟩ := hy
  have hBy0 : ∀ i, 0 ≤ (Bh *ᵥ y) i := fun i => by
    show 0 ≤ ∑ j, Bh i j * y j
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hBh i j) (hy0 j))
  have h1 : ∑ i ∈ W, w i * u i ≤ ∑ i ∈ W, u i * (Bh *ᵥ y) i := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have := hycov i
    simp only [wIndic, hi, if_true] at this
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left this (hu.1 i (hWJ hi))
  have h2 : ∑ i ∈ W, u i * (Bh *ᵥ y) i ≤ ∑ i ∈ J, u i * (Bh *ᵥ y) i :=
    Finset.sum_le_sum_of_subset_of_nonneg hWJ (fun i hi _ => mul_nonneg (hu.1 i hi) (hBy0 i))
  have h3 : ∑ i ∈ J, u i * (Bh *ᵥ y) i = ∑ j, (∑ i ∈ J, Bh i j * u i) * y j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  have h4 : ∑ j, (∑ i ∈ J, Bh i j * u i) * y j ≤ dh ⬝ᵥ y := by
    unfold dotProduct
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hu.2 j) (hy0 j))
  exact_mod_cast (by linarith : ∑ i ∈ W, w i * u i ≤ dh ⬝ᵥ y)

end BudLem33

open BudLem33 BudgetedAffine.Budget SpectralSparsify.Sampling in
theorem solution :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (m : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
      (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ d → 0 < γ → (∀ i ∈ J, 0 < w i ∧ w i ≤ 1) →
      (∀ i ∈ J, ((4 * γ * (Real.log n / Real.log (Real.log n)) * w i : ℝ) : EReal) <
        coverCost B d (Pi.single i 1)) →
      (∀ W ⊆ J, ∑ i ∈ W, w i ≤ 1 → coverCost B d (indic W) ≤ (γ : EReal)) →
      coverCost B d (indic J) ≤ ((4 * γ * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) := by
  classical
  obtain ⟨N, hN⟩ := tail_small
  refine ⟨N, fun n hn m B d J γ w hB hd hγ hw hc1 hc2 => ?_⟩
  obtain ⟨hn3, htail⟩ := hN n hn
  set η := beta n with hηdef
  have hη : 4 * γ * (Real.log n / Real.log (Real.log n)) = η * γ := by
    rw [hηdef]; unfold beta; ring
  have hηpos : 0 < η := by
    have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn3
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have : 0 < Real.log (Real.log n) := Real.log_pos hlog
    rw [hηdef]; unfold beta; positivity
  have hηγ : 0 < η * γ := mul_pos hηpos hγ
  rw [hη]
  by_contra hcon
  rw [not_le] at hcon
  -- `z(J)` is finite
  have hfe : ∀ i, i ∈ J → ∃ y : Fin n → ℝ, 0 ≤ y ∧ indic {i} ≤ B *ᵥ y := by
    intro i hi
    have h1 := hc2 {i} (by simpa using hi) (by simpa using (hw i hi).2)
    have h2 : coverCost B d (indic {i}) < ⊤ := lt_of_le_of_lt h1 (EReal.coe_lt_top γ)
    unfold coverCost at h2
    rw [iInf_lt_iff] at h2
    obtain ⟨y, hy⟩ := h2
    rw [iInf_lt_iff] at hy
    obtain ⟨hyf, -⟩ := hy
    exact ⟨y, hyf⟩
  choose! yi hyi using hfe
  have hJfin : coverCost B d (indic J) ≠ ⊤ := by
    have hfeas : 0 ≤ ∑ i ∈ J, yi i ∧ indic J ≤ B *ᵥ ∑ i ∈ J, yi i := by
      refine ⟨Finset.sum_nonneg (fun i hi => (hyi i hi).1), fun r => ?_⟩
      rw [Matrix.mulVec_sum, Finset.sum_apply]
      have hnn : ∀ i ∈ J, 0 ≤ (B *ᵥ yi i) r := fun i hi => by
        show 0 ≤ ∑ j, B r j * yi i j
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hB r j) ((hyi i hi).1 j))
      by_cases hr : r ∈ J
      · have h1 := (hyi r hr).2 r
        simp only [indic, Finset.mem_singleton, if_true] at h1
        simp only [indic, hr, if_true]
        exact le_trans h1 (Finset.single_le_sum (f := fun i => (B *ᵥ yi i) r) hnn hr)
      · simp only [indic, hr, if_false]
        exact Finset.sum_nonneg hnn
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf₂_le (∑ i ∈ J, yi i) hfeas)
  -- rescaling (Claim 3.1)
  set Bh := BHat B w J with hBh
  set dh := dHat B d w J η γ with hdh
  have hBhnn : ∀ i j, 0 ≤ Bh i j := BHat_nonneg B w J hB hw
  have hdhnn : 0 ≤ dh := fun j =>
    div_nonneg (hd j) (mul_nonneg hηγ.le (colMax_nonneg B w J hB hw j))
  have h31 : ∀ W ⊆ J, coverCost B d (indic W) = ((η * γ : ℝ) : EReal) * coverCost Bh dh (wIndic w W) :=
    fun W hW => claim_3_1 hn3 B d J γ w hB hd hγ hw W hW
  have hzJ := h31 J subset_rfl
  have hzhJ_ne_top : coverCost Bh dh (wIndic w J) ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_mul_top_of_pos hηγ] at hzJ
    exact hJfin hzJ
  obtain ⟨zr, hzr⟩ : ∃ zr : ℝ, coverCost Bh dh (wIndic w J) = (zr : EReal) :=
    ⟨_, (EReal.coe_toReal hzhJ_ne_top (ne_bot_of_le_ne_bot (by simp)
      (coverCost_nonneg' Bh dh hdhnn _))).symm⟩
  have hzr1 : 1 < zr := by
    rw [hzJ, hzr, ← EReal.coe_mul] at hcon
    have := EReal.coe_lt_coe_iff.1 hcon
    nlinarith
  -- primal optimum and strong duality
  obtain ⟨ystar, hy0, hycov, hyval⟩ := coverCost_attained Bh dh (wIndic w J) hdhnn hzhJ_ne_top
  set P : LinearOptimization.GeneralFormLP m n :=
    ⟨Bh, wIndic w J, dh, fun _ => .ge, fun _ => .nonneg⟩ with hP
  have hPfeas : ∀ y, y ∈ LinearOptimization.generalFeasibleSet P ↔ 0 ≤ y ∧ wIndic w J ≤ Bh *ᵥ y := by
    intro y
    simp only [LinearOptimization.generalFeasibleSet, hP, LinearOptimization.LinearConstraint.IsSatisfiedAt,
      LinearOptimization.VarSign.IsSatisfiedBy, Set.mem_setOf_eq, Pi.le_def, Matrix.mulVec]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  have hopt : LinearOptimization.IsLpOptimal P.c (LinearOptimization.generalFeasibleSet P) ystar := by
    refine ⟨(hPfeas ystar).2 ⟨hy0, hycov⟩, fun y hy => ?_⟩
    have := iInf₂_le (f := fun (y : Fin n → ℝ) (_ : 0 ≤ y ∧ wIndic w J ≤ Bh *ᵥ y) =>
      ((dh ⬝ᵥ y : ℝ) : EReal)) y ((hPfeas y).1 hy)
    change coverCost Bh dh (wIndic w J) ≤ _ at this
    rw [← hyval] at this
    exact_mod_cast this
  obtain ⟨p, ⟨hpfeas, -⟩, hpval⟩ := LinearOptimization.lp_strong_duality P ystar hopt
  have hDF : DualFeasible Bh dh J p := by
    obtain ⟨hrow, hsign⟩ := hpfeas
    refine ⟨fun i _ => hsign i, fun j => ?_⟩
    have h1 : (-dh) j ≤ (-Bhᵀ) j ⬝ᵥ p := hrow j
    have h2 : (-Bhᵀ) j ⬝ᵥ p = -∑ i ∈ J, Bh i j * p i := by
      simp only [dotProduct, Matrix.neg_apply, Matrix.transpose_apply, neg_mul,
        Finset.sum_neg_distrib, neg_inj]
      rw [← Finset.sum_subset (Finset.subset_univ J)]
      intro i _ hi
      simp [hBh, BHat, hi]
    rw [h2] at h1
    simp only [Pi.neg_apply, neg_le_neg_iff] at h1
    exact h1
  have hsum : 1 < ∑ i ∈ J, w i * p i := by
    have : p ⬝ᵥ wIndic w J = ∑ i ∈ J, w i * p i := by
      simp only [dotProduct, wIndic, mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext; simp) (fun i _ => by ring)
    have hv : P.c ⬝ᵥ ystar = zr := by
      have := hyval
      rw [hzr] at this
      exact_mod_cast this
    rw [← this]
    have : p ⬝ᵥ P.b = zr := by rw [hpval, hv]
    simpa [hP] using (show 1 < p ⬝ᵥ P.b by rw [this]; exact hzr1)
  have hp0 : ∀ i ∈ J, 0 ≤ p i := hDF.1
  -- randomized rounding: Claims 3.2 and 3.3
  have h32 := claim_3_2 hn3 B d J γ w hB hd hγ hw hc1 p hDF
  have h33 := claim_3_3 J w p hw hp0 hsum
  have hfrac : ∀ i ∈ J, 0 ≤ p i - ⌊p i⌋ ∧ p i - ⌊p i⌋ ≤ 1 := fun i _ =>
    ⟨by linarith [Int.floor_le (p i)], by linarith [Int.lt_floor_add_one (p i)]⟩
  obtain ⟨T, hT, hTA, hTB⟩ := exists_both J (fun i => p i - ⌊p i⌋) hfrac _ _
    (lt_of_lt_of_le (by linarith) (add_le_add h32 h33))
  set Z : Fin m → ℝ := fun i => (⌊p i⌋ : ℝ) + if i ∈ T then 1 else 0 with hZ
  have hZint : ∀ i ∈ J, Z i = 0 ∨ 1 ≤ Z i := by
    intro i hi
    have hf : (0 : ℤ) ≤ ⌊p i⌋ := Int.floor_nonneg.2 (hp0 i hi)
    rcases (Int.le_iff_lt_or_eq.1 hf) with hlt | heq
    · right
      have : (1 : ℝ) ≤ (⌊p i⌋ : ℝ) := by exact_mod_cast hlt
      simp only [hZ]
      split_ifs <;> linarith
    · simp only [hZ, ← heq, Int.cast_zero, zero_add]
      split_ifs
      · right; exact le_rfl
      · left; rfl
  have hZ0 : ∀ i ∈ J, 0 ≤ Z i := fun i hi => by
    rcases hZint i hi with h | h <;> linarith
  -- a scenario `W`
  have hW : ∃ W ⊆ J, ∑ i ∈ W, w i ≤ 1 ∧ 1 / 2 < ∑ i ∈ W, w i * Z i := by
    set J' := J.filter (fun i => 1 ≤ Z i) with hJ'
    have hJ'J : J' ⊆ J := Finset.filter_subset _ _
    have hsumJ' : ∑ i ∈ J, w i * Z i = ∑ i ∈ J', w i * Z i := by
      rw [hJ', Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rcases hZint i hi with h | h
      · simp [h]
      · simp [h]
    have hB' : 1 / 2 < ∑ i ∈ J', w i * Z i := hsumJ' ▸ hTB
    by_cases hbig : ∃ i ∈ J', 1 / 2 < w i * Z i
    · obtain ⟨i, hi, hgt⟩ := hbig
      exact ⟨{i}, by simpa using hJ'J hi, by simpa using (hw i (hJ'J hi)).2, by simpa using hgt⟩
    push_neg at hbig
    set F := J'.powerset.filter (fun W => ∑ i ∈ W, w i * Z i ≤ 1 / 2) with hF
    have hFne : F.Nonempty := ⟨∅, by simp [hF]⟩
    obtain ⟨W0, hW0F, hW0max⟩ := Finset.exists_max_image F (fun W => ∑ i ∈ W, w i * Z i) hFne
    obtain ⟨hW0J', hW0s⟩ := Finset.mem_filter.1 hW0F
    rw [Finset.mem_powerset] at hW0J'
    have hne : W0 ≠ J' := by
      intro h; rw [h] at hW0s; linarith
    obtain ⟨i, hiJ', hiW0⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hW0J' hne)
    have hiJ := hJ'J hiJ'
    have hZi : 1 ≤ Z i := (Finset.mem_filter.1 hiJ').2
    have hwi := hw i hiJ
    have hpos : 0 < w i * Z i := mul_pos hwi.1 (by linarith)
    have hins : ∑ j ∈ insert i W0, w j * Z j = w i * Z i + ∑ j ∈ W0, w j * Z j :=
      Finset.sum_insert hiW0
    refine ⟨insert i W0, Finset.insert_subset hiJ (hW0J'.trans hJ'J), ?_, ?_⟩
    · rw [Finset.sum_insert hiW0]
      have h1 : ∑ j ∈ W0, w j ≤ ∑ j ∈ W0, w j * Z j := Finset.sum_le_sum (fun j hj => by
        have hZj : 1 ≤ Z j := (Finset.mem_filter.1 (hW0J' hj)).2
        have := (hw j (hJ'J (hW0J' hj))).1
        nlinarith)
      have h2 : w i ≤ w i * Z i := by nlinarith
      have h3 := hbig i hiJ'
      linarith
    · by_contra hle
      rw [not_lt] at hle
      have hmem : insert i W0 ∈ F := Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 (Finset.insert_subset hiJ' hW0J'), hle⟩
      have := hW0max _ hmem
      rw [hins] at this
      linarith
  obtain ⟨W, hWJ, hWw, hWZ⟩ := hW
  -- weak duality on `W` and Claim 3.1
  have hu : DualFeasible Bh dh J (fun i => 2 * Z i / η) := hTA
  have hwd := weak_dual Bh dh hBhnn J W hWJ w (fun i => 2 * Z i / η) hu
  have hv : 1 / η < ∑ i ∈ W, w i * (2 * Z i / η) := by
    have : ∑ i ∈ W, w i * (2 * Z i / η) = (2 / η) * ∑ i ∈ W, w i * Z i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]
    have : (2 / η) * (1 / 2) = 1 / η := by field_simp
    rw [← this]
    exact mul_lt_mul_of_pos_left hWZ (by positivity)
  have hzW := h31 W hWJ
  have hgt : (γ : EReal) < coverCost B d (indic W) := by
    rw [hzW]
    set v := ∑ i ∈ W, w i * (2 * Z i / η)
    by_cases htop : coverCost Bh dh (wIndic w W) = ⊤
    · rw [htop, EReal.coe_mul_top_of_pos hηγ]; exact EReal.coe_lt_top γ
    obtain ⟨r, hr⟩ : ∃ r : ℝ, coverCost Bh dh (wIndic w W) = (r : EReal) :=
      ⟨_, (EReal.coe_toReal htop (ne_bot_of_le_ne_bot (by simp)
        (coverCost_nonneg' Bh dh hdhnn _))).symm⟩
    rw [hr] at hwd ⊢
    rw [← EReal.coe_mul]
    have hvr : v ≤ r := EReal.coe_le_coe_iff.1 hwd
    have : γ < η * γ * r := by
      have h1 : η * γ * (1 / η) = γ := by field_simp
      have h2 : η * γ * (1 / η) < η * γ * r :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le hv hvr) hηγ
      linarith
    exact_mod_cast this
  exact absurd (hc2 W hWJ hWw) (not_le.2 hgt)
