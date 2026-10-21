-- Prove2me | solution 1 for BudgetedAffine.Budget.claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:33:13.189447+00:00
-- url     : https://prove2.me/submissions/b4adce67-c98a-4626-9bab-ed305f07a8b3

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction
import Definitions.Def_BudgetedAffine_Budget_Rescaling

set_option autoImplicit false
open Matrix BudgetedAffine.Budget

theorem ereal_cancel' (c : ℝ) (hc : 0 < c) (a : EReal) :
    ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * a) = a := by
  induction a using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc, EReal.coe_mul_bot_of_pos (inv_pos.2 hc)]
  | top =>
    rw [EReal.coe_mul_top_of_pos hc, EReal.coe_mul_top_of_pos (inv_pos.2 hc)]
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    congr 1
    field_simp

theorem ereal_mul_iInf' (κ : ℝ) (hκ : 0 < κ) {ι : Sort*} (f : ι → EReal) :
    (κ : EReal) * ⨅ i, f i = ⨅ i, (κ : EReal) * f i := by
  apply le_antisymm
  · exact le_iInf fun i => mul_le_mul_of_nonneg_left (iInf_le f i) (by exact_mod_cast hκ.le)
  · have h1 : ((κ⁻¹ : ℝ) : EReal) * (⨅ i, (κ : EReal) * f i) ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc ((κ⁻¹ : ℝ) : EReal) * (⨅ i, (κ : EReal) * f i)
          ≤ ((κ⁻¹ : ℝ) : EReal) * ((κ : EReal) * f i) :=
            mul_le_mul_of_nonneg_left (iInf_le _ i) (by exact_mod_cast (inv_pos.2 hκ).le)
        _ = f i := ereal_cancel' κ hκ _
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0:EReal) ≤ (κ : EReal) by exact_mod_cast hκ.le)
    have h3 : (κ : EReal) * (((κ⁻¹ : ℝ) : EReal) * (⨅ i, (κ : EReal) * f i)) =
        ⨅ i, (κ : EReal) * f i := by
      have := ereal_cancel' (κ⁻¹) (inv_pos.2 hκ) (⨅ i, (κ : EReal) * f i)
      rw [inv_inv] at this
      exact this
    rw [h3] at h2
    exact h2

theorem beta_pos' (n : ℕ) (hn : 3 ≤ n) : 0 < beta n := by
  unfold beta
  have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have : 0 < Real.log (Real.log n) := Real.log_pos hlog
  have : 0 < Real.log n := by linarith
  positivity

theorem colMax_nonneg' {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (j : Fin n) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i ∈ J, 0 < w i) :
    0 ≤ colMax B w J j := by
  unfold colMax
  exact Real.iSup_nonneg (fun k => mul_nonneg (hw k k.2).le (hB _ _))

theorem le_colMax' {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (j : Fin n) (i : Fin m) (hi : i ∈ J) :
    w i * B i j ≤ colMax B w J j := by
  unfold colMax
  exact le_ciSup (f := fun k : J => w k * B k j) (Finite.bddAbove_range _) ⟨i, hi⟩

theorem BHat_nonneg' {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i ∈ J, 0 < w i) (i : Fin m) (j : Fin n) :
    0 ≤ BHat B w J i j := by
  unfold BHat
  simp only [Matrix.of_apply]
  split_ifs with h
  · exact div_nonneg (mul_nonneg (hw i h).le (hB _ _)) (colMax_nonneg' B w J j hB hw)
  · exact le_rfl

theorem colMax_zero' {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (w : Fin m → ℝ)
    (J : Finset (Fin m)) (hB : ∀ i j, 0 ≤ B i j) (hw : ∀ i ∈ J, 0 < w i) (i : Fin m)
    (hi : i ∈ J) (j : Fin n) (h0 : colMax B w J j = 0) : B i j = 0 := by
  have h1 := le_colMax' B w J j i hi
  rw [h0] at h1
  have := hw i hi
  have h2 := hB i j
  by_contra hne
  have : 0 < B i j := lt_of_le_of_ne h2 (Ne.symm hne)
  nlinarith

theorem fwd' {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) (J : Finset (Fin m))
    (w : Fin m → ℝ) (η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (hw : ∀ i ∈ J, 0 < w i)
    (W : Finset (Fin m)) (hW : W ⊆ J) (y : Fin n → ℝ) (hy : 0 ≤ y ∧ indic W ≤ B *ᵥ y) :
    0 ≤ (fun j => colMax B w J j * y j) ∧
    wIndic w W ≤ BHat B w J *ᵥ (fun j => colMax B w J j * y j) ∧
    η * γ * (dHat B d w J η γ ⬝ᵥ (fun j => colMax B w J j * y j)) ≤ d ⬝ᵥ y := by
  obtain ⟨hy0, hyB⟩ := hy
  have hM := fun j => colMax_nonneg' B w J j hB hw
  refine ⟨fun j => mul_nonneg (hM j) (hy0 j), ?_, ?_⟩
  · intro i
    by_cases hiW : i ∈ W
    · have hiJ := hW hiW
      have hterm : ∀ j, BHat B w J i j * (colMax B w J j * y j) = w i * (B i j * y j) := by
        intro j
        by_cases h0 : colMax B w J j = 0
        · rw [colMax_zero' B w J hB hw i hiJ j h0]; simp [h0]
        · simp only [BHat, Matrix.of_apply, if_pos hiJ]
          field_simp
      have : (BHat B w J *ᵥ (fun j => colMax B w J j * y j)) i = w i * (B *ᵥ y) i := by
        simp only [mulVec, dotProduct, hterm, Finset.mul_sum]
      rw [this]
      have h1 : indic W i ≤ (B *ᵥ y) i := hyB i
      have h2 : indic W i = 1 := by simp [indic, hiW]
      have h3 : wIndic w W i = w i := by simp [wIndic, hiW]
      rw [h3]
      have := hw i hiJ
      nlinarith
    · have h3 : wIndic w W i = 0 := by simp [wIndic, hiW]
      rw [h3]
      simp only [mulVec, dotProduct]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (BHat_nonneg' B w J hB hw i j)
        (mul_nonneg (hM j) (hy0 j)))
  · simp only [dotProduct, dHat, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases h0 : colMax B w J j = 0
    · simp [h0]
      exact mul_nonneg (hd j) (hy0 j)
    · have : η * γ * (d j / (η * γ * colMax B w J j) * (colMax B w J j * y j)) = d j * y j := by
        field_simp
      rw [this]

theorem bwd' {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ) (J : Finset (Fin m))
    (w : Fin m → ℝ) (η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (hw : ∀ i ∈ J, 0 < w i)
    (W : Finset (Fin m)) (hW : W ⊆ J) (yh : Fin n → ℝ)
    (hy : 0 ≤ yh ∧ wIndic w W ≤ BHat B w J *ᵥ yh) :
    0 ≤ (fun j => yh j / colMax B w J j) ∧
    indic W ≤ B *ᵥ (fun j => yh j / colMax B w J j) ∧
    d ⬝ᵥ (fun j => yh j / colMax B w J j) = η * γ * (dHat B d w J η γ ⬝ᵥ yh) := by
  obtain ⟨hy0, hyB⟩ := hy
  have hM := fun j => colMax_nonneg' B w J j hB hw
  refine ⟨fun j => div_nonneg (hy0 j) (hM j), ?_, ?_⟩
  · intro i
    by_cases hiW : i ∈ W
    · have hiJ := hW hiW
      have hterm : ∀ j, BHat B w J i j * yh j = w i * (B i j * (yh j / colMax B w J j)) := by
        intro j
        simp only [BHat, Matrix.of_apply, if_pos hiJ]
        ring
      have h1 := hyB i
      have h3 : wIndic w W i = w i := by simp [wIndic, hiW]
      have : (BHat B w J *ᵥ yh) i = w i * (B *ᵥ (fun j => yh j / colMax B w J j)) i := by
        simp only [mulVec, dotProduct, hterm, Finset.mul_sum]
      rw [this, h3] at h1
      have h2 : indic W i = 1 := by simp [indic, hiW]
      rw [h2]
      have := hw i hiJ
      by_contra hlt
      push Not at hlt
      nlinarith
    · have h2 : indic W i = 0 := by simp [indic, hiW]
      rw [h2]
      simp only [mulVec, dotProduct]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hB i j) (div_nonneg (hy0 j) (hM j)))
  · simp only [dotProduct, dHat, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h0 : colMax B w J j = 0
    · simp [h0]
    · field_simp

theorem solution {m n : ℕ} (hn : 3 ≤ n) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hd : 0 ≤ d) (hγ : 0 < γ) (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1)
    (W : Finset (Fin m)) (hW : W ⊆ J) :
    coverCost B d (indic W) =
      ((beta n * γ : ℝ) : EReal) *
        coverCost (BHat B w J) (dHat B d w J (beta n) γ) (wIndic w W) := by
  have hη := beta_pos' n hn
  have hκ : 0 < beta n * γ := mul_pos hη hγ
  have hw' : ∀ i ∈ J, 0 < w i := fun i hi => (hw i hi).1
  unfold coverCost
  rw [ereal_mul_iInf' _ hκ]
  simp only [ereal_mul_iInf' _ hκ]
  apply le_antisymm
  · refine le_iInf fun yh => le_iInf fun hyh => ?_
    obtain ⟨h0, h1, h2⟩ := bwd' B d J w (beta n) γ hη hγ hB hd hw' W hW yh hyh
    refine le_trans (iInf₂_le (fun j => yh j / colMax B w J j) ⟨h0, h1⟩) ?_
    rw [h2, ← EReal.coe_mul]
  · refine le_iInf fun y => le_iInf fun hy => ?_
    obtain ⟨h0, h1, h2⟩ := fwd' B d J w (beta n) γ hη hγ hB hd hw' W hW y hy
    refine le_trans (iInf₂_le (fun j => colMax B w J j * y j) ⟨h0, h1⟩) ?_
    rw [← EReal.coe_mul]
    exact_mod_cast h2
