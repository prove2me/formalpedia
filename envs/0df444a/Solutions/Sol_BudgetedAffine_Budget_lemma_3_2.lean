-- Prove2me | solution 1 for BudgetedAffine.Budget.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:33:11.937004+00:00
-- url     : https://prove2.me/submissions/fcc01bdc-4697-4611-9fc0-e4885bb56260

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_BudgetedAffine_Budget_Construction

set_option autoImplicit false
open Matrix BudgetedAffine.Budget

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

theorem dot_yLin' {m n : ℕ} (d : Fin n → ℝ) (I : Finset (Fin m)) (α : Fin m → ℝ)
    (v : Fin m → Fin n → ℝ) (h : Fin m → ℝ) :
    d ⬝ᵥ yLin I α v h = ∑ i ∈ I, (α i * h i) * (d ⬝ᵥ v i) := by
  simp only [yLin, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem solution {m n : ℕ} (hn : 3 ≤ n) (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (w : Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : IsOptimalAR A B c d X (budgetSet w) xs ys)
    (OPT : ℝ) (hOPT : zAR A B c d X (budgetSet w) = (OPT : EReal))
    (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d w xs OPT, IsCoverOpt B d (Pi.single i 1) (v i)) :
    ∀ h ∈ budgetSet w, d ⬝ᵥ yLin (Iset A B d w xs OPT) (alpha A xs) v h ≤ beta n * OPT := by
  intro h hh
  obtain ⟨hh01, hhsum⟩ := hh
  set I := Iset A B d w xs OPT with hI
  have hβ := beta_pos' n hn
  -- OPT ≥ 0
  have hOPT0 : 0 ≤ OPT := by
    obtain ⟨hfeas, hwc⟩ := hopt
    have h0 : (0 : Fin m → ℝ) ∈ budgetSet w := by
      refine ⟨fun i => ⟨le_rfl, zero_le_one⟩, ?_⟩
      simp
    have hys0 := (hfeas.2 0 h0).1
    have hge : (((c ⬝ᵥ xs + d ⬝ᵥ ys 0 : ℝ)) : EReal) ≤ worstCost c d (budgetSet w) xs ys := by
      unfold worstCost
      exact le_iSup₂_of_le 0 h0 le_rfl
    rw [hwc, hOPT] at hge
    have hge' : c ⬝ᵥ xs + d ⬝ᵥ ys 0 ≤ OPT := by exact_mod_cast hge
    have h1 : 0 ≤ c ⬝ᵥ xs := hcX xs hfeas.1
    have h2 : 0 ≤ d ⬝ᵥ ys 0 := dotProduct_nonneg_of_nonneg hd hys0
    linarith
  have hβO : 0 ≤ beta n * OPT := mul_nonneg hβ.le hOPT0
  have hkey : ∀ i ∈ I, alpha A xs i * (d ⬝ᵥ v i) ≤ w i * beta n * OPT := by
    intro i hi
    have h1 := (Finset.mem_filter.1 hi).2.2
    have h2 := (hv i hi).2.2
    rw [← h2] at h1
    rw [← EReal.coe_mul] at h1
    exact_mod_cast h1
  rw [dot_yLin']
  calc ∑ i ∈ I, (alpha A xs i * h i) * (d ⬝ᵥ v i)
      ≤ ∑ i ∈ I, h i * (w i * beta n * OPT) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have := mul_le_mul_of_nonneg_left (hkey i hi) (hh01 i).1
        linarith
    _ ≤ ∑ i, h i * (w i * beta n * OPT) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => ?_)
        exact mul_nonneg (hh01 i).1 (mul_nonneg (mul_nonneg (hw i).1 hβ.le) hOPT0)
    _ = beta n * OPT * ∑ i, w i * h i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ beta n * OPT * 1 := mul_le_mul_of_nonneg_left hhsum hβO
    _ = beta n * OPT := by ring
