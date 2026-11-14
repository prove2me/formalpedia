-- Prove2me | solution 1 for BilateralProfit.proposition_4_7
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T15:23:20.879203+00:00
-- url     : https://prove2.me/submissions/3441d044-10eb-439a-93db-55323c5d195f

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Definitions.Def_BilateralProfit_MWU
import Theorems.Thm_BanditAlgorithm_expWeights_psi_regret


namespace BilateralProfit.MWU47Submission

lemma factor_pos (γ l : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hl : l ∈ Set.Icc (-1 : ℝ) 1) : 0 < 1 - γ * l := by
  have hprod := mul_le_mul_of_nonneg_left hl.2 hγ.le
  linarith

/-- The scalar conversion from exact logarithmic losses to the signed linear losses. -/
lemma neg_log_factor_le (γ l : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hl : l ∈ Set.Icc (-1 : ℝ) 1) :
    -Real.log (1 - γ * l) ≤ γ * l + γ ^ 2 * |l| := by
  have hlabs : |l| ≤ 1 := abs_le.mpr hl
  have hz : |-(γ * l)| ≤ 1 / 2 := by
    rw [abs_neg, abs_mul, abs_of_pos hγ]
    have := mul_le_mul_of_nonneg_left hlabs hγ.le
    linarith
  have hzc : ‖((-(γ * l) : ℝ) : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (hz.trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have hcomplex := Complex.norm_log_one_add_sub_self_le hzc
  have hre := (Complex.abs_re_le_norm
    (Complex.log (1 + ((-(γ * l) : ℝ) : ℂ)) - ((-(γ * l) : ℝ) : ℂ))).trans hcomplex
  have hcast : (1 : ℂ) + ((-(γ * l) : ℝ) : ℂ) = ((1 - γ * l : ℝ) : ℂ) := by push_cast; ring
  rw [hcast] at hre
  have hreal : |Real.log (1 - γ * l) + γ * l| ≤
      |γ * l| ^ 2 * (1 - |γ * l|)⁻¹ / 2 := by
    simpa only [Complex.sub_re, Complex.log_ofReal_re, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, sub_neg_eq_add] using hre
  have habs : |γ * l| ≤ 1 / 2 := by simpa only [abs_neg] using hz
  have hinv : (1 - |γ * l|)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - |γ * l|) (by norm_num : (0 : ℝ) < 2)]
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
    linarith
  have hquad : |Real.log (1 - γ * l) + γ * l| ≤ (γ * l) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hinv (sq_nonneg |γ * l|)
    rw [sq_abs] at hreal hm
    nlinarith
  have hlsq : l ^ 2 ≤ |l| := by
    have hm := mul_nonneg (abs_nonneg l) (sub_nonneg.mpr hlabs)
    rw [mul_sub, mul_one, ← sq, sq_abs] at hm
    linarith
  have hm := mul_le_mul_of_nonneg_left hlsq (sq_nonneg γ)
  nlinarith [(abs_le.mp hquad).1]

noncomputable def logLoss (γ : ℝ) (l : ℝ) : ℝ := -Real.log (1 - γ * l) / γ

lemma exp_neg_logLoss (γ l : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hl : l ∈ Set.Icc (-1 : ℝ) 1) :
    Real.exp (-γ * logLoss γ l) = 1 - γ * l := by
  have heq : -γ * logLoss γ l = Real.log (1 - γ * l) := by
    dsimp [logLoss]
    field_simp
  rw [heq, Real.exp_log (factor_pos γ l hγ hγ1 hl)]

lemma logLoss_le (γ l : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (hl : l ∈ Set.Icc (-1 : ℝ) 1) :
    logLoss γ l ≤ l + γ * |l| := by
  apply (div_le_iff₀ hγ).mpr
  nlinarith [neg_log_factor_le γ l hγ hγ1 hl]

end BilateralProfit.MWU47Submission


namespace BilateralProfit.MWU47Submission

open scoped BigOperators

variable {X : Type} [Fintype X]

lemma exp_sum_logLoss_eq_weight (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ℓ : ℕ → X → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (t : ℕ) (i : X) :
    Real.exp (-(γ * ∑ s ∈ Finset.range t, logLoss γ (ℓ s i))) = mwWeight γ ℓ t i := by
  induction t with
  | zero => simp [mwWeight]
  | succ t ih =>
      rw [Finset.sum_range_succ, mwWeight]
      rw [show -(γ * ((∑ s ∈ Finset.range t, logLoss γ (ℓ s i)) + logLoss γ (ℓ t i))) =
        -(γ * (∑ s ∈ Finset.range t, logLoss γ (ℓ s i))) + -γ * logLoss γ (ℓ t i) by ring]
      rw [Real.exp_add, ih, exp_neg_logLoss γ (ℓ t i) hγ hγ1 (hℓ t i)]

lemma weight_pos (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ℓ : ℕ → X → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (t : ℕ) (i : X) :
    0 < mwWeight γ ℓ t i := by
  rw [← exp_sum_logLoss_eq_weight γ hγ hγ1 ℓ hℓ]
  exact Real.exp_pos _

lemma weight_sum_pos (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ℓ : ℕ → X → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (t : ℕ) (j : X) :
    0 < ∑ i, mwWeight γ ℓ t i := by
  apply Finset.sum_pos'
  · exact fun i _ => (weight_pos γ hγ hγ1 ℓ hℓ t i).le
  · exact ⟨j, Finset.mem_univ _, weight_pos γ hγ hγ1 ℓ hℓ t j⟩

lemma dist_sum_one (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ℓ : ℕ → X → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (t : ℕ) (j : X) :
    ∑ i, mwDist γ ℓ t i = 1 := by
  simp only [mwDist, ← Finset.sum_div]
  exact div_self (weight_sum_pos γ hγ hγ1 ℓ hℓ t j).ne'

lemma reindex_weight {Y : Type} [Fintype Y] (e : Y ≃ X) (γ : ℝ)
    (ℓ : ℕ → X → ℝ) (t : ℕ) (i : Y) :
    mwWeight γ (fun t i => ℓ t (e i)) t i = mwWeight γ ℓ t (e i) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [mwWeight, ih]

lemma reindex_dist {Y : Type} [Fintype Y] (e : Y ≃ X) (γ : ℝ)
    (ℓ : ℕ → X → ℝ) (t : ℕ) (i : Y) :
    mwDist γ (fun t i => ℓ t (e i)) t i = mwDist γ ℓ t (e i) := by
  unfold mwDist
  simp_rw [reindex_weight]
  rw [e.sum_comp]

end BilateralProfit.MWU47Submission


namespace BilateralProfit.MWU47Submission

lemma fin_regret (k : ℕ) (hk : 0 < k) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (T : ℕ) (ℓ : ℕ → Fin k → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (j : Fin k) :
    ∑ t ∈ Finset.range T, ∑ i, mwDist γ ℓ t i * ℓ t i ≤
      ∑ t ∈ Finset.range T, ℓ t j + γ * ∑ t ∈ Finset.range T, |ℓ t j| + Real.log k / γ := by
  let y := fun t i => logLoss γ (ℓ t i)
  let p := fun t i => mwDist γ ℓ t i
  have hlib := BanditAlgorithm.expWeights_psi_regret k T (by omega) γ hγ y j
  dsimp only at hlib
  have hexp (t : ℕ) (i : Fin k) :
      Real.exp (-(γ * ∑ s ∈ Finset.range t, y s i)) = mwWeight γ ℓ t i :=
    exp_sum_logLoss_eq_weight γ hγ hγ1 ℓ hℓ t i
  have hfac (t : ℕ) (i : Fin k) : Real.exp (-γ * y t i) = 1 - γ * ℓ t i :=
    exp_neg_logLoss γ (ℓ t i) hγ hγ1 (hℓ t i)
  simp_rw [hexp, hfac] at hlib
  change (∑ t ∈ Finset.range T, ∑ i, p t i * (y t i - y t j)) ≤
    Real.log k / γ + (1 / γ) *
      ∑ t ∈ Finset.range T, ∑ i, p t i * ((1 - γ * ℓ t i) + γ * y t i - 1) at hlib
  have hpsum (t : ℕ) : ∑ i, p t i = 1 := dist_sum_one γ hγ hγ1 ℓ hℓ t j
  have hleft : (∑ t ∈ Finset.range T, ∑ i, p t i * (y t i - y t j)) =
      (∑ t ∈ Finset.range T, ∑ i, p t i * y t i) - ∑ t ∈ Finset.range T, y t j := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.sum_mul, hpsum, one_mul]
  have hright : (∑ t ∈ Finset.range T, ∑ i, p t i * ((1 - γ * ℓ t i) + γ * y t i - 1)) =
      γ * ((∑ t ∈ Finset.range T, ∑ i, p t i * y t i) -
        ∑ t ∈ Finset.range T, ∑ i, p t i * ℓ t i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright] at hlib
  have hcancel : (1 / γ) * (γ *
      ((∑ t ∈ Finset.range T, ∑ i, p t i * y t i) -
        ∑ t ∈ Finset.range T, ∑ i, p t i * ℓ t i)) =
      (∑ t ∈ Finset.range T, ∑ i, p t i * y t i) -
        ∑ t ∈ Finset.range T, ∑ i, p t i * ℓ t i := by field_simp
  rw [hcancel] at hlib
  have hcore : (∑ t ∈ Finset.range T, ∑ i, p t i * ℓ t i) ≤
      ∑ t ∈ Finset.range T, y t j + Real.log k / γ := by linarith
  have hcomp : (∑ t ∈ Finset.range T, y t j) ≤
      (∑ t ∈ Finset.range T, ℓ t j) + γ * ∑ t ∈ Finset.range T, |ℓ t j| := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun t _ => logLoss_le γ (ℓ t j) hγ hγ1 (hℓ t j))
  linarith

end BilateralProfit.MWU47Submission

namespace BilateralProfit

theorem submission_proposition_4_7 {X : Type} [Fintype X] (γ : ℝ) (hγ : 0 < γ)
    (hγ' : γ ≤ 1 / 2) (T : ℕ) (ℓ : ℕ → X → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (j : X) :
    ∑ t ∈ Finset.range T, ∑ i, mwDist γ ℓ t i * ℓ t i ≤
      ∑ t ∈ Finset.range T, ℓ t j + γ * ∑ t ∈ Finset.range T, |ℓ t j| +
        Real.log (Fintype.card X) / γ := by
  classical
  let e := (Fintype.equivFin X).symm
  let ℓ' := fun t i => ℓ t (e i)
  have hk : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨j⟩
  have hfin := MWU47Submission.fin_regret (Fintype.card X) hk γ hγ hγ' T ℓ'
    (fun t i => hℓ t (e i)) (e.symm j)
  have hround (t : ℕ) : (∑ i, mwDist γ ℓ' t i * ℓ' t i) =
      ∑ i, mwDist γ ℓ t i * ℓ t i := by
    dsimp only [ℓ']
    simp_rw [MWU47Submission.reindex_dist]
    exact e.sum_comp (fun i : X => mwDist γ ℓ t i * ℓ t i)
  simp_rw [hround] at hfin
  simpa only [ℓ', e.apply_symm_apply] using hfin

end BilateralProfit
open BilateralProfit

theorem solution {X : Type} [Fintype X] (γ : ℝ) (hγ : 0 < γ)
    (hγ' : γ ≤ 1 / 2) (T : ℕ) (ℓ : ℕ → X → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (-1 : ℝ) 1) (j : X) :
    ∑ t ∈ Finset.range T, ∑ i, mwDist γ ℓ t i * ℓ t i ≤
      ∑ t ∈ Finset.range T, ℓ t j + γ * ∑ t ∈ Finset.range T, |ℓ t j| +
        Real.log (Fintype.card X) / γ := by
  exact BilateralProfit.submission_proposition_4_7 γ hγ hγ' T ℓ hℓ j
