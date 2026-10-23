-- Prove2me | solution 1 for DRMeanVar.Reform.thm1_proof_display_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:31:26.987514+00:00
-- url     : https://prove2.me/submissions/d3e9dc42-da57-4e48-a687-776a40bf8372

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

theorem empVar_eq_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    empVar R φ = empSecond R φ - (empMean R φ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  unfold empVar empSecond
  have hm : ∑ i, φ ⬝ᵥ R i = n * empMean R φ := by
    unfold empMean; field_simp
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem empVar_nonneg_aux {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    0 ≤ empVar R φ := by
  unfold empVar
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem hFun_sub_sq_aux {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (p : ENNReal) (δ α : ℝ) (φ : Fin d → ℝ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    hFun p δ R α φ - α ^ 2 =
      (Real.sqrt (empVar R φ) +
        Real.sqrt (δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2)) ^ 2 := by
  have hV := empVar_nonneg_aux R φ
  have hD : 0 ≤ δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2 := by linarith
  have hvar := empVar_eq_aux R φ
  unfold hFun
  rw [add_sq, Real.sq_sqrt hV, Real.sq_sqrt hD]
  rw [hvar]
  ring

instance Pn_isProb_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ)) :
    IsProbabilityMeasure (Pn R) := by
  constructor
  have hn : (n : ENNReal) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp [Pn, Measure.coe_finsetSum, Finset.sum_apply]
  exact ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top n)

theorem integral_Pn_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) :
    ∫ x, f x ∂(Pn R) = (n : ℝ)⁻¹ * ∑ i, f (R i) := by
  unfold Pn
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, smul_eq_mul, ENNReal.toReal_inv]
  · intro i _; exact integrable_dirac (by simp)

theorem Pn_mem_U_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ)) (q : ENNReal) (δ : ℝ)
    (hq : 1 ≤ q) :
    Pn R ∈ U q δ R := by
  refine ⟨inferInstance, ?_⟩
  unfold RWPI.SqrtLasso.transportCost
  refine le_trans (iInf₂_le ((Pn R).map (fun x => (x, x))) ?_) ?_
  · refine ⟨Measure.isProbabilityMeasure_map (by fun_prop), ?_, ?_⟩
    · rw [Measure.map_map (by fun_prop) (by fun_prop)]; exact Measure.map_id
    · rw [Measure.map_map (by fun_prop) (by fun_prop)]; exact Measure.map_id
  · refine le_trans (lintegral_map_le _ _) ?_
    haveI : Fact (1 ≤ q) := ⟨hq⟩
    simp [lqSqCost]

end DRMeanVar.Reform

open DRMeanVar.Reform in
theorem solution {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (q p : ENNReal) (δ αbar : ℝ)
    (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) (hφ : φ ∈ F q δ αbar R) :
    IsGreatest ((fun α => hFun p δ R α φ - α ^ 2) ''
      {α : ℝ | αbar ≤ α ∧ (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0})
      (dualObj p δ R φ) ∧
    αbar ≤ empMean R φ ∧
    hFun p δ R (empMean R φ) φ - (empMean R φ) ^ 2 = dualObj p δ R φ := by
  have hmean : αbar ≤ empMean R φ := by
    have h := hφ.2 (Pn R) (Pn_mem_U_aux R q δ hq)
    unfold pMean at h
    rw [integral_Pn_aux] at h
    exact h
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  have hN : 0 ≤ ‖WithLp.toLp p φ‖ := norm_nonneg _
  have hsq : Real.sqrt (δ * ‖WithLp.toLp p φ‖ ^ 2) = Real.sqrt δ * ‖WithLp.toLp p φ‖ := by
    rw [Real.sqrt_mul hδ, Real.sqrt_sq hN]
  have hat : hFun p δ R (empMean R φ) φ - (empMean R φ) ^ 2 = dualObj p δ R φ := by
    rw [hFun_sub_sq_aux R p δ _ φ (by simp; positivity)]
    unfold dualObj
    simp [hsq]
  refine ⟨⟨⟨empMean R φ, ⟨hmean, by simp; positivity⟩, hat⟩, ?_⟩, hmean, hat⟩
  rintro v ⟨α, ⟨_, hα⟩, rfl⟩
  simp only
  rw [hFun_sub_sq_aux R p δ α φ hα]
  unfold dualObj
  have h1 : Real.sqrt (δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2) ≤
      Real.sqrt δ * ‖WithLp.toLp p φ‖ := by
    rw [← hsq]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (α - empMean R φ)])
  have h0 := Real.sqrt_nonneg (δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2)
  have hV := Real.sqrt_nonneg (empVar R φ)
  nlinarith
