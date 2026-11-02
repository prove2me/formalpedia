-- Prove2me | solution 1 for DataMerger.Quality.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:14:26.17587+00:00
-- url     : https://prove2.me/submissions/71242078-c9da-44a9-bc26-91ced35dfe79

import Mathlib
import Definitions.Def_DataMerger_Quality_Model
import Theorems.Thm_DataMerger_Quality_data_comparison
import Theorems.Thm_DataMerger_Quality_exclusivity

open DataMerger.Quality

lemma dmp_int1 (c q u w : ℝ) :
    ∫ x in u..w, (c - x - q) = (c - q) * (w - u) - (w ^ 2 - u ^ 2) / 2 := by
  have hd : ∀ x ∈ Set.uIcc u w,
      HasDerivAt (fun x : ℝ => (c - q) * x - x ^ 2 / 2) (c - x - q) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul (c - q)).sub ((hasDerivAt_pow 2 x).div_const 2)
    refine this.congr_deriv ?_
    simp; ring
  have hint : IntervalIntegrable (fun x : ℝ => c - x - q) MeasureTheory.volume u w :=
    ((continuous_const.sub continuous_id).sub continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

lemma dmp_int2 (c q u w : ℝ) :
    ∫ x in u..w, (c - (1 - x) - q) = (c - 1 - q) * (w - u) + (w ^ 2 - u ^ 2) / 2 := by
  have hd : ∀ x ∈ Set.uIcc u w,
      HasDerivAt (fun x : ℝ => (c - 1 - q) * x + x ^ 2 / 2) (c - (1 - x) - q) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul (c - 1 - q)).add ((hasDerivAt_pow 2 x).div_const 2)
    refine this.congr_deriv ?_
    simp; ring
  have hint : IntervalIntegrable (fun x : ℝ => c - (1 - x) - q) MeasureTheory.volume u w :=
    ((continuous_const.sub (continuous_const.sub continuous_id)).sub
      continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

/-- Closed form of B-market consumer surplus when the rival holds no data. -/
lemma dmp_UB_closed (V : ℝ → ℝ) (d : ℝ) :
    UB V d 0 = V 0 - 5 / 4 + (V d - V 0) / 2 + (V d - V 0) ^ 2 / 36 := by
  unfold UB
  simp only []
  rw [dmp_int1, dmp_int2]
  unfold DB pB
  ring

/-- Consumer surplus in market A below the choke price. -/
lemma dmp_CSA (alpha p : ℝ) (hp : p ≤ alpha) : DataMerger.Quality.CSA alpha p = (alpha - p) ^ 2 / 2 := by
  unfold DataMerger.Quality.CSA
  have hcongr : Set.EqOn (fun s => DA alpha s) (fun s => alpha - 0 - s - 0) (Set.uIcc p alpha) := by
    intro s hs
    rw [Set.uIcc_of_le hp] at hs
    simp only [DA]
    rw [max_eq_left (by linarith [hs.2])]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  have := dmp_int1 alpha 0 p alpha
  simp only [sub_zero] at this ⊢
  rw [this]
  ring

lemma dmp_DA_nonneg (alpha p : ℝ) : 0 ≤ DA alpha p := le_max_right _ _

lemma dmp_pDA (alpha p : ℝ) : p * DA alpha p = (alpha - DA alpha p) * DA alpha p := by
  unfold DA
  rcases le_total (alpha - p) 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h]; ring

lemma dmp_DA_sub (alpha d : ℝ) (hd : 0 ≤ d) : DA alpha (alpha - d) = d := by
  unfold DA
  rw [max_eq_left (by linarith)]
  ring

lemma dmp_objI (alpha : ℝ) (V : ℝ → ℝ) (p : ℝ) :
    objI alpha V p = (alpha - DA alpha p) * DA alpha p + piB V (DA alpha p) 0 -
      piB V 0 (DA alpha p) := by
  unfold objI
  rw [dmp_pDA, max_eq_left]
  · unfold T1; ring
  · unfold T1 T2 piB
    nlinarith [sq_nonneg (V (DA alpha p) - V 0)]

lemma dmp_objM (alpha : ℝ) (V : ℝ → ℝ) (p : ℝ) :
    objM alpha V p = (alpha - DA alpha p) * DA alpha p + piB V (DA alpha p) 0 := by
  unfold objM
  rw [dmp_pDA, max_eq_left]
  unfold T2 piB
  nlinarith [sq_nonneg (V (DA alpha p) - V 0)]

theorem solution (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (pI pM : ℝ) (hI : ∀ p, objI alpha V p ≤ objI alpha V pI)
    (hM : ∀ p, objM alpha V p ≤ objM alpha V pM) :
    let aI := allocI (piB V) (DA alpha pI)
    let aM := allocM (piB V) (DA alpha pM)
    pI < pM ∧
      qaPrice V aI.1 aI.2 < qaPrice V aM.1 aM.2 ∧
      qaPrice V aI.2 aI.1 < qaPrice V aM.2 aM.1 ∧
      DataMerger.Quality.CSA alpha pM < DataMerger.Quality.CSA alpha pI ∧
      UB V aM.1 aM.2 < UB V aI.1 aI.2 := by
  intro aI aM
  have hS' := hS
  obtain ⟨halpha, hV, hV', hV3, _⟩ := hS'
  have hmono : StrictMonoOn V (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hV.continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hV' x (le_of_lt hx)
  -- reduce to the data-level comparison
  have hdc := data_comparison alpha V hS (DA alpha pI) (DA alpha pM)
    (dmp_DA_nonneg _ _) (dmp_DA_nonneg _ _)
    (fun d hd => by
      have := hI (alpha - d)
      rw [dmp_objI, dmp_objI, dmp_DA_sub alpha d hd] at this
      exact this)
    (fun d hd => by
      have := hM (alpha - d)
      rw [dmp_objM, dmp_objM, dmp_DA_sub alpha d hd] at this
      exact this)
  obtain ⟨hMpos, hMI, _⟩ := hdc
  set dI := DA alpha pI with hdI
  set dM := DA alpha pM with hdM
  have hIpos : 0 < dI := lt_trans hMpos hMI
  have hpI : pI < alpha := by
    by_contra h
    push Not at h
    have : dI = 0 := by rw [hdI]; unfold DA; exact max_eq_right (by linarith)
    linarith
  have hpM : pM < alpha := by
    by_contra h
    push Not at h
    have : dM = 0 := by rw [hdM]; unfold DA; exact max_eq_right (by linarith)
    linarith
  have hdIe : dI = alpha - pI := by rw [hdI]; unfold DA; exact max_eq_left (by linarith)
  have hdMe : dM = alpha - pM := by rw [hdM]; unfold DA; exact max_eq_left (by linarith)
  have haI : aI = (dI, 0) := by
    show allocI (piB V) dI = (dI, 0)
    unfold allocI
    rw [if_pos (exclusivity alpha V hS dI hIpos).1]
  have haM : aM = (dM, 0) := by
    show allocM (piB V) dM = (dM, 0)
    unfold allocM
    rw [if_pos (exclusivity alpha V hS dM hMpos).2]
  rw [haI, haM]
  simp only []
  have hVlt : V dM < V dI := hmono (le_of_lt hMpos) (le_of_lt hIpos) hMI
  have hV0 : V 0 < V dM := hmono Set.self_mem_Ici (le_of_lt hMpos) hMpos
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · unfold qaPrice pB; linarith
  · unfold qaPrice pB; linarith
  · rw [dmp_CSA alpha pM hpM.le, dmp_CSA alpha pI hpI.le, ← hdIe, ← hdMe]
    nlinarith
  · rw [dmp_UB_closed, dmp_UB_closed]
    nlinarith [mul_pos (sub_pos.mpr hVlt) (sub_pos.mpr hV0)]
