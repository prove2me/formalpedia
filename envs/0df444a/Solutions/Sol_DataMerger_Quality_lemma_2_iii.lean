-- Prove2me | solution 1 for DataMerger.Quality.lemma_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:15:11.703123+00:00
-- url     : https://prove2.me/submissions/080d6e1a-c27c-423f-a412-711afac1ae63

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

open DataMerger.Quality

lemma dm3_int1 (c q u w : ℝ) :
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

lemma dm3_int2 (c q u w : ℝ) :
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

/-- Closed form of B-market consumer surplus. -/
lemma dm3_UB_closed (V : ℝ → ℝ) (d1 d2 : ℝ) :
    UB V d1 d2 = (V d1 + V d2) / 2 - 5 / 4 + (V d1 - V d2) ^ 2 / 36 := by
  unfold UB
  simp only []
  rw [dm3_int1, dm3_int2]
  unfold DB pB
  ring

theorem solution (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (d1 d2 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) :
    0 < deriv (fun x => UB V x d2) d1 ∧
      0 < deriv (fun x => UB V d1 x) d2 := by
  obtain ⟨_, hV, hV', hV3, _⟩ := hS
  have hmono : StrictMonoOn V (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hV.continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    exact hV' x (le_of_lt hx)
  have h01 : V 0 ≤ V d1 := hmono.monotoneOn Set.self_mem_Ici hd1 hd1
  have h02 : V 0 ≤ V d2 := hmono.monotoneOn Set.self_mem_Ici hd2 hd2
  have h31 := hV3 d1 hd1
  have h32 := hV3 d2 hd2
  have p1 := hV' d1 hd1
  have p2 := hV' d2 hd2
  constructor
  · have hf : (fun x => UB V x d2) =
        fun x => (V x + V d2) / 2 - 5 / 4 + (V x - V d2) ^ 2 / 36 := by
      funext x; exact dm3_UB_closed V x d2
    have hD : HasDerivAt (fun x => (V x + V d2) / 2 - 5 / 4 + (V x - V d2) ^ 2 / 36)
        (deriv V d1 * (1 / 2 + (V d1 - V d2) / 18)) d1 := by
      have hv := (hV d1).hasDerivAt
      have := ((((hv.add_const (V d2)).div_const 2).sub_const (5 / 4)).add
        (((hv.sub_const (V d2)).pow 2).div_const 36))
      refine this.congr_deriv ?_
      norm_num; ring
    rw [hf, hD.deriv]
    apply mul_pos p1
    linarith
  · have hf : (fun x => UB V d1 x) =
        fun x => (V d1 + V x) / 2 - 5 / 4 + (V d1 - V x) ^ 2 / 36 := by
      funext x; exact dm3_UB_closed V d1 x
    have hD : HasDerivAt (fun x => (V d1 + V x) / 2 - 5 / 4 + (V d1 - V x) ^ 2 / 36)
        (deriv V d2 * (1 / 2 - (V d1 - V d2) / 18)) d2 := by
      have hv := (hV d2).hasDerivAt
      have := ((((hv.const_add (V d1)).div_const 2).sub_const (5 / 4)).add
        (((hv.const_sub (V d1)).pow 2).div_const 36))
      refine this.congr_deriv ?_
      norm_num; ring
    rw [hf, hD.deriv]
    apply mul_pos p2
    linarith
