-- Prove2me | solution 1 for DurrettProbability.brownian_nowhere_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:14:09.100517+00:00
-- url     : https://prove2.me/submissions/86920ce2-2f37-42bc-8aff-bb2e93aa25c3

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace DurrettProbability

theorem AuxNL_ball {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    gaussianReal 0 v (Metric.closedBall 0 r) ≤ ENNReal.ofReal (2 * r / Real.sqrt v) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv'
  rw [gaussianReal_apply _ hv]
  calc ∫⁻ x in Metric.closedBall 0 r, gaussianPDF 0 v x
      ≤ ∫⁻ x in Metric.closedBall (0 : ℝ) r, ENNReal.ofReal (Real.sqrt v)⁻¹ := by
        refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun x _ => ?_
        rw [gaussianPDF_def]
        apply ENNReal.ofReal_le_ofReal
        rw [gaussianPDFReal_def]
        have h1 : Real.sqrt v ≤ Real.sqrt (2 * Real.pi * v) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
        have h2 : (Real.sqrt (2 * Real.pi * v))⁻¹ ≤ (Real.sqrt v)⁻¹ := inv_anti₀ hs h1
        have h3 : Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ (x - 0) ^ 2 / (2 * (v : ℝ)) := by positivity
          rw [neg_div]; linarith
        calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * v))
            ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ ≤ (Real.sqrt v)⁻¹ := by rw [mul_one]; exact h2
    _ = ENNReal.ofReal (2 * r / Real.sqrt v) := by
        rw [setLIntegral_const, Real.volume_closedBall, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp

theorem AuxNL_null {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (K L : ℕ) :
    P {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ L ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, |(t : ℝ) - s| ≤ δ →
      |B t ω - B s ω| ≤ K * |(t : ℝ) - s|} = 0 := by
  set tn : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) / (n : ℝ≥0) with htn
  set Δ : ℕ → ℕ → Ω → ℝ := fun n k ω => B (tn n (k + 1)) ω - B (tn n k) ω with hΔ
  set c : ℝ := 8 * K with hc
  have hc0 : 0 ≤ c := by positivity
  set E : ℕ → Set Ω := fun n => ⋃ i ∈ Finset.range ((L + 1) * n),
    ⋂ k ∈ Finset.Ico i (i + 3), Δ n k ⁻¹' Metric.closedBall 0 (c / n) with hE
  have htnr : ∀ n k, (tn n k : ℝ) = k / n := fun n k => by simp [htn]
  have hind : ∀ n, iIndepFun (Δ n) P := fun n =>
    hB.hasIndepIncrements.nat (t := tn n) (fun a b h => by
      simp only [htn]; gcongr)
  have hlaw : ∀ n, 0 < n → ∀ k, P (Δ n k ⁻¹' Metric.closedBall 0 (c / n))
      ≤ ENNReal.ofReal (2 * (c / n) * Real.sqrt n) := by
    intro n hn k
    have h : HasLaw (Δ n k) (gaussianReal 0 (nndist (tn n (k + 1) : ℝ) (tn n k : ℝ))) P :=
      hB.hasLaw_sub _ _
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hv : ((nndist (tn n (k + 1) : ℝ) (tn n k : ℝ) : ℝ≥0) : ℝ) = 1 / n := by
      rw [coe_nndist, Real.dist_eq, htnr, htnr]
      rw [show ((k + 1 : ℕ) : ℝ) / n - k / n = 1 / n by push_cast; field_simp; ring]
      exact abs_of_pos (by positivity)
    have hv0 : nndist (tn n (k + 1) : ℝ) (tn n k : ℝ) ≠ 0 := by
      intro h0; rw [h0] at hv; simp at hv; linarith
    rw [← Measure.map_apply_of_aemeasurable h.aemeasurable Metric.isClosed_closedBall.measurableSet,
      h.map_eq]
    refine (AuxNL_ball hv0 (by positivity)).trans (le_of_eq ?_)
    congr 1
    rw [hv, Real.sqrt_div' 1 hn'.le, Real.sqrt_one, div_div_eq_mul_div, div_one]
  have hEle : ∀ n, 0 < n → P (E n) ≤
      ENNReal.ofReal (((L + 1) * n : ℕ) * (2 * (c / n) * Real.sqrt n) ^ 3) := by
    intro n hn
    calc P (E n) ≤ ∑ i ∈ Finset.range ((L + 1) * n),
          P (⋂ k ∈ Finset.Ico i (i + 3), Δ n k ⁻¹' Metric.closedBall 0 (c / n)) :=
          measure_biUnion_finset_le _ _
      _ = ∑ i ∈ Finset.range ((L + 1) * n),
          ∏ k ∈ Finset.Ico i (i + 3), P (Δ n k ⁻¹' Metric.closedBall 0 (c / n)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (hind n).measure_inter_preimage_eq_mul _
            (fun _ _ => Metric.isClosed_closedBall.measurableSet)
      _ ≤ ∑ i ∈ Finset.range ((L + 1) * n),
          ∏ k ∈ Finset.Ico i (i + 3), ENNReal.ofReal (2 * (c / n) * Real.sqrt n) := by
          gcongr with i hi k hk
          exact hlaw n hn k
      _ = ENNReal.ofReal (((L + 1) * n : ℕ) * (2 * (c / n) * Real.sqrt n) ^ 3) := by
          simp only [Finset.prod_const, Nat.card_Ico, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, add_tsub_cancel_left]
          symm
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]
  have htend : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (((L + 1) * n : ℕ) * (2 * (c / n) * Real.sqrt n) ^ 3)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((L + 1 : ℝ) * (8 * c ^ 3)) * (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      simpa using this.const_mul ((L + 1 : ℝ) * (8 * c ^ 3))
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (h1.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
    push_cast
    field_simp
    rw [show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring, hsq]
    ring
  -- inclusion
  have hsub : {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ L ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, |(t : ℝ) - s| ≤ δ →
      |B t ω - B s ω| ≤ K * |(t : ℝ) - s|} ⊆ ⋃ m : ℕ, ⋂ n : ℕ, ⋂ (_ : m ≤ n), E n := by
    rintro ω ⟨s, hsL, δ, hδ, hlip⟩
    refine Set.mem_iUnion.2 ⟨⌈4 / δ⌉₊ + 1, Set.mem_iInter.2 fun n => Set.mem_iInter.2 fun hn => ?_⟩
    have hn1 : (⌈4 / δ⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hn' : (0 : ℝ) < n := by linarith [Nat.cast_nonneg (α := ℝ) ⌈4 / δ⌉₊]
    have h4 : 4 / (n : ℝ) ≤ δ := by
      rw [div_le_iff₀ hn']
      have := Nat.le_ceil (4 / δ)
      rw [div_le_iff₀ hδ] at this
      nlinarith
    set i := ⌈(s : ℝ) * n⌉₊ with hi
    have hi1 : (s : ℝ) * n ≤ i := Nat.le_ceil _
    have hi2 : (i : ℝ) < s * n + 1 := Nat.ceil_lt_add_one (by positivity)
    have hpt : ∀ k', i ≤ k' → k' ≤ i + 3 → |B (tn n k') ω - B s ω| ≤ K * (4 / n) := by
      intro k' hk1 hk2
      have hk1' : (i : ℝ) ≤ k' := by exact_mod_cast hk1
      have hk2' : (k' : ℝ) ≤ i + 3 := by exact_mod_cast hk2
      have e1 : (s : ℝ) ≤ k' / n := by rw [le_div_iff₀ hn']; linarith
      have e2 : (k' : ℝ) / n - s ≤ 4 / n := by
        rw [div_sub' hn'.ne', div_le_div_iff_of_pos_right hn']; linarith
      have hab : |(tn n k' : ℝ) - s| ≤ 4 / n := by
        rw [htnr, abs_of_nonneg (by linarith)]; exact e2
      exact (hlip _ (hab.trans h4)).trans (mul_le_mul_of_nonneg_left hab (by positivity))
    simp only [hE, Set.mem_iUnion, Set.mem_iInter, Finset.mem_range, Finset.mem_Ico,
      Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    refine ⟨i, ?_, fun k hk => ?_⟩
    · have hL : (s : ℝ) * n ≤ L * n := mul_le_mul_of_nonneg_right hsL hn'.le
      have : (i : ℝ) < ((L + 1) * n : ℕ) := by push_cast; nlinarith
      exact_mod_cast this
    · have a1 := hpt (k + 1) (by omega) (by omega)
      have a2 := hpt k hk.1 (by omega)
      simp only [hΔ]
      calc |B (tn n (k + 1)) ω - B (tn n k) ω|
          ≤ |B (tn n (k + 1)) ω - B s ω| + |B s ω - B (tn n k) ω| := abs_sub_le _ _ _
        _ ≤ K * (4 / n) + K * (4 / n) := by rw [abs_sub_comm (B s ω)]; linarith
        _ = c / n := by rw [hc]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun m => ?_)
  refine le_antisymm (ge_of_tendsto htend ?_) bot_le
  filter_upwards [eventually_ge_atTop (max m 1)] with n hn
  calc P (⋂ n' : ℕ, ⋂ (_ : m ≤ n'), E n') ≤ P (E n) :=
        measure_mono (Set.iInter₂_subset n (le_of_max_le_left hn))
    _ ≤ _ := hEle n (lt_of_lt_of_le one_pos (le_of_max_le_right hn))

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (C : ℝ), ¬ LipschitzAtPoint (fun t => B t ω) s C := by
  have hall : ∀ᵐ ω ∂P, ∀ K L : ℕ, ¬ (∃ s : ℝ≥0, (s : ℝ) ≤ L ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ≥0, |(t : ℝ) - s| ≤ δ → |B t ω - B s ω| ≤ K * |(t : ℝ) - s|) := by
    rw [ae_all_iff]; intro K; rw [ae_all_iff]; intro L
    exact ae_iff.2 (measure_mono_null (fun ω h => not_not.mp h)
      (AuxNL_null hB.toIsPreBrownianReal K L))
  filter_upwards [hall] with ω hω s C ⟨δ, hδ, hlip⟩
  exact hω ⌈C⌉₊ ⌈(s : ℝ)⌉₊ ⟨s, Nat.le_ceil _, δ, hδ, fun t ht =>
    (hlip t ht).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (abs_nonneg _))⟩

end DurrettProbability
