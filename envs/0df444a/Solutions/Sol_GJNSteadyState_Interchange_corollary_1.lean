-- Prove2me | solution 1 for GJNSteadyState.Interchange.corollary_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:43:12.601517+00:00
-- url     : https://prove2.me/submissions/2ec619f1-ddc9-483a-9665-933838e8cf7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
import Theorems.Thm_GJNSteadyState_Interchange_theorem_7
open MeasureTheory Filter Topology Matrix

open GJNSteadyState.Interchange in
/-- The workload vector `w = e′[I − P′]⁻¹` satisfies `w ≥ e` componentwise. -/
private lemma wvec_ge_one {J : ℕ} (Ξ : Network J) (hP0 : ∀ j k, 0 ≤ Ξ.P j k)
    (hPm : Tendsto (fun m : ℕ => Ξ.P ^ m) atTop (𝓝 0)) (j : Fin J) : 1 ≤ wvec Ξ j := by
  set A : Matrix (Fin J) (Fin J) ℝ := Ξ.Pᵀ with hA
  have hAm : Tendsto (fun m : ℕ => A ^ m) atTop (𝓝 0) := by
    have hc : Continuous (fun M : Matrix (Fin J) (Fin J) ℝ => Mᵀ) := continuous_id.matrix_transpose
    have := (hc.tendsto 0).comp hPm
    simp only [Matrix.transpose_zero] at this
    refine this.congr (fun m => ?_)
    simp [hA, Matrix.transpose_pow]
  have hvc : ∀ v : Fin J → ℝ, Continuous (fun M : Matrix (Fin J) (Fin J) ℝ => v ᵥ* M) :=
    fun v => continuous_const.matrix_vecMul continuous_id
  -- invertibility of 1 - A
  have hunit : IsUnit (1 - A) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro u v huv
    simp only at huv
    have h0 : (u - v) ᵥ* (1 - A) = 0 := by
      rw [Matrix.sub_vecMul, huv, sub_self]
    set d := u - v with hd
    have hfix : ∀ m : ℕ, d = d ᵥ* A ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h1 : d = d ᵥ* A := by
          have := h0
          rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at this
          exact this
        rw [pow_succ, ← Matrix.vecMul_vecMul, ← ih]; exact h1
    have hlim : Tendsto (fun m : ℕ => d ᵥ* A ^ m) atTop (𝓝 (d ᵥ* 0)) :=
      ((hvc d).tendsto 0).comp hAm
    rw [Matrix.vecMul_zero] at hlim
    have hd0 : d = 0 := by
      have : Tendsto (fun _ : ℕ => d) atTop (𝓝 0) := hlim.congr (fun m => (hfix m).symm)
      exact tendsto_nhds_unique tendsto_const_nhds this
    exact sub_eq_zero.1 hd0
  set w := wvec Ξ with hw
  have hwfix : w = (fun _ => (1 : ℝ)) + w ᵥ* A := by
    have h1 : w ᵥ* (1 - A) = fun _ => (1 : ℝ) := by
      rw [hw, wvec, Matrix.vecMul_vecMul, ← hA,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), Matrix.vecMul_one]
    rw [Matrix.vecMul_sub, Matrix.vecMul_one] at h1
    rw [← h1]; abel
  have hAnn : ∀ m : ℕ, ∀ i k, 0 ≤ (A ^ m) i k := by
    intro m
    induction m with
    | zero => intro i k; simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ m ih =>
      intro i k
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (by simp [hA, hP0]))
  have hiter : ∀ m : ℕ, w = (∑ i ∈ Finset.range m, (fun _ => (1 : ℝ)) ᵥ* A ^ i) + w ᵥ* A ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      conv_lhs => rw [ih]
      conv_lhs => rw [hwfix]
      rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, ← pow_succ', Finset.sum_range_succ, add_assoc]
  have hge : ∀ m : ℕ, 1 + (w ᵥ* A ^ (m + 1)) j ≤ w j := by
    intro m
    have h := congrFun (hiter (m + 1)) j
    rw [Pi.add_apply, Finset.sum_apply] at h
    rw [h]
    gcongr
    have hterm : ∀ i ∈ Finset.range (m + 1), 0 ≤ ((fun _ => (1 : ℝ)) ᵥ* A ^ i) j := by
      intro i _
      simp only [Matrix.vecMul, dotProduct, one_mul]
      exact Finset.sum_nonneg (fun k _ => hAnn i k j)
    have h0 := Finset.single_le_sum hterm (Finset.mem_range.2 (Nat.succ_pos m))
    simpa [Matrix.vecMul, dotProduct, Matrix.one_apply] using h0
  have hlim : Tendsto (fun m : ℕ => 1 + (w ᵥ* A ^ (m + 1)) j) atTop (𝓝 (1 + (w ᵥ* 0) j)) := by
    refine tendsto_const_nhds.add ?_
    exact (continuous_apply j).continuousAt.tendsto.comp
      (((hvc w).tendsto 0).comp (hAm.comp (tendsto_add_atTop_nat 1)))
  rw [Matrix.vecMul_zero, Pi.zero_apply, add_zero] at hlim
  exact le_of_tendsto' hlim hge

open GJNSteadyState.Interchange in
theorem solution {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j)
    (π : ℕ → Measure (State J)) [∀ n, IsProbabilityMeasure (π n)]
    (hπ : ∀ᶠ n in atTop, IsStationary (htNet Ξ κ0 n) (π n)) :
    IsTightMeasureSet (Set.range fun n => (π n).map (scaleQ n)) := by
  obtain ⟨C₁, c₁, hC, hc, hev⟩ := GJNSteadyState.Interchange.theorem_7 Ξ hΞ hcrit κ0 hκ0
  obtain ⟨_, _, _, _, _, hP0, _, hPm⟩ := hΞ
  have hw := wvec_ge_one Ξ hP0 hPm
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and hπ)
  set f : ℕ → Measure (Fin J → ℝ) := fun n => (π n).map (scaleQ n) with hf
  have hfin : ∀ M, IsTightMeasureSet (f '' {n | n < M}) := by
    intro M
    induction M with
    | zero =>
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε _
      exact ⟨∅, isCompact_empty, fun μ hμ => by simp at hμ⟩
    | succ M ih =>
      have : {n | n < M + 1} = insert M {n | n < M} := by
        ext n; simp only [Set.mem_setOf_eq, Set.mem_insert_iff]; omega
      rw [this, Set.image_insert_eq, Set.insert_eq]
      exact isTightMeasureSet_singleton.union ih
  have htail : IsTightMeasureSet (f '' {n | N ≤ n}) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεt : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ _ => by rw [hεt]; exact le_top⟩
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    set s : ℝ := max 1 (Real.log (C₁ / ε.toReal) / c₁) with hsdef
    have hs0 : 0 < s := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hsε : ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s))) ≤ ε := by
      rw [← ENNReal.ofReal_toReal hεt]
      apply ENNReal.ofReal_le_ofReal
      have h1 : Real.log (C₁ / ε.toReal) ≤ c₁ * s := by
        have := le_max_right 1 (Real.log (C₁ / ε.toReal) / c₁)
        rw [← hsdef] at this
        rwa [div_le_iff₀ hc, mul_comm] at this
      have h2 : Real.exp (-(c₁ * s)) ≤ ε.toReal / C₁ := by
        calc Real.exp (-(c₁ * s)) ≤ Real.exp (-(Real.log (C₁ / ε.toReal))) :=
              Real.exp_le_exp.2 (by linarith)
          _ = ε.toReal / C₁ := by
              rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      calc C₁ * Real.exp (-(c₁ * s)) ≤ C₁ * (ε.toReal / C₁) := by gcongr
        _ = ε.toReal := by field_simp
    refine ⟨Metric.closedBall 0 s, isCompact_closedBall _ _, ?_⟩
    rintro μ ⟨n, hn, rfl⟩
    obtain ⟨h7, hst⟩ := hN n hn
    simp only [hf]
    rw [Measure.map_apply (measurable_scaleQ n) Metric.isClosed_closedBall.measurableSet.compl]
    refine le_trans (measure_mono ?_) (le_trans (h7 (π n) hst s hs0) hsε)
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      not_le] at hx
    obtain ⟨j, hj⟩ : ∃ j, s < ‖scaleQ n x j‖ := by
      by_contra h
      push Not at h
      exact absurd hx (not_lt.2 ((pi_norm_le_iff_of_nonneg hs0.le).2 h))
    show s < (Real.sqrt n)⁻¹ * (wvec Ξ ⬝ᵥ fun j => (x.1 j : ℝ))
    have hxj : (0 : ℝ) ≤ x.1 j := Nat.cast_nonneg _
    have hnorm : ‖scaleQ n x j‖ = (Real.sqrt n)⁻¹ * (x.1 j : ℝ) := by
      simp only [scaleQ, Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg hxj (Real.sqrt_nonneg _)), div_eq_inv_mul]
    rw [hnorm] at hj
    refine lt_of_lt_of_le hj ?_
    gcongr
    calc (x.1 j : ℝ) ≤ wvec Ξ j * x.1 j := le_mul_of_one_le_left hxj (hw j)
      _ ≤ wvec Ξ ⬝ᵥ fun j => (x.1 j : ℝ) := by
        unfold dotProduct
        exact Finset.single_le_sum (f := fun k => wvec Ξ k * (x.1 k : ℝ))
          (fun k _ => mul_nonneg (le_trans zero_le_one (hw k)) (Nat.cast_nonneg _))
          (Finset.mem_univ j)
  refine ((hfin N).union htail).subset ?_
  rintro μ ⟨n, rfl⟩
  rcases lt_or_ge n N with h | h
  · left; exact ⟨n, h, rfl⟩
  · right; exact ⟨n, h, rfl⟩
