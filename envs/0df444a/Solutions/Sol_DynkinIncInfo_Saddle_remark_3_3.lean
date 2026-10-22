-- Prove2me | solution 1 for DynkinIncInfo.Saddle.remark_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:11:22.69853+00:00
-- url     : https://prove2.me/submissions/859f8366-edb0-4f24-81b5-d38983bda6f2

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_Model
import Definitions.Def_DynkinIncInfo_Saddle_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open DynkinIncInfo.Saddle

namespace DynkinRemark33Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Vup_le_G2 (p : Params) (st : Setting Ω) (x' y' : ℝ) :
    Vup p st x' y' ≤ ENNReal.ofReal (G2 p x') := by
  haveI := st.isProb
  unfold Vup dynkinUpper
  refine (iInf₂_le (fun _ : Ω => (0 : WithTop ℝ≥0)) (isStoppingTime_const _ _)).trans ?_
  refine iSup₂_le fun τ _ => ?_
  have hB := st.brownian.eval_zero_ae_eq_zero
  calc dynkinM st.P (L1 p st x' y') (U2 p st x' y') τ (fun _ => 0)
      ≤ ∫⁻ _, ENNReal.ofReal (G2 p x') ∂st.P := by
        apply lintegral_mono_ae
        filter_upwards [hB] with ω hω
        have hS : S p st x' y' 0 ω = x' := by simp [S, hω]
        unfold dynkinPayoff
        split_ifs with h1 h2
        · have : τ ω = 0 := le_antisymm h1.1 bot_le
          rw [this]
          show ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G1 p (S p st x' y' 0 ω)) ≤ _
          rw [hS]
          apply ENNReal.ofReal_le_ofReal
          simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul]
          unfold G1 G2; linarith [p.ε0_pos]
        · show ENNReal.ofReal (Real.exp (-p.r * ((0 : ℝ≥0) : ℝ)) * G2 p (S p st x' y' 0 ω)) ≤ _
          rw [hS]; simp
        · exact zero_le
    _ = ENNReal.ofReal (G2 p x') := by simp

end DynkinRemark33Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (x y : ℝ) (hx : 0 < x) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 < V p st x y := by
  haveI := st.isProb
  -- a level `c` such that `B_1 ≥ c` forces `S_1 ≥ K + ε0`
  set c : ℝ := (Real.log ((p.K + p.ε0) / x) + p.δ0 + p.σ ^ 2 / 2) / p.σ with hc
  set E : Set Ω := {ω | c ≤ st.B 1 ω} with hE
  have hEm : MeasurableSet E := measurableSet_le measurable_const (st.measurable_B 1)
  have hKε : 0 < p.K + p.ε0 := by linarith [p.K_pos, p.ε0_pos]
  have hS1 : ∀ ω ∈ E, p.K + p.ε0 ≤ S p st x y 1 ω := by
    intro ω hω
    simp only [hE, Set.mem_setOf_eq] at hω
    have hD : D st y ω ≤ 1 := by unfold D; split_ifs <;> norm_num
    have hσc : p.σ * c = Real.log ((p.K + p.ε0) / x) + p.δ0 + p.σ ^ 2 / 2 := by
      rw [hc]; field_simp [p.σ_pos.ne']
    have hexp : Real.log ((p.K + p.ε0) / x) ≤
        p.σ * st.B 1 ω + (p.r - p.δ0 * D st y ω) * ((1 : ℝ≥0) : ℝ) - ((1 : ℝ≥0) : ℝ) * p.σ ^ 2 / 2 := by
      simp only [NNReal.coe_one, mul_one, one_mul]
      have h1 : p.σ * c ≤ p.σ * st.B 1 ω := mul_le_mul_of_nonneg_left hω p.σ_pos.le
      have h2 : p.δ0 * D st y ω ≤ p.δ0 := by
        have := p.δ0_pos; nlinarith
      linarith [p.r_pos]
    unfold S
    calc p.K + p.ε0 = x * ((p.K + p.ε0) / x) := by field_simp
      _ = x * Real.exp (Real.log ((p.K + p.ε0) / x)) := by
          rw [Real.exp_log (div_pos hKε hx)]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hx.le
  -- `P(E) > 0` since `B_1` is a nondegenerate Gaussian
  have hPE : st.P E ≠ 0 := by
    have hlaw := st.brownian.hasLaw_eval 1
    have hmap : st.P E = gaussianReal 0 ((1 : ℝ≥0)) (Set.Ici c) := by
      rw [← hlaw.map_eq, Measure.map_apply (st.measurable_B 1) measurableSet_Ici]
      rfl
    rw [hmap]
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 (v := (1 : ℝ≥0)) one_ne_zero h0
    simp at this
  -- the lower bound `M(1, γ) ≥ e^{-r} ε0 P(E)` for every `γ`
  set c0 : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-p.r) * p.ε0) with hc0
  have hc0pos : c0 ≠ 0 := by
    rw [hc0]
    have := Real.exp_pos (-p.r)
    have := p.ε0_pos
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hM : ∀ γ : Ω → WithTop ℝ≥0,
      c0 * st.P E ≤ M p st x y (fun _ => ((1 : ℝ≥0) : WithTop ℝ≥0)) γ := by
    intro γ
    rw [← lintegral_indicator_const hEm]
    apply lintegral_mono
    intro ω
    unfold dynkinPayoff
    split_ifs with h1 h2
    · -- `τ = 1 ≤ γ`
      show E.indicator (fun _ => c0) ω ≤
        ENNReal.ofReal (Real.exp (-p.r * ((1 : ℝ≥0) : ℝ)) * G1 p (S p st x y 1 ω))
      by_cases hω : ω ∈ E
      · rw [Set.indicator_of_mem hω, hc0]
        apply ENNReal.ofReal_le_ofReal
        simp only [NNReal.coe_one, mul_one]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        have := hS1 ω hω
        unfold G1
        exact le_max_of_le_left (by linarith)
      · rw [Set.indicator_of_notMem hω]; exact zero_le
    · -- `γ < 1`
      refine (Set.indicator_le_self _ _ ω).trans ?_
      have hne : γ ω ≠ ⊤ := ne_top_of_lt h2
      obtain ⟨G, hG⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hG]
      show c0 ≤ ENNReal.ofReal (Real.exp (-p.r * (G : ℝ)) * G2 p (S p st x y G ω))
      rw [hc0]
      apply ENNReal.ofReal_le_ofReal
      have hG1 : (G : ℝ) ≤ 1 := by
        rw [← hG] at h2
        exact_mod_cast (WithTop.coe_lt_coe.mp h2).le
      apply mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [p.r_pos])) _ p.ε0_pos.le
        (Real.exp_pos _).le
      unfold G2
      linarith [le_max_right (S p st x y G ω - p.K) 0]
    · exfalso
      rcases le_or_gt (((1 : ℝ≥0) : WithTop ℝ≥0)) (γ ω) with h | h
      · exact h1 ⟨h, WithTop.coe_ne_top⟩
      · exact h2 h
  have hVup : c0 * st.P E ≤ Vup p st x y := by
    unfold Vup dynkinUpper
    refine le_iInf₂ fun γ _ => ?_
    exact (hM γ).trans (le_iSup₂ (f := fun τ (_ : IsStoppingTime (FS p st x y) τ) =>
      dynkinM st.P (L1 p st x y) (U2 p st x y) τ γ) _ (isStoppingTime_const _ _))
  have hpos : Vup p st x y ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hc0pos hPE)) hVup).ne'
  have hfin : Vup p st x y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (DynkinRemark33Aux.Vup_le_G2 p st x y)
  exact ENNReal.toReal_pos hpos hfin
