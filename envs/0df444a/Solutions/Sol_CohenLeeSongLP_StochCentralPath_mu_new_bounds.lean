-- Prove2me | solution 1 for CohenLeeSongLP.StochCentralPath.mu_new_bounds
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T02:55:38.975401+00:00
-- url     : https://prove2.me/submissions/9fcafcc0-b511-48b1-9075-33009d75fad5

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix

namespace FCex70ba82ad
open CohenLeeSongLP.StochCentralPath

/-- `A = (1, 1, 0, …, 0)`, a full-row-rank `1 × 10` matrix. -/
noncomputable def A0 : Matrix (Fin 1) (Fin 10) ℝ :=
  Matrix.of fun _ j => if (j : ℕ) < 2 then (1 : ℝ) else 0

noncomputable def e0 : ℝ := 1 / 1000000

/-- `δ_μ = ε e₀`. -/
noncomputable def dmu : Fin 10 → ℝ := fun j => if (j : ℕ) = 0 then e0 else 0

noncomputable def one10 : Fin 10 → ℝ := fun _ => 1

noncomputable def kS : ℝ := 1000000000

lemma xbar_one : xbar one10 one10 one10 = one10 := by
  funext i; simp [xbar, one10]

lemma sbar_one : sbar one10 one10 one10 = one10 := by
  funext i; simp [sbar, one10]

lemma hAA : A0 * A0.transpose = (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp [A0, Matrix.mul_apply, Fin.sum_univ_succ]
  norm_num

lemma hinv : (A0 * A0.transpose)⁻¹ = (1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  apply Matrix.inv_eq_right_inv
  rw [hAA, smul_mul_smul_comm, Matrix.one_mul]
  norm_num

lemma rank_A0 : A0.rank = 1 := by
  apply le_antisymm (Matrix.rank_le_height A0)
  have hu : IsUnit (A0 * A0.transpose) := by
    rw [Matrix.isUnit_iff_isUnit_det, hAA, Matrix.det_smul, Matrix.det_one]
    norm_num
  have h1 := Matrix.rank_of_isUnit (A0 * A0.transpose) hu
  have h2 := Matrix.rank_mul_le_left A0 A0.transpose
  simp only [Fintype.card_fin] at h1
  omega

/-- `p_μ = P̄ δ_μ = (ε/2, ε/2, 0, …, 0)`. -/
lemma pMu_eq : pMu A0 one10 one10 one10 dmu = fun j : Fin 10 => if (j : ℕ) < 2 then e0 / 2 else 0 := by
  unfold pMu
  rw [xbar_one, sbar_one]
  unfold projBar
  have hD : Matrix.diagonal (fun i => Real.sqrt (one10 i / one10 i)) = 1 := by
    ext i j; simp [Matrix.diagonal, Matrix.one_apply, one10]
  have hM : Matrix.diagonal (fun i => one10 i / one10 i) = 1 := by
    ext i j; simp [Matrix.diagonal, Matrix.one_apply, one10]
  have hv : (fun i => dmu i / Real.sqrt (one10 i * one10 i)) = dmu := by
    funext i; simp [one10]
  rw [hD, hM, hv]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv]
  funext j
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, A0, dmu, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

lemma stepS_eq (i : Fin 10) : stepS A0 one10 one10 one10 dmu i = if (i : ℕ) < 2 then e0 / 2 else 0 := by
  unfold stepS; rw [pMu_eq, xbar_one, sbar_one]; simp [one10]

lemma stepX_eq (i : Fin 10) :
    stepX A0 one10 one10 one10 dmu i = dmu i - (if (i : ℕ) < 2 then e0 / 2 else 0) := by
  unfold stepX; rw [pMu_eq, xbar_one, sbar_one]; simp [one10]

lemma log10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)

lemma log10_le : Real.log 10 ≤ 9 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
  linarith

lemma step_bounds (i : Fin 10) :
    |stepS A0 one10 one10 one10 dmu i / sbar one10 one10 one10 i| ≤ e0 / 2 ∧
    |stepX A0 one10 one10 one10 dmu i / xbar one10 one10 one10 i| ≤ e0 / 2 := by
  rw [stepS_eq, stepX_eq, xbar_one, sbar_one]
  have he : 0 < e0 := by unfold e0; norm_num
  simp only [one10, div_one, dmu]
  constructor
  · split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma mem_success : dmu ∈ successEvent A0 one10 one10 one10 := by
  have hb : e0 / 2 ≤ 1 / (100 * Real.log ((10 : ℕ) : ℝ)) := by
    rw [Nat.cast_ofNat, le_div_iff₀ (by have := log10_pos; positivity)]
    have := log10_le
    have := log10_pos
    unfold e0; nlinarith
  intro i
  exact ⟨(step_bounds i).1.trans hb, (step_bounds i).2.trans hb⟩

lemma sampleProb_one (i : Fin 10) : sampleProb kS dmu i = 1 := by
  unfold sampleProb
  apply min_eq_left
  have h0 : 0 ≤ dmu i ^ 2 / ∑ l, dmu l ^ 2 := by positivity
  unfold kS
  push_cast
  nlinarith

lemma pi_dirac_eq (a : Fin 10 → ℝ) :
    Measure.pi (fun i => Measure.dirac (a i)) = Measure.dirac a := by
  classical
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  simp only [Set.indicator, Pi.one_apply]
  rw [Finset.prod_boole]
  simp [Set.mem_univ_pi]

lemma stepLaw_eq : stepLaw A0 one10 one10 one10 kS dmu = Measure.dirac dmu := by
  classical
  unfold stepLaw sampleLaw
  have hc : (fun i => coordLaw (sampleProb kS dmu i) (dmu i)) = fun i => Measure.dirac (dmu i) := by
    funext i
    rw [sampleProb_one]
    simp [coordLaw]
  rw [hc, pi_dirac_eq]
  unfold ProbabilityTheory.cond
  rw [MeasureTheory.restrict_dirac, if_pos mem_success, Measure.dirac_apply_of_mem mem_success, inv_one,
    one_smul]

lemma asm : Assumption41 one10 one10 1 one10 dmu kS e0 (e0 / 1000) := by
  have he : 0 < e0 := by unfold e0; norm_num
  have hl := log10_le
  have hl0 := log10_pos
  refine
    { x_pos := fun i => by simp [one10]
      s_pos := fun i => by simp [one10]
      t_pos := by norm_num
      xs_approx := fun i => by simp [one10]; norm_num
      εmp_pos := by positivity
      εmp_le := by unfold e0; norm_num
      w_approx := fun i => by
        simp only [one10, div_one, mul_one]
        constructor <;> linarith
      ε_pos := he
      ε_le := by
        rw [Nat.cast_ofNat, le_div_iff₀ (by positivity)]
        unfold e0; nlinarith
      δμ_norm := by
        unfold norm2
        have : ∑ i, dmu i ^ 2 = e0 ^ 2 := by
          simp [Fin.sum_univ_succ, dmu]
        rw [this, Real.sqrt_sq he.le, mul_one]
      kSamp_pos := by unfold kS; norm_num
      kSamp_ge := by
        have hs : Real.sqrt ((10 : ℕ) : ℝ) ≤ 4 := by
          rw [Real.sqrt_le_iff]; norm_num
        rw [Nat.cast_ofNat] at hs ⊢
        rw [div_le_iff₀ (by positivity)]
        have hs0 : 0 ≤ Real.sqrt (10 : ℝ) := Real.sqrt_nonneg _
        have hl2 : Real.log 10 ^ 2 ≤ 81 := by nlinarith
        unfold kS e0
        have : Real.sqrt 10 * Real.log 10 ^ 2 ≤ 4 * 81 := by
          apply mul_le_mul hs hl2 (by positivity) (by norm_num)
        nlinarith }

/-- Part 1 fails: `‖E[μ⁻¹(μ^new − μ − δ̃_μ)]‖₂ = ε²/(2√2) > 10 ε_mp ε = ε²/100`. -/
lemma part1_fails :
    10 * (e0 / 1000) * e0 <
      norm2 (fun i => ∫ δ, (muNew A0 one10 one10 one10 δ i - one10 i * one10 i - δ i) /
        (one10 i * one10 i) ∂(stepLaw A0 one10 one10 one10 kS dmu)) := by
  rw [stepLaw_eq]
  simp only [integral_dirac]
  unfold norm2 muNew
  simp only [stepS_eq, stepX_eq]
  rw [Real.lt_sqrt (by unfold e0; norm_num)]
  simp [Fin.sum_univ_succ, dmu, one10]
  unfold e0
  norm_num

end FCex70ba82ad

open CohenLeeSongLP.StochCentralPath MeasureTheory ProbabilityTheory in
theorem solution : ¬ (∀ {n d : ℕ} (hn : 10 ≤ n) (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : A.rank = d) (x s v δμ : Fin n → ℝ) (t kSamp ε εmp : ℝ)
    (hAs : Assumption41 x s t v δμ kSamp ε εmp),
    IsProbabilityMeasure (stepLaw A x s v kSamp δμ) ∧
    norm2 (fun i => ∫ δ, (muNew A x s v δ i - x i * s i - δ i) / (x i * s i)
      ∂(stepLaw A x s v kSamp δμ)) ≤ 10 * εmp * ε ∧
    norm2 (fun i => ∫ δ, (muNew A x s v δ i - x i * s i) / (x i * s i)
      ∂(stepLaw A x s v kSamp δμ)) ≤ 5 * ε ∧
    (∀ i, variance (fun δ => muNew A x s v δ i / (x i * s i)) (stepLaw A x s v kSamp δμ)
      ≤ 50 * ε ^ 2 / kSamp) ∧
    (∀ δ ∈ successEvent A x s v, ∀ i,
      |(muNew A x s v δ i - x i * s i) / (x i * s i)| ≤ 0.021 / Real.log n)) := by
  intro h
  have h1 := (@h 10 1 le_rfl FCex70ba82ad.A0 FCex70ba82ad.rank_A0 FCex70ba82ad.one10
    FCex70ba82ad.one10 FCex70ba82ad.one10 FCex70ba82ad.dmu 1 FCex70ba82ad.kS FCex70ba82ad.e0
    (FCex70ba82ad.e0 / 1000) FCex70ba82ad.asm).2.1
  exact absurd h1 (not_le.mpr FCex70ba82ad.part1_fails)
