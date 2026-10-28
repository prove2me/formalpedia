-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T09:47:14.449029+00:00
-- url     : https://prove2.me/submissions/5ed1c143-5f5e-4f06-874c-104b4067d13c

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace FBMStrongSim.RecordBreak

private lemma gaussian_mgf_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (hcent : P[X] = 0) {σ : ℝ} (hvar : Var[X; P] ≤ σ ^ 2) (t : ℝ) :
    mgf X P t ≤ Real.exp (t ^ 2 * σ ^ 2 / 2) := by
  rw [mgf_gaussianReal hX.map_eq_gaussianReal, hcent]
  simp only [zero_mul, zero_add]
  apply Real.exp_le_exp.mpr
  have hv : (Var[X; P].toNNReal : ℝ) = Var[X; P] :=
    Real.coe_toNNReal _ (variance_nonneg X P)
  rw [hv]
  nlinarith [sq_nonneg t]

private lemma gaussian_exp_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) P := by
  have h := (mgf_pos_iff (X := X) (μ := P) (t := t)).mp ?_
  · exact h
  · rw [mgf_gaussianReal hX.map_eq_gaussianReal]
    positivity

private lemma gaussian_exp_abs_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * |X ω|)) P := by
  have hX_int : Integrable (fun ω => Real.exp (t * X ω)) P :=
    gaussian_exp_integrable hX t
  have hX_neg_int : Integrable (fun ω => Real.exp ((-t) * X ω)) P :=
    gaussian_exp_integrable hX (-t)
  have h_abs_meas : AEStronglyMeasurable (fun ω => Real.exp (t * |X ω|)) P :=
    (hX.aemeasurable.abs.const_mul t).exp.aestronglyMeasurable
  have h_le : (fun ω => Real.exp (t * |X ω|)) ≤
      fun ω => Real.exp (t * X ω) + Real.exp ((-t) * X ω) := by
    intro ω
    change Real.exp (t * |X ω|) ≤ Real.exp (t * X ω) + Real.exp ((-t) * X ω)
    by_cases hx : 0 ≤ X ω
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · have hx' : X ω < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx']
      have : t * -X ω = (-t) * X ω := by ring
      rw [this]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  refine Integrable.mono' (hX_int.add hX_neg_int) h_abs_meas ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact h_le ω

private lemma gaussian_exp_abs_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (hcent : P[X] = 0) {σ : ℝ} (hvar : Var[X; P] ≤ σ ^ 2) (t : ℝ) :
    ∫ ω, Real.exp (t * |X ω|) ∂P ≤ 2 * Real.exp (t ^ 2 * σ ^ 2 / 2) := by
  have hX_int : Integrable (fun ω => Real.exp (t * X ω)) P :=
    gaussian_exp_integrable hX t
  have hX_neg_int : Integrable (fun ω => Real.exp ((-t) * X ω)) P :=
    gaussian_exp_integrable hX (-t)
  have h_abs_int : Integrable (fun ω => Real.exp (t * |X ω|)) P :=
    gaussian_exp_abs_integrable hX t
  have h_le : (fun ω => Real.exp (t * |X ω|)) ≤
      fun ω => Real.exp (t * X ω) + Real.exp ((-t) * X ω) := by
    intro ω
    change Real.exp (t * |X ω|) ≤ Real.exp (t * X ω) + Real.exp ((-t) * X ω)
    by_cases hx : 0 ≤ X ω
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · have hx' : X ω < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx']
      have : t * -X ω = (-t) * X ω := by ring
      rw [this]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    ∫ ω, Real.exp (t * |X ω|) ∂P
        ≤ ∫ ω, (Real.exp (t * X ω) + Real.exp ((-t) * X ω)) ∂P := by
          exact integral_mono h_abs_int (hX_int.add hX_neg_int) h_le
    _ = mgf X P t + mgf X P (-t) := by
          rw [integral_add hX_int hX_neg_int]
          rfl
    _ ≤ Real.exp (t ^ 2 * σ ^ 2 / 2) + Real.exp (t ^ 2 * σ ^ 2 / 2) := by
          gcongr
          · exact gaussian_mgf_bound hX hcent hvar t
          · simpa only [neg_sq] using gaussian_mgf_bound hX hcent hvar (-t)
    _ = 2 * Real.exp (t ^ 2 * σ ^ 2 / 2) := by ring

end FBMStrongSim.RecordBreak

namespace FBMStrongSim.RecordBreak

private lemma lemma_3_3_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hcent : ∀ i, P[X i] = 0) {σ : ℝ} (hσ : 0 ≤ σ) (hσpos : 0 < σ)
    (hvar : ∀ i, Var[X i; P] ≤ σ ^ 2) :
    P[fun ω => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      fun i => |X i ω|] ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  let M : Ω → ℝ := fun ω => Finset.univ.sup' hne (fun i => |X i ω|)
  change P[M] ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLpos : 0 < Real.log (2 * (n : ℝ)) := by
    apply Real.log_pos
    nlinarith
  let L : ℝ := Real.log (2 * (n : ℝ))
  let s : ℝ := Real.sqrt (2 * L)
  let t : ℝ := s / σ
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_pos : 0 < s := by
    apply Real.sqrt_pos.mpr
    positivity
  have ht : 0 < t := div_pos hs_pos hσpos
  have hM_ae : AEMeasurable M P := by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h_eq : M = fun ω => ⨆ i : Fin n, |X i ω| := by
      funext ω
      apply le_antisymm
      · refine Finset.sup'_le hne (fun i => |X i ω|) (fun i hi => ?_)
        exact le_ciSup (Finite.bddAbove_range (fun i : Fin n => |X i ω|)) i
      · refine (ciSup_le_iff (Finite.bddAbove_range (fun i : Fin n => |X i ω|))).mpr (fun i => ?_)
        exact Finset.le_sup' (fun i : Fin n => |X i ω|) (Finset.mem_univ i)
    rw [h_eq]
    exact AEMeasurable.iSup (fun i => (hX i).aemeasurable.abs)
  have hM_nonneg : ∀ ω, 0 ≤ M ω := by
    intro ω
    exact (Finset.le_sup'_iff hne).mpr
      ⟨⟨0, hn⟩, Finset.mem_univ _, abs_nonneg (X ⟨0, hn⟩ ω)⟩
  have h_abs_int : ∀ i, Integrable (fun ω => Real.exp (t * |X i ω|)) P :=
    fun i => gaussian_exp_abs_integrable (hX i) t
  let S : Ω → ℝ := fun ω => ∑ i, Real.exp (t * |X i ω|)
  have hS_int : Integrable S P := by
    dsimp [S]
    exact integrable_finsetSum Finset.univ (fun i hi => h_abs_int i)
  have h_expM_le : ∀ ω, Real.exp (t * M ω) ≤ S ω := by
    intro ω
    obtain ⟨j, hj, hMj⟩ := Finset.exists_mem_eq_sup' hne (fun i => |X i ω|)
    dsimp [S]
    calc
      Real.exp (t * M ω) = Real.exp (t * |X j ω|) := by
        change Real.exp (t * Finset.univ.sup' hne (fun i => |X i ω|)) =
          Real.exp (t * |X j ω|)
        rw [hMj]
      _ ≤ ∑ i, Real.exp (t * |X i ω|) :=
        Finset.single_le_sum (f := fun i => Real.exp (t * |X i ω|))
          (fun i hi => (Real.exp_pos _).le) hj
  have h_expM_ae : AEStronglyMeasurable (fun ω => Real.exp (t * M ω)) P :=
    (hM_ae.const_mul t).exp.aestronglyMeasurable
  have h_expM_int : Integrable (fun ω => Real.exp (t * M ω)) P := by
    refine Integrable.mono' hS_int h_expM_ae ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h_expM_le ω
  have hM_int : Integrable M P := by
    refine Integrable.mono' (h_expM_int.const_mul (1 / t)) hM_ae.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hM_nonneg ω)]
    have hnonneg : 0 ≤ t * M ω := mul_nonneg ht.le (hM_nonneg ω)
    have hle : t * M ω ≤ Real.exp (t * M ω) := by
      linarith [Real.add_one_le_exp (t * M ω)]
    have hmul : M ω * t ≤ Real.exp (t * M ω) := by
      rw [mul_comm (M ω) t]
      exact hle
    have hle' := (le_div_iff₀ ht).mpr hmul
    simpa [one_div, div_eq_mul_inv, mul_comm] using hle'
  have h_jensen : Real.exp (t * ∫ ω, M ω ∂P) ≤ ∫ ω, Real.exp (t * M ω) ∂P := by
    have h := ConvexOn.map_integral_le (μ := P) (s := Set.univ)
      (f := fun ω => t * M ω) (g := Real.exp)
      convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ (fun ω => Set.mem_univ _))
      (hM_int.const_mul t) h_expM_int
    simpa only [integral_const_mul] using h
  have h_exp_bound : ∫ ω, Real.exp (t * M ω) ∂P ≤
      2 * n * Real.exp (t ^ 2 * σ ^ 2 / 2) := by
    calc
      ∫ ω, Real.exp (t * M ω) ∂P ≤ ∫ ω, S ω ∂P :=
        integral_mono h_expM_int hS_int h_expM_le
      _ = ∑ i, ∫ ω, Real.exp (t * |X i ω|) ∂P := by
        dsimp [S]
        rw [integral_finsetSum Finset.univ (fun i hi => h_abs_int i)]
      _ ≤ ∑ _i : Fin n, 2 * Real.exp (t ^ 2 * σ ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact gaussian_exp_abs_integral_le (hX i) (hcent i) (hvar i) t
      _ = 2 * n * Real.exp (t ^ 2 * σ ^ 2 / 2) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring
  have h_exp_final : Real.exp (t * ∫ ω, M ω ∂P) ≤
      2 * n * Real.exp (t ^ 2 * σ ^ 2 / 2) :=
    le_trans h_jensen h_exp_bound
  have hlog := Real.log_le_log (Real.exp_pos _) h_exp_final
  rw [Real.log_exp] at hlog
  have hlog_rhs : Real.log (2 * n * Real.exp (t ^ 2 * σ ^ 2 / 2)) =
      Real.log (2 * (n : ℝ)) + t ^ 2 * σ ^ 2 / 2 := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  rw [hlog_rhs] at hlog
  have hEM : ∫ ω, M ω ∂P ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
    have hdiv : ∫ ω, M ω ∂P ≤ Real.log (2 * (n : ℝ)) / t + t * σ ^ 2 / 2 := by
      rw [div_add_div _ _ ht.ne' (by norm_num : (2 : ℝ) ≠ 0)] at *
      field_simp [ht.ne'] at hlog ⊢
      nlinarith
    have ht_sq : t ^ 2 = 2 * L / σ ^ 2 := by
      dsimp [t, s]
      rw [div_pow, Real.sq_sqrt (by positivity)]
    have hval : Real.log (2 * (n : ℝ)) / t + t * σ ^ 2 / 2 = s * σ := by
      dsimp [t, s, L]
      field_simp [hσpos.ne']
      rw [Real.sq_sqrt (by positivity)]
      ring
    calc
      ∫ ω, M ω ∂P ≤ Real.log (2 * (n : ℝ)) / t + t * σ ^ 2 / 2 := hdiv
      _ = s * σ := hval
      _ = Real.sqrt (2 * Real.log (2 * n)) * σ := rfl
      _ ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
        have hs_le : Real.sqrt (2 * Real.log (2 * n)) ≤
            2 * Real.sqrt (2 * Real.log (2 * n)) := by
          linarith [Real.sqrt_nonneg (2 * Real.log (2 * n))]
        exact mul_le_mul_of_nonneg_right hs_le hσ
  exact hEM


private lemma lemma_3_3_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hcent : ∀ i, P[X i] = 0) {σ : ℝ} (hσ : 0 ≤ σ) (hσ0 : σ = 0)
    (hvar : ∀ i, Var[X i; P] ≤ σ ^ 2) :
    P[fun ω => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
      fun i => |X i ω|] ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  let M : Ω → ℝ := fun ω => Finset.univ.sup' hne (fun i => |X i ω|)
  change P[M] ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ
  have hX_ae_zero : ∀ i, X i =ᵐ[P] 0 := by
    intro i
    have hvle : Var[X i; P] ≤ 0 := by
      simpa [hσ0] using hvar i
    have hv0 : Var[X i; P] = 0 := le_antisymm hvle (variance_nonneg (X i) P)
    have h := ae_eq_integral_of_variance_eq_zero (hX i).memLp_two hv0
    filter_upwards [h] with ω hω
    exact hω.trans (hcent i)
  have hM_ae_zero : M =ᵐ[P] fun _ => 0 := by
    have hall : ∀ᵐ ω ∂P, ∀ i ∈ (Finset.univ : Finset (Fin n)), X i ω = 0 :=
      (Finset.eventually_all Finset.univ).mpr (fun i hi => hX_ae_zero i)
    filter_upwards [hall] with ω hω
    change Finset.univ.sup' hne (fun i => |X i ω|) = 0
    apply le_antisymm
    · refine Finset.sup'_le hne (fun i => |X i ω|) (fun i hi => ?_)
      rw [hω i hi]
      simp
    · exact (Finset.le_sup'_iff hne).mpr
        ⟨⟨0, hn⟩, Finset.mem_univ _, abs_nonneg (X ⟨0, hn⟩ ω)⟩
  calc
    ∫ ω, M ω ∂P = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hM_ae_zero
    _ = 0 := by simp
    _ ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
      rw [hσ0]
      simp

/-- Lemma 3.3, p. 10: if `X_1, …, X_n` (`n ≥ 1`, not necessarily independent) are centered
Gaussian random variables with variances at most `σ²`, then
`E[max_{1 ≤ i ≤ n} |X_i|] ≤ 2 √(2 log(2n)) · σ` (natural logarithm). -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hcent : ∀ i, P[X i] = 0) {σ : ℝ} (hσ : 0 ≤ σ) (hvar : ∀ i, Var[X i; P] ≤ σ ^ 2) :
    P[fun ω => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i => |X i ω|]
      ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
  by_cases hσ0 : σ = 0
  · exact lemma_3_3_zero hn X hX hcent hσ hσ0 hvar
  · exact lemma_3_3_pos hn X hX hcent hσ (lt_of_le_of_ne hσ (Ne.symm hσ0)) hvar

end FBMStrongSim.RecordBreak

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hcent : ∀ i, P[X i] = 0) {σ : ℝ} (hσ : 0 ≤ σ) (hvar : ∀ i, Var[X i; P] ≤ σ ^ 2) :
    P[fun ω => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i => |X i ω|]
      ≤ 2 * Real.sqrt (2 * Real.log (2 * n)) * σ := by
  exact Prove2SwarmSubmission.FBMStrongSim.RecordBreak.lemma_3_3 hn X hX hcent hσ hvar
