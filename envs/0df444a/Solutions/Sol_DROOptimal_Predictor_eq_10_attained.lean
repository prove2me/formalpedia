-- Prove2me | solution 1 for DROOptimal.Predictor.eq_10_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:35:05.762357+00:00
-- url     : https://prove2.me/submissions/522f38e8-6eb6-47e5-8b86-1fdb2ff707fd

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

open Filter Topology

lemma coord_cont {d : ℕ} (i : Fin d) : Continuous (fun q : Δ d => (q : Fin d → ℝ) i) :=
  (continuous_apply i).comp continuous_subtype_val

lemma mul_log_div_ge_neg_one (p q : ℝ) (hp : 0 ≤ p) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    -1 ≤ p * Real.log (p / q) := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]; simp
  · rw [Real.log_div h.ne' hq0.ne']
    have h1 : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1
    have h2 : Real.log (1 / p) ≤ 1 / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [one_div, Real.log_inv] at h2
    have : p * (-Real.log p) ≤ p * (p⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 h.le
    rw [mul_sub, mul_inv_cancel₀ h.ne'] at this
    nlinarith

lemma relEntropy_lsc_snd {d : ℕ} (p : Δ d) : LowerSemicontinuous (fun q : Δ d => relEntropy p q) := by
  classical
  intro q y hy
  change y < relEntropy p q at hy
  have hp0 : ∀ i, 0 ≤ (p : Fin d → ℝ) i := fun i => p.2.1 i
  have hq0 : ∀ q : Δ d, ∀ i, 0 ≤ (q : Fin d → ℝ) i := fun q i => q.2.1 i
  have hq1 : ∀ q : Δ d, ∀ i, (q : Fin d → ℝ) i ≤ 1 := fun q i => by
    have := Finset.single_le_sum (fun j _ => q.2.1 j) (Finset.mem_univ i)
    rw [q.2.2] at this; exact this
  by_cases hc : ∀ i, (q : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0
  · -- finite case
    let F : Δ d → ℝ := fun q' => ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q' : Fin d → ℝ) i)
    have hFq : relEntropy p q = (F q : EReal) := by simp only [relEntropy, if_pos hc, F]
    have hcont : ContinuousAt F q := by
      show Tendsto (fun q' : Δ d => ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q' : Fin d → ℝ) i)) (𝓝 q) (𝓝 (∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q : Fin d → ℝ) i)))
      refine tendsto_finsetSum _ (fun i _ => ?_)
      by_cases hpi : (p : Fin d → ℝ) i = 0
      · simp only [hpi, zero_mul]; exact continuousAt_const
      · have hqi : (q : Fin d → ℝ) i ≠ 0 := fun h => hpi (hc i h)
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.log
        · exact continuousAt_const.div (coord_cont i).continuousAt hqi
        · exact div_ne_zero hpi hqi
    rw [hFq] at hy
    obtain ⟨R, hyR, hRF⟩ := EReal.lt_iff_exists_real_btwn.mp hy
    have hRF' : R < F q := by exact_mod_cast hRF
    have hev1 : ∀ᶠ q' : Δ d in 𝓝 q, R < F q' := hcont.eventually (lt_mem_nhds hRF')
    have hev2 : ∀ᶠ q' : Δ d in 𝓝 q, ∀ i, (q' : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0 := by
      rw [eventually_all]
      intro i
      by_cases hpi : (p : Fin d → ℝ) i = 0
      · exact Eventually.of_forall (fun _ _ => hpi)
      · have hqi : 0 < (q : Fin d → ℝ) i :=
          lt_of_le_of_ne (hq0 q i) (fun h => hpi (hc i h.symm))
        have := (coord_cont i).continuousAt.eventually (lt_mem_nhds hqi)
        exact this.mono (fun q' h h0 => absurd h0 (ne_of_gt h))
    filter_upwards [hev1, hev2] with q' h1 h2
    show y < relEntropy p q'
    simp only [relEntropy, if_pos h2]
    exact lt_trans hyR (by exact_mod_cast h1)
  · -- infinite case
    push Not at hc
    obtain ⟨j, hqj, hpj⟩ := hc
    have hpj' : 0 < (p : Fin d → ℝ) j := lt_of_le_of_ne (hp0 j) (Ne.symm hpj)
    -- a real bound R ≥ y
    obtain ⟨R, hR⟩ : ∃ R : ℝ, y ≤ (R : EReal) := by
      induction y using EReal.rec with
      | bot => exact ⟨0, bot_le⟩
      | coe a => exact ⟨a, le_rfl⟩
      | top => exact absurd hy (not_lt.mpr le_top)
    set A : ℝ := |R| + d + 1
    set δ : ℝ := (p : Fin d → ℝ) j * Real.exp (-(A / (p : Fin d → ℝ) j))
    have hδ : 0 < δ := mul_pos hpj' (Real.exp_pos _)
    have hev : ∀ᶠ q' : Δ d in 𝓝 q, (q' : Fin d → ℝ) j < δ := by
      have := (coord_cont j).continuousAt (x := q)
      apply this.eventually (gt_mem_nhds _)
      simpa [hqj] using hδ
    filter_upwards [hev] with q' hq'
    show y < relEntropy p q'
    by_cases hc' : ∀ i, (q' : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0
    · simp only [relEntropy, if_pos hc']
      refine lt_of_le_of_lt hR ?_
      have hpos : ∀ i, 0 < (p : Fin d → ℝ) i → 0 < (q' : Fin d → ℝ) i := fun i hi =>
        lt_of_le_of_ne (hq0 q' i) (fun h => hi.ne' (hc' i h.symm))
      have hqj' := hpos j hpj'
      -- each term ≥ -1
      have hterm : ∀ i, -1 ≤ (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q' : Fin d → ℝ) i) := by
        intro i
        rcases (hp0 i).eq_or_lt with h | h
        · rw [← h]; simp
        · exact mul_log_div_ge_neg_one _ _ (hp0 i) (hpos i h) (hq1 q' i)
      -- term j is large
      have hj : A < (p : Fin d → ℝ) j * Real.log ((p : Fin d → ℝ) j / (q' : Fin d → ℝ) j) := by
        have h1 : Real.log ((p : Fin d → ℝ) j / δ) < Real.log ((p : Fin d → ℝ) j / (q' : Fin d → ℝ) j) :=
          Real.log_lt_log (div_pos hpj' hδ) (div_lt_div_of_pos_left hpj' hqj' hq')
        have h2 : Real.log ((p : Fin d → ℝ) j / δ) = A / (p : Fin d → ℝ) j := by
          simp only [δ]
          rw [div_mul_eq_div_div, div_self hpj'.ne', one_div, Real.log_inv, Real.log_exp, neg_neg]
        rw [h2] at h1
        have := mul_lt_mul_of_pos_left h1 hpj'
        rwa [mul_div_cancel₀ _ hpj'.ne'] at this
      have hsum := Finset.single_le_sum (f := fun i =>
          (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q' : Fin d → ℝ) i) + 1)
        (fun i _ => by linarith [hterm i]) (Finset.mem_univ j)
      rw [Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
      have : R < ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (q' : Fin d → ℝ) i) := by
        have := le_abs_self R
        simp only [A] at hj
        linarith
      exact_mod_cast this
    · simp only [relEntropy, if_neg hc']
      exact lt_of_le_of_lt hR (EReal.coe_lt_top R)

lemma relEntropy_self {d : ℕ} (p : Δ d) : relEntropy p p = 0 := by
  classical
  have hc : ∀ i, (p : Fin d → ℝ) i = 0 → (p : Fin d → ℝ) i = 0 := fun _ h => h
  simp only [relEntropy, if_pos hc]
  have : ∑ i, (p : Fin d → ℝ) i * Real.log ((p : Fin d → ℝ) i / (p : Fin d → ℝ) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : (p : Fin d → ℝ) i = 0
    · simp [h]
    · simp [div_self h]
  rw [this]; rfl

end DROOptimal.Predictor

open DROOptimal.Predictor

theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) (x : ↥X) (ℙ' : Δ d) :
    ∃ ℙ₀ : Δ d, relEntropy ℙ' ℙ₀ ≤ (r : EReal) ∧ drPredictor γ r x ℙ' = cost γ x ℙ₀ := by
  set S : Set (Δ d) := {ℙ : Δ d | relEntropy ℙ' ℙ ≤ (r : EReal)}
  have hS : IsClosed S := (relEntropy_lsc_snd ℙ').isClosed_preimage (r : EReal)
  have : CompactSpace (Δ d) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin d))
  have hSc : IsCompact S := hS.isCompact
  have hne : S.Nonempty := ⟨ℙ', by show relEntropy ℙ' ℙ' ≤ _; rw [relEntropy_self]; exact_mod_cast hr⟩
  have hcont : Continuous (fun ℙ : Δ d => cost γ x ℙ) := by
    unfold cost
    exact continuous_finsetSum _ (fun i _ => (coord_cont i).mul continuous_const)
  obtain ⟨ℙ₀, hmem, hmax⟩ := hSc.exists_isMaxOn hne hcont.continuousOn
  refine ⟨ℙ₀, hmem, ?_⟩
  unfold drPredictor
  apply IsGreatest.csSup_eq
  refine ⟨⟨ℙ₀, hmem, rfl⟩, ?_⟩
  rintro _ ⟨ℙ, hℙ, rfl⟩
  exact hmax hℙ
