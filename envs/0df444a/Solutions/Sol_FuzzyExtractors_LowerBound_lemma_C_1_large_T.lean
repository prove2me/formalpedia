-- Prove2me | solution 1 for FuzzyExtractors.LowerBound.lemma_C_1_large_T
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:48.096997+00:00
-- url     : https://prove2.me/submissions/57fcb5ba-67bb-433e-a51c-e1a553134222

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_FuzzyExtractors_LowerBound_Basic
set_option autoImplicit false
open FuzzyExtractors.Hamming FuzzyExtractors.LowerBound
open scoped ENNReal

lemma ss_withSketch_apply {M S : Type} (SS : M → PMF S) (W : PMF M) (w : M) (s : S) :
    withSketch SS W (w, s) = W w * SS w s := by
  unfold withSketch
  rw [PMF.bind_apply, tsum_eq_single w]
  · rw [PMF.map_apply, tsum_eq_single s]
    · simp
    · intro s' hs'
      have : ¬ ((w, s) = (w, s')) := by
        intro h
        have h' : s = s' := by simpa using h
        exact hs' h'.symm
      simp [this]
  · intro w' hw'
    rw [PMF.map_apply]
    have : ∀ s', ¬ ((w, s) = (w', s')) := by
      intro s' h
      apply hw'
      simp only [Prod.mk.injEq] at h
      exact h.1.symm
    simp [this]

theorem solution {M V : Type} [Fintype M] (SS : M → PMF V) (S : Finset M)
    (hS : S.Nonempty) (m' : ℝ)
    (h : m' ≤ FuzzyExtractors.Hamming.avgMinEntropy (FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFinset S hS))) :
    ∃ v : V, (2 : ℝ) ^ m' ≤ ((producers SS S v).card : ℝ) := by
  classical
  set W := PMF.uniformOfFinset S hS with hW
  have hWw : ∀ w, w ∈ S → W w = (S.card : ℝ≥0∞)⁻¹ := by
    intro w hw
    rw [hW, PMF.uniformOfFinset_apply_of_mem hS hw]
  have hWn : ∀ w, w ∉ S → W w = 0 := by
    intro w hw
    rw [hW, PMF.uniformOfFinset_apply_of_notMem hS hw]
  obtain ⟨w0, hw0⟩ := hS
  obtain ⟨v0, hv0⟩ := (SS w0).support_nonempty
  haveI : Nonempty V := ⟨v0⟩
  have hbdd : BddAbove (Set.range fun v : V => (producers SS S v).card) := by
    refine ⟨S.card, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨vstar, hvstar⟩ : ∃ vs : V, ∀ v : V, (producers SS S v).card ≤ (producers SS S vs).card := by
    obtain ⟨vs, hvs⟩ := Nat.sSup_mem (Set.range_nonempty (fun v : V => (producers SS S v).card)) hbdd
    refine ⟨vs, fun v => ?_⟩
    have := le_csSup hbdd (Set.mem_range_self v)
    rw [← hvs] at this
    exact this
  refine ⟨vstar, ?_⟩
  set N : ℕ := (producers SS S vstar).card with hN
  have hNpos : 0 < N := by
    have : w0 ∈ producers SS S v0 := by
      simp only [producers, Finset.mem_filter]; exact ⟨hw0, hv0⟩
    have h1 : 0 < (producers SS S v0).card := Finset.card_pos.mpr ⟨w0, this⟩
    exact lt_of_lt_of_le h1 (hvstar v0)
  set A : ℝ≥0∞ := ∑' v : V, ⨆ w : M, withSketch SS W (w, v) with hA
  have hAeq : avgMinEntropy (withSketch SS W) = -Real.logb 2 A.toReal := rfl
  -- 1 ≤ N * A
  have hv : ∀ v : V, ∑ w ∈ S, W w * SS w v ≤ (N : ℝ≥0∞) * ⨆ w : M, withSketch SS W (w, v) := by
    intro v
    have h1 : ∑ w ∈ S, W w * SS w v = ∑ w ∈ producers SS S v, W w * SS w v := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro w hwS hwnp
      have : SS w v = 0 := by
        by_contra hne
        exact hwnp (by simp only [producers, Finset.mem_filter]; exact ⟨hwS, (PMF.mem_support_iff _ _).mpr hne⟩)
      simp [this]
    rw [h1]
    calc ∑ w ∈ producers SS S v, W w * SS w v
        ≤ ∑ w ∈ producers SS S v, ⨆ w' : M, withSketch SS W (w', v) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← ss_withSketch_apply]
          exact le_iSup (fun w' => withSketch SS W (w', v)) w
      _ = ((producers SS S v).card : ℝ≥0∞) * ⨆ w' : M, withSketch SS W (w', v) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ≥0∞) * ⨆ w' : M, withSketch SS W (w', v) := by
          gcongr
          exact_mod_cast hvstar v
  have hone : 1 ≤ (N : ℝ≥0∞) * A := by
    have h1 : ∑' v : V, ∑ w ∈ S, W w * SS w v ≤ ∑' v : V, (N : ℝ≥0∞) * ⨆ w : M, withSketch SS W (w, v) :=
      ENNReal.tsum_le_tsum hv
    rw [ENNReal.tsum_mul_left] at h1
    have h2 : ∑' v : V, ∑ w ∈ S, W w * SS w v = 1 := by
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      have : ∀ w ∈ S, ∑' v : V, W w * SS w v = W w := by
        intro w _
        rw [ENNReal.tsum_mul_left, (SS w).tsum_coe, mul_one]
      rw [Finset.sum_congr rfl this]
      have hcard : (S.card : ℝ≥0∞) ≠ 0 := by
        have : 0 < S.card := Finset.card_pos.mpr ⟨w0, hw0⟩
        exact_mod_cast this.ne'
      rw [Finset.sum_congr rfl (fun w hw => hWw w hw), Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _)
    rw [h2] at h1
    exact h1
  -- A finite
  have hA1 : A ≤ 1 := by
    calc A ≤ ∑' v : V, ∑' w : M, withSketch SS W (w, v) := by
          refine ENNReal.tsum_le_tsum fun v => iSup_le fun w => ?_
          exact ENNReal.le_tsum (f := fun w => withSketch SS W (w, v)) w
      _ = ∑' p : M × V, withSketch SS W p := by
          rw [ENNReal.tsum_comm]
          exact (ENNReal.tsum_prod (f := fun w v => withSketch SS W (w, v))).symm
      _ = 1 := (withSketch SS W).tsum_coe
  have hAne : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hA1
  have hreal : 1 ≤ (N : ℝ) * A.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hone
    simpa using this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hApos : 0 < A.toReal := by
    by_contra hcon
    have : A.toReal = 0 := le_antisymm (not_lt.mp hcon) ENNReal.toReal_nonneg
    rw [this] at hreal; exact absurd hreal (by norm_num)
  rw [hAeq] at h
  have h3 : Real.logb 2 (1 / (N : ℝ)) ≤ Real.logb 2 A.toReal := by
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [div_le_iff₀ hNr]; linarith
  have h4 : Real.logb 2 (1 / (N : ℝ)) = - Real.logb 2 N := by
    rw [one_div, Real.logb_inv]
  have h5 : m' ≤ Real.logb 2 N := by linarith
  calc (2 : ℝ) ^ m' ≤ (2 : ℝ) ^ (Real.logb 2 N) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
    _ = N := Real.rpow_logb (by norm_num) (by norm_num) hNr
