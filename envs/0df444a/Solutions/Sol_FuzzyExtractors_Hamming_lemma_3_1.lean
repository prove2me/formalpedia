-- Prove2me | solution 1 for FuzzyExtractors.Hamming.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:40:40.350476+00:00
-- url     : https://prove2.me/submissions/9d0a5b41-19ef-4259-a9f3-643c2bc07311

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
set_option autoImplicit false
open FuzzyExtractors.Hamming
open scoped ENNReal

lemma ss_withSketchAux_apply {M S ι : Type} (SS : M → PMF S) (WI : PMF (M × ι))
    (w : M) (s : S) (i : ι) :
    withSketchAux SS WI (w, (s, i)) = WI (w, i) * SS w s := by
  unfold withSketchAux
  rw [PMF.bind_apply, tsum_eq_single (w, i)]
  · rw [PMF.map_apply, tsum_eq_single s]
    · simp
    · intro s' hs'
      have : ¬ ((w, (s, i)) = (w, (s', i))) := by
        intro h
        have h' : s = s' := by simpa using h
        exact hs' h'.symm
      simp [this]
  · intro p hp
    rw [PMF.map_apply]
    have : ∀ s', ¬ ((w, (s, i)) = (p.1, (s', p.2))) := by
      intro s' h
      apply hp
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.symm h.2.2.symm
    simp [this]

theorem solution {M S : Type} (dis : M → M → ℕ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hcorr : SketchCorrect dis t SS Rec) (lam : ℝ)
    (hrange : ∃ T : Finset S, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ w, (SS w).support ⊆ (T : Set S)) :
    ∀ m : ℝ, IsAvgSecureSketch dis m (m - lam) t SS Rec := by
  intro m
  refine ⟨hcorr, ?_⟩
  intro ι WI hm
  obtain ⟨T, hTcard, hT⟩ := hrange
  classical
  set A : ℝ≥0∞ := ∑' i : ι, ⨆ w : M, WI (w, i) with hA
  set A' : ℝ≥0∞ := ∑' x : S × ι, ⨆ w : M, withSketchAux SS WI (w, x) with hA'
  have hAeq : avgMinEntropy WI = -Real.logb 2 A.toReal := rfl
  have hA'eq : avgMinEntropy (withSketchAux SS WI) = -Real.logb 2 A'.toReal := rfl
  -- A ≤ 1
  have hA1 : A ≤ 1 := by
    calc A ≤ ∑' i : ι, ∑' w : M, WI (w, i) := by
          refine ENNReal.tsum_le_tsum fun i => iSup_le fun w => ?_
          exact ENNReal.le_tsum (f := fun w => WI (w, i)) w
      _ = ∑' p : M × ι, WI p := by
          rw [ENNReal.tsum_comm]
          exact (ENNReal.tsum_prod (f := fun w i => WI (w, i))).symm
      _ = 1 := WI.tsum_coe
  obtain ⟨⟨w0, i0⟩, hp0⟩ := WI.support_nonempty
  have hp0' : WI (w0, i0) ≠ 0 := hp0
  obtain ⟨s0, hs0⟩ := (SS w0).support_nonempty
  have hs0' : SS w0 s0 ≠ 0 := hs0
  have hApos : 0 < A := by
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hp0') ?_
    refine le_trans (le_iSup (fun w => WI (w, i0)) w0) ?_
    exact ENNReal.le_tsum i0
  have hA'pos : 0 < A' := by
    have : withSketchAux SS WI (w0, (s0, i0)) ≠ 0 := by
      rw [ss_withSketchAux_apply]; exact mul_ne_zero hp0' hs0'
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr this) ?_
    refine le_trans (le_iSup (fun w => withSketchAux SS WI (w, (s0, i0))) w0) ?_
    exact ENNReal.le_tsum (f := fun x : S × ι => ⨆ w : M, withSketchAux SS WI (w, x)) (s0, i0)
  -- main bound
  have hbound : A' ≤ (T.card : ℝ≥0∞) * A := by
    have h1 : A' = ∑' s : S, ∑' i : ι, ⨆ w : M, WI (w, i) * SS w s := by
      rw [hA']
      refine Eq.trans (ENNReal.tsum_prod (f := fun s i => ⨆ w : M, withSketchAux SS WI (w, (s, i)))) ?_
      refine tsum_congr fun s => tsum_congr fun i => ?_
      simp_rw [ss_withSketchAux_apply]
    rw [h1]
    have h2 : ∀ s i, (⨆ w : M, WI (w, i) * SS w s) ≤ (if s ∈ T then 1 else 0) * ⨆ w : M, WI (w, i) := by
      intro s i
      refine iSup_le fun w => ?_
      by_cases hs : s ∈ T
      · simp only [hs, if_true, one_mul]
        calc WI (w, i) * SS w s ≤ WI (w, i) * 1 :=
              mul_le_mul' le_rfl (PMF.coe_le_one _ _)
          _ ≤ _ := by rw [mul_one]; exact le_iSup (fun w => WI (w, i)) w
      · have : SS w s = 0 := by
          by_contra h
          exact hs (hT w ((PMF.mem_support_iff _ _).mpr h))
        simp [hs, this]
    calc ∑' s : S, ∑' i : ι, ⨆ w : M, WI (w, i) * SS w s
        ≤ ∑' s : S, ∑' i : ι, (if s ∈ T then 1 else 0) * ⨆ w : M, WI (w, i) :=
          ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum fun i => h2 s i
      _ = ∑' s : S, (if s ∈ T then 1 else 0) * A := by
          refine tsum_congr fun s => ?_
          rw [ENNReal.tsum_mul_left]
      _ = (T.card : ℝ≥0∞) * A := by
          rw [ENNReal.tsum_mul_right]
          congr 1
          rw [tsum_eq_sum (s := T)]
          · simp
          · intro s hs; simp [hs]
  -- pass to reals
  have hAne : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hA1
  have hAreal_pos : 0 < A.toReal := ENNReal.toReal_pos hApos.ne' hAne
  have hA'ne : A' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hbound
  have hA'real_pos : 0 < A'.toReal := ENNReal.toReal_pos hA'pos.ne' hA'ne
  have hreal : A'.toReal ≤ (T.card : ℝ) * A.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hbound
    simpa using this
  rw [hAeq] at hm
  have hAle : A.toReal ≤ (2:ℝ) ^ (-m) := by
    have : Real.logb 2 A.toReal ≤ -m := by linarith
    exact (Real.logb_le_iff_le_rpow (by norm_num) hAreal_pos).mp this
  have hfin : A'.toReal ≤ (2:ℝ) ^ (lam - m) := by
    calc A'.toReal ≤ (T.card : ℝ) * A.toReal := hreal
      _ ≤ (2:ℝ) ^ lam * (2:ℝ) ^ (-m) :=
          mul_le_mul hTcard hAle hAreal_pos.le (by positivity)
      _ = (2:ℝ) ^ (lam - m) := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf
  have : Real.logb 2 A'.toReal ≤ lam - m :=
    (Real.logb_le_iff_le_rpow (by norm_num) hA'real_pos).mpr hfin
  rw [hA'eq]
  linarith
