-- Prove2me | solution 1 for BootRobust.NWDual.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:45:46.565753+00:00
-- url     : https://prove2.me/submissions/ca7ecdb1-c770-4c9c-a717-18fce6f1e360

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

set_option autoImplicit false

namespace P0566

variable {ι : Type*} [Fintype ι]

lemma sum_exp_pos (D g : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) :
    0 < ∑ i, Real.exp (g i) * D i := by
  obtain ⟨hnn, hsum⟩ := hD
  apply Finset.sum_pos'
  · intro i _; exact mul_nonneg (Real.exp_pos _).le (hnn i)
  · by_contra hcon
    push Not at hcon
    have h0 : ∀ i, D i = 0 := by
      intro i
      have h1 := hcon i (Finset.mem_univ i)
      have h2 := mul_nonneg (Real.exp_pos (g i)).le (hnn i)
      have h3 : Real.exp (g i) * D i = 0 := le_antisymm h1 h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (Real.exp_pos _).ne'
      · exact h
    simp [h0] at hsum

/-- Gibbs variational inequality. -/
lemma gibbs (D D' g : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hD' : D' ∈ stdSimplex ℝ ι)
    (hac : ∀ i, D i = 0 → D' i = 0) :
    ∑ i, g i * D' i ≤ ∑ i, D' i * Real.log (D' i / D i) +
      Real.log (∑ i, Real.exp (g i) * D i) := by
  have hSpos := sum_exp_pos D g hD
  set S := ∑ i, Real.exp (g i) * D i with hS
  obtain ⟨hnn, hsum⟩ := hD
  obtain ⟨hnn', hsum'⟩ := hD'
  have key : ∀ i, D' i * (g i - Real.log (D' i / D i)) - D' i * Real.log S ≤
      Real.exp (g i) * D i / S - D' i := by
    intro i
    rcases (hnn' i).eq_or_lt with h0 | hpos
    · rw [← h0]
      have : 0 ≤ Real.exp (g i) * D i / S :=
        div_nonneg (mul_nonneg (Real.exp_pos _).le (hnn i)) hSpos.le
      simp [this]
    · have hDpos : 0 < D i := by
        rcases (hnn i).eq_or_lt with h | h
        · exact absurd (hac i h.symm) hpos.ne'
        · exact h
      have hx : 0 < Real.exp (g i) * D i / (S * D' i) := by positivity
      have hl := Real.log_le_sub_one_of_pos hx
      have hlog : Real.log (Real.exp (g i) * D i / (S * D' i)) =
          g i + Real.log (D i) - Real.log S - Real.log (D' i) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_exp]
        ring
      rw [hlog] at hl
      have h2 := mul_le_mul_of_nonneg_left hl hpos.le
      have h3 : D' i * (Real.exp (g i) * D i / (S * D' i) - 1) =
          Real.exp (g i) * D i / S - D' i := by
        field_simp
      rw [h3] at h2
      rw [Real.log_div hpos.ne' hDpos.ne']
      nlinarith [h2]
  have hsm := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  have e1 : ∑ i, Real.exp (g i) * D i / S = 1 := by
    rw [← Finset.sum_div]; exact div_self hSpos.ne'
  have e2 : ∑ i, (D' i * (g i - Real.log (D' i / D i)) - D' i * Real.log S) =
      ∑ i, g i * D' i - ∑ i, D' i * Real.log (D' i / D i) - Real.log S := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum']
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp [mul_comm]
  rw [e2, Finset.sum_sub_distrib, e1, hsum'] at hsm
  linarith


/-- partition function -/
noncomputable def F (D f : ι → ℝ) (l : ℝ) : ℝ := ∑ i, Real.exp (l * f i) * D i

lemma F_pos (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (l : ℝ) : 0 < F D f l :=
  sum_exp_pos D (fun i => l * f i) hD

lemma F_zero (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) : F D f 0 = 1 := by
  simp [F, hD.2]

lemma F_hasDeriv (D f : ι → ℝ) (l : ℝ) :
    HasDerivAt (F D f) (∑ i, f i * (Real.exp (l * f i) * D i)) l := by
  have h : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt (fun l : ℝ => Real.exp (l * f i) * D i)
      (f i * (Real.exp (l * f i) * D i)) l := by
    intro i _
    have h1 : HasDerivAt (fun l : ℝ => l * f i) (f i) l := by
      simpa using (hasDerivAt_id l).mul_const (f i)
    have h2 := (h1.exp).mul_const (D i)
    refine h2.congr_deriv ?_
    ring
  exact HasDerivAt.fun_sum h

lemma F_continuous (D f : ι → ℝ) : Continuous (F D f) :=
  continuous_iff_continuousAt.2 fun l => (F_hasDeriv D f l).continuousAt

/-- the exponentially tilted distribution -/
noncomputable def tilt (D f : ι → ℝ) (l : ℝ) : ι → ℝ :=
  fun i => Real.exp (l * f i) * D i / F D f l

lemma tilt_simplex (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (l : ℝ) :
    tilt D f l ∈ stdSimplex ℝ ι := by
  refine ⟨fun i => div_nonneg (mul_nonneg (Real.exp_pos _).le (hD.1 i)) (F_pos D f hD l).le, ?_⟩
  unfold tilt
  rw [← Finset.sum_div]
  exact div_self (F_pos D f hD l).ne'

lemma tilt_ac (D f : ι → ℝ) (l : ℝ) (i : ι) (h : D i = 0) : tilt D f l i = 0 := by
  simp [tilt, h]

lemma tilt_kl (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (l : ℝ) :
    ∑ i, tilt D f l i * Real.log (tilt D f l i / D i) =
      l * ∑ i, f i * tilt D f l i - Real.log (F D f l) := by
  have hF := F_pos D f hD l
  have hs := (tilt_simplex D f hD l).2
  have key : ∀ i, tilt D f l i * Real.log (tilt D f l i / D i) =
      l * (f i * tilt D f l i) - Real.log (F D f l) * tilt D f l i := by
    intro i
    by_cases h : D i = 0
    · simp [tilt_ac D f l i h]
    · have hDpos : 0 < D i := lt_of_le_of_ne (hD.1 i) (Ne.symm h)
      have : tilt D f l i / D i = Real.exp (l * f i) / F D f l := by
        unfold tilt; field_simp
      rw [this, Real.log_div (Real.exp_pos _).ne' hF.ne', Real.log_exp]
      ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hs]
  ring


def Good (D f : ι → ℝ) (r : ℝ) : Prop :=
  ∃ D' : ι → ℝ, D' ∈ stdSimplex ℝ ι ∧ (∀ i, D i = 0 → D' i = 0) ∧
    ∑ i, D' i * Real.log (D' i / D i) ≤ r ∧ 0 ≤ ∑ i, f i * D' i

lemma strong_nonpos (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
    (H : ∀ l : ℝ, 0 < l → Real.exp (-r) < F D f l)
    (hf : ∀ i, 0 < D i → f i ≤ 0) : Good D f r := by
  classical
  set p0 : ℝ := ∑ i, (if f i = 0 then D i else 0) with hp0
  by_cases h : Real.exp (-r) ≤ p0
  · have hp0pos : 0 < p0 := lt_of_lt_of_le (Real.exp_pos _) h
    refine ⟨fun i => if f i = 0 then D i / p0 else 0, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs
      · exact div_nonneg (hD.1 i) hp0pos.le
      · exact le_rfl
    · have : ∑ i, (if f i = 0 then D i / p0 else 0) = p0 / p0 := by
        rw [hp0, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      rw [this, div_self hp0pos.ne']
    · intro i hi; simp [hi]
    · have key : ∀ i, (if f i = 0 then D i / p0 else 0) *
          Real.log ((if f i = 0 then D i / p0 else 0) / D i) =
          (if f i = 0 then D i else 0) / p0 * Real.log (p0⁻¹) := by
        intro i
        by_cases hf0 : f i = 0
        · by_cases hDi : D i = 0
          · simp [hf0, hDi]
          · simp only [hf0, if_true]
            have : D i / p0 / D i = p0⁻¹ := by field_simp
            rw [this]
        · simp [hf0]
      rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.sum_mul, ← Finset.sum_div, ← hp0,
        div_self hp0pos.ne', one_mul, Real.log_inv]
      have : -r ≤ Real.log p0 := by
        calc -r = Real.log (Real.exp (-r)) := (Real.log_exp _).symm
          _ ≤ Real.log p0 := Real.log_le_log (Real.exp_pos _) h
      linarith
    · have : ∀ i, f i * (if f i = 0 then D i / p0 else 0) = 0 := by
        intro i; by_cases hf0 : f i = 0 <;> simp [hf0]
      simp [this]
  · push Not at h
    exfalso
    have hT : Filter.Tendsto (fun l : ℝ => F D f l) Filter.atTop (nhds p0) := by
      unfold F
      rw [hp0]
      apply tendsto_finsetSum
      intro i _
      by_cases hDi : D i = 0
      · simp [hDi]
      · have hDpos : 0 < D i := lt_of_le_of_ne (hD.1 i) (Ne.symm hDi)
        by_cases hf0 : f i = 0
        · simp [hf0]
        · have hneg : f i < 0 := lt_of_le_of_ne (hf i hDpos) hf0
          simp only [hf0, if_false]
          have h1 : Filter.Tendsto (fun l : ℝ => l * f i) Filter.atTop Filter.atBot :=
            Filter.tendsto_id.atTop_mul_const_of_neg hneg
          have h2 := (Real.tendsto_exp_atBot.comp h1).mul_const (D i)
          simpa using h2
    obtain ⟨l, hl1, hl2⟩ :=
      ((hT.eventually (gt_mem_nhds h)).and (Filter.eventually_gt_atTop 0)).exists
    exact absurd (H l hl2) (not_lt.2 hl1.le)

lemma strong_pos (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
    (H : ∀ l : ℝ, 0 < l → Real.exp (-r) < F D f l)
    (hneg : ∑ i, f i * D i < 0) (j : ι) (hj : 0 < D j) (hfj : 0 < f j) : Good D f r := by
  have hT : Filter.Tendsto (fun l : ℝ => Real.exp (l * f j) * D j) Filter.atTop Filter.atTop :=
    (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.atTop_mul_const hfj)).atTop_mul_const hj
  obtain ⟨l1, hl1, hl1pos⟩ :=
    ((hT.eventually_gt_atTop 1).and (Filter.eventually_gt_atTop 0)).exists
  have hFl1 : 1 < F D f l1 := lt_of_lt_of_le hl1
    (Finset.single_le_sum (f := fun i => Real.exp (l1 * f i) * D i)
      (fun i _ => mul_nonneg (Real.exp_pos _).le (hD.1 i)) (Finset.mem_univ j))
  have hd := F_hasDeriv D f 0
  have hd0 : ∑ i, f i * (Real.exp (0 * f i) * D i) = ∑ i, f i * D i := by simp
  rw [hd0] at hd
  have hs := hd.tendsto_slope_zero_right
  obtain ⟨t0, ht1, ht2⟩ :=
    ((hs.eventually (gt_mem_nhds hneg)).and (Ioo_mem_nhdsGT hl1pos)).exists
  have hFt0 : F D f t0 < 1 := by
    have hpos : 0 < t0⁻¹ := inv_pos.2 ht2.1
    simp only [zero_add, smul_eq_mul, F_zero D f hD] at ht1
    by_contra hge
    push Not at hge
    have : 0 ≤ t0⁻¹ * (F D f t0 - 1) := mul_nonneg hpos.le (by linarith)
    linarith
  obtain ⟨ls, hls, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hl1pos.le)
    (F_continuous D f).continuousOn
  have hFls : F D f ls < 1 :=
    lt_of_le_of_lt (isMinOn_iff.1 hmin _ (Set.mem_Icc.2 ⟨ht2.1.le, ht2.2.le⟩)) hFt0
  have hls0 : 0 < ls := by
    rcases hls.1.eq_or_lt with h | h
    · rw [← h, F_zero D f hD] at hFls; exact absurd hFls (lt_irrefl 1)
    · exact h
  have hlsl : ls < l1 := by
    rcases hls.2.eq_or_lt with h | h
    · rw [h] at hFls; linarith
    · exact h
  have hloc : IsLocalMin (F D f) ls := hmin.isLocalMin (Icc_mem_nhds hls0 hlsl)
  have hder : ∑ i, f i * (Real.exp (ls * f i) * D i) = 0 :=
    hloc.hasDerivAt_eq_zero (F_hasDeriv D f ls)
  have h0 : ∑ i, f i * tilt D f ls i = 0 := by
    have : ∑ i, f i * tilt D f ls i =
        (∑ i, f i * (Real.exp (ls * f i) * D i)) / F D f ls := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      unfold tilt
      ring
    rw [this, hder, zero_div]
  refine ⟨tilt D f ls, tilt_simplex D f hD ls, tilt_ac D f ls, ?_, h0.ge⟩
  rw [tilt_kl D f hD, h0]
  have h3 : -r < Real.log (F D f ls) :=
    (Real.lt_log_iff_exp_lt (F_pos D f hD ls)).2 (H ls hls0)
  linarith

lemma strong (D f : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ) (hr : 0 ≤ r)
    (H : ∀ l : ℝ, 0 < l → Real.exp (-r) < F D f l) : Good D f r := by
  by_cases h1 : 0 ≤ ∑ i, f i * D i
  · refine ⟨D, hD, fun i h => h, ?_, h1⟩
    have : ∀ i, D i * Real.log (D i / D i) = 0 := by
      intro i
      by_cases h : D i = 0
      · simp [h]
      · simp [div_self h]
    simp [hr]
  · push Not at h1
    by_cases h2 : ∃ j, 0 < D j ∧ 0 < f j
    · obtain ⟨j, hj, hfj⟩ := h2
      exact strong_pos D f hD r H h1 j hj hfj
    · exact strong_nonpos D f hD r H (fun i hi => by
        by_contra hc; exact h2 ⟨i, hi, not_le.1 hc⟩)


lemma ball_iff [DecidableEq ι] (D D' : ι → ℝ) (r : ℝ) :
    BootRobust.Perf.bootDist D' D ≤ (r : EReal) ↔
      (∀ i, D i = 0 → D' i = 0) ∧ ∑ i, D' i * Real.log (D' i / D i) ≤ r := by
  by_cases h : ∀ i, D i = 0 → D' i = 0
  · rw [BootRobust.Perf.bootDist, if_pos h, EReal.coe_le_coe_iff]
    exact ⟨fun hh => ⟨h, hh⟩, fun hh => hh.2⟩
  · rw [BootRobust.Perf.bootDist, if_neg h]
    constructor
    · intro hh; exact absurd hh (by simp)
    · intro hh; exact absurd hh.1 h

lemma den_pos (w D' : ι → ℝ) (hw : ∀ i, 0 < w i) (hD' : D' ∈ stdSimplex ℝ ι) :
    0 < ∑ i, w i * D' i := by
  apply Finset.sum_pos'
  · intro i _; exact mul_nonneg (hw i).le (hD'.1 i)
  · by_contra hcon
    push Not at hcon
    have h0 : ∀ i, D' i = 0 := by
      intro i
      have h1 := hcon i (Finset.mem_univ i)
      have h2 := mul_nonneg (hw i).le (hD'.1 i)
      have h3 : w i * D' i = 0 := le_antisymm h1 h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (hw i).ne'
      · exact h
    have := hD'.2
    simp [h0] at this

end P0566

open BootRobust.NWDual in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    robustNW BootRobust.Perf.bootDist D r w (L z) = ⨅ α ∈ dualSet D r w (L z), (α : EReal) := by
  generalize L z = ℓ
  apply le_antisymm
  · unfold robustNW
    refine iSup₂_le fun D' hmem => ?_
    refine le_iInf₂ fun α hα => ?_
    obtain ⟨hs, hb⟩ := hmem
    obtain ⟨hac, hkl⟩ := (P0566.ball_iff D D' r).1 hb
    obtain ⟨ν, hν, hdual⟩ := hα
    have hg := P0566.gibbs D D' (fun i => (ℓ i - α) * w i / ν) hD hs hac
    have e1 : ∑ i, (ℓ i - α) * w i / ν * D' i =
        (∑ i, w i * ℓ i * D' i - α * ∑ i, w i * D' i) / ν := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [e1] at hg
    have h2 : (∑ i, w i * ℓ i * D' i - α * ∑ i, w i * D' i) / ν * ν =
        ∑ i, w i * ℓ i * D' i - α * ∑ i, w i * D' i := by field_simp
    have h3 : (∑ i, w i * ℓ i * D' i - α * ∑ i, w i * D' i) / ν * ν ≤
        (∑ i, D' i * Real.log (D' i / D i) +
          Real.log (∑ i, Real.exp ((ℓ i - α) * w i / ν) * D i)) * ν :=
      mul_le_mul_of_nonneg_right hg hν.le
    have h4 : (∑ i, D' i * Real.log (D' i / D i)) * ν ≤ r * ν :=
      mul_le_mul_of_nonneg_right hkl hν.le
    have h5 : ∑ i, w i * ℓ i * D' i ≤ α * ∑ i, w i * D' i := by nlinarith
    have h6 : BootRobust.Perf.nwEst w ℓ D' ≤ α := by
      unfold BootRobust.Perf.nwEst
      rw [div_le_iff₀ (P0566.den_pos w D' hw hs)]
      exact h5
    exact EReal.coe_le_coe_iff.2 h6
  · apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    obtain ⟨α, hcα, hαa⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    refine le_trans (iInf₂_le α ?_) hαa.le
    set f : ι → ℝ := fun i => (ℓ i - α) * w i with hf
    have hmain : ∃ l : ℝ, 0 < l ∧ P0566.F D f l ≤ Real.exp (-r) := by
      by_contra hno
      push Not at hno
      have H : ∀ l : ℝ, 0 < l → Real.exp (-r) < P0566.F D f l := hno
      rcases lt_or_ge r 0 with hr | hr
      · have h1 : P0566.F D f 0 < Real.exp (-r) := by
          rw [P0566.F_zero D f hD]
          exact Real.one_lt_exp_iff.2 (by linarith)
        have h2 : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), P0566.F D f x < Real.exp (-r) :=
          ((P0566.F_continuous D f).continuousAt.eventually (gt_mem_nhds h1)).filter_mono
            nhdsWithin_le_nhds
        obtain ⟨l, hl1, hl2⟩ := (h2.and self_mem_nhdsWithin).exists
        exact absurd (H l hl2) (not_lt.2 hl1.le)
      · obtain ⟨D', hs, hac, hkl, hpos⟩ := P0566.strong D f hD r hr H
        have hmem : D' ∈ {D' : ι → ℝ | D' ∈ stdSimplex ℝ ι ∧
            BootRobust.Perf.bootDist D' D ≤ (r : EReal)} :=
          ⟨hs, (P0566.ball_iff D D' r).2 ⟨hac, hkl⟩⟩
        have hle : ((BootRobust.Perf.nwEst w ℓ D' : ℝ) : EReal) ≤
            robustNW BootRobust.Perf.bootDist D r w ℓ :=
          le_iSup₂ (f := fun D' (_ : D' ∈ {D' : ι → ℝ | D' ∈ stdSimplex ℝ ι ∧
            BootRobust.Perf.bootDist D' D ≤ (r : EReal)}) =>
            ((BootRobust.Perf.nwEst w ℓ D' : ℝ) : EReal)) D' hmem
        have hlt : BootRobust.Perf.nwEst w ℓ D' < α :=
          EReal.coe_lt_coe_iff.1 (lt_of_le_of_lt hle hcα)
        unfold BootRobust.Perf.nwEst at hlt
        rw [div_lt_iff₀ (P0566.den_pos w D' hw hs)] at hlt
        have e : ∑ i, f i * D' i = ∑ i, w i * ℓ i * D' i - α * ∑ i, w i * D' i := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          simp only [hf]
          ring
        linarith
    obtain ⟨l, hl, hFl⟩ := hmain
    refine ⟨l⁻¹, inv_pos.2 hl, ?_⟩
    have hFpos := P0566.F_pos D f hD l
    have hlog : Real.log (P0566.F D f l) ≤ -r := (Real.log_le_iff_le_exp hFpos).2 hFl
    have e : ∑ i, Real.exp ((ℓ i - α) * w i / l⁻¹) * D i = P0566.F D f l := by
      unfold P0566.F
      apply Finset.sum_congr rfl
      intro i _
      have : (ℓ i - α) * w i / l⁻¹ = l * ((ℓ i - α) * w i) := by
        rw [div_inv_eq_mul, mul_comm]
      rw [this]
    rw [e]
    have : l⁻¹ * Real.log (P0566.F D f l) + r * l⁻¹ =
        l⁻¹ * (Real.log (P0566.F D f l) + r) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 hl).le (by linarith)
