-- Prove2me | solution 1 for BanditAlgorithm.klucb_index_threshold_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T04:02:30.675562+00:00
-- url     : https://prove2.me/submissions/5f6a23bd-2f7a-408f-bf20-85134ad24b5f

import Definitions.Def_klucbTruncatedRelativeEntropy
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set Filter Topology

namespace BanditAlgorithm

private lemma hasDerivAt_bernoulliRelativeEntropy_snd
    {p x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun q ↦ bernoulliRelativeEntropy p q)
      ((x - p) / (x * (1 - x))) x := by
  have hx1' : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have honeSub : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x :=
    (hasDerivAt_id' x).const_sub 1
  have hlogOneSub :
      HasDerivAt (fun y : ℝ ↦ Real.log (1 - y)) (-1 / (1 - x)) x :=
    honeSub.log hx1'
  have hlogx : HasDerivAt (fun y : ℝ ↦ Real.log y) (1 / x) x :=
    (hasDerivAt_id' x).log hx0
  rcases eq_or_ne p 0 with rfl | hp0
  · have hbase : HasDerivAt (fun y : ℝ ↦ -Real.log (1 - y))
        (-(-1 / (1 - x))) x := hlogOneSub.neg
    have heq : (fun y : ℝ ↦ bernoulliRelativeEntropy 0 y) =ᶠ[𝓝 x]
        fun y ↦ -Real.log (1 - y) := by
      filter_upwards [eventually_ne_nhds hx1] with y hy
      simp [bernoulliRelativeEntropy, Real.log_inv,
        sub_ne_zero.mpr hy.symm]
    refine (hbase.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [neg_div, neg_neg, sub_zero, div_eq_div_iff hx1' (mul_ne_zero hx0 hx1')]
    ring
  rcases eq_or_ne p 1 with rfl | hp1
  · have hbase : HasDerivAt (fun y : ℝ ↦ -Real.log y) (-(1 / x)) x :=
      hlogx.neg
    have heq : (fun y : ℝ ↦ bernoulliRelativeEntropy 1 y) =ᶠ[𝓝 x]
        fun y ↦ -Real.log y := by
      filter_upwards [eventually_ne_nhds hx0] with y hy
      simp [bernoulliRelativeEntropy, Real.log_inv, hy]
    refine (hbase.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [neg_div', div_eq_div_iff hx0 (mul_ne_zero hx0 hx1')]
    ring
  · have hfirst :
        HasDerivAt (fun y : ℝ ↦ p * (Real.log p - Real.log y))
          (p * (0 - 1 / x)) x :=
      ((hasDerivAt_const x (Real.log p)).sub hlogx).const_mul p
    have hsecond :
        HasDerivAt
          (fun y : ℝ ↦
            (1 - p) * (Real.log (1 - p) - Real.log (1 - y)))
          ((1 - p) * (0 - -1 / (1 - x))) x :=
      ((hasDerivAt_const x (Real.log (1 - p))).sub hlogOneSub).const_mul
        (1 - p)
    have hbase := hfirst.add hsecond
    have heq :
        (fun y : ℝ ↦ bernoulliRelativeEntropy p y) =ᶠ[𝓝 x]
          fun y ↦ p * (Real.log p - Real.log y) +
            (1 - p) * (Real.log (1 - p) - Real.log (1 - y)) := by
      filter_upwards [eventually_ne_nhds hx0,
        eventually_ne_nhds hx1] with y hy0 hy1
      rw [bernoulliRelativeEntropy,
        Real.log_div hp0 hy0,
        Real.log_div (sub_ne_zero.mpr hp1.symm)
          (sub_ne_zero.mpr hy1.symm)]
    refine (hbase.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp
    ring

lemma bernoulliRelativeEntropy_mono_snd
    {p x y : ℝ} (hpx : p ≤ x) (hx0 : 0 < x)
    (hxy : x ≤ y) (hy1 : y < 1) :
    bernoulliRelativeEntropy p x ≤ bernoulliRelativeEntropy p y := by
  have hcont : ContinuousOn (fun q ↦ bernoulliRelativeEntropy p q) (Icc x y) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      have : 0 < z := lt_of_lt_of_le hx0 hz.1
      exact ne_of_gt this
    have hz1 : z ≠ 1 := by
      have : z < 1 := lt_of_le_of_lt hz.2 hy1
      exact ne_of_lt this
    exact (hasDerivAt_bernoulliRelativeEntropy_snd hz0 hz1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ
      (fun q ↦ bernoulliRelativeEntropy p q) (interior (Icc x y)) := by
    intro z hz
    have hz' : z ∈ Ioo x y := by simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    exact (hasDerivAt_bernoulliRelativeEntropy_snd
      (by linarith) (by linarith)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ interior (Icc x y),
      0 ≤ deriv (fun q ↦ bernoulliRelativeEntropy p q) z := by
    intro z hz
    have hz' : z ∈ Ioo x y := by simpa [interior_Icc, hxy] using hz
    rcases hz' with ⟨hzx, hzy⟩
    rw [(hasDerivAt_bernoulliRelativeEntropy_snd
      (by linarith) (by linarith)).deriv]
    exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  exact (monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont hdiff hderiv)
    (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

lemma bernoulliRelativeEntropy_self_index
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    bernoulliRelativeEntropy p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [bernoulliRelativeEntropy]
  simp [bernoulliRelativeEntropy, div_self hp0,
    div_self (sub_ne_zero.mpr hp1.symm)]

lemma klucb_threshold_feasible_of_le_sSup
    {p β q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hβ : 0 ≤ β) (hq : q ∈ Ioo (0 : ℝ) 1) (hpq : p ≤ q)
    (hindex : q ≤ sSup {x ∈ Icc (0 : ℝ) 1 |
      bernoulliRelativeEntropy p x ≤ β ∧
        (x = 0 → p = 0) ∧ (x = 1 → p = 1)}) :
    bernoulliRelativeEntropy p q ≤ β := by
  let F : Set ℝ := {x ∈ Icc (0 : ℝ) 1 |
    bernoulliRelativeEntropy p x ≤ β ∧
      (x = 0 → p = 0) ∧ (x = 1 → p = 1)}
  have hpF : p ∈ F := by
    refine ⟨hp, ?_, ?_, ?_⟩
    · rw [bernoulliRelativeEntropy_self_index hp]
      exact hβ
    · exact fun h ↦ h
    · exact fun h ↦ h
  have hFne : F.Nonempty := ⟨p, hpF⟩
  by_contra hnot
  have hbad : β < bernoulliRelativeEntropy p q := lt_of_not_ge hnot
  by_cases hpqeq : p = q
  · subst q
    rw [bernoulliRelativeEntropy_self_index hp] at hbad
    linarith
  have hpqlt : p < q := lt_of_le_of_ne hpq hpqeq
  have hcont :
      ContinuousAt (fun x ↦ bernoulliRelativeEntropy p x) q :=
    (hasDerivAt_bernoulliRelativeEntropy_snd
      (ne_of_gt hq.1) (ne_of_lt hq.2)).continuousAt
  have hev : {x : ℝ | β < bernoulliRelativeEntropy p x} ∈ 𝓝 q :=
    hcont (isOpen_Ioi.mem_nhds hbad)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  let η := min δ (q - p)
  let r := q - η / 2
  have hηpos : 0 < η := lt_min hδ (sub_pos.mpr hpqlt)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηgap : η ≤ q - p := min_le_right _ _
  have hrq : r < q := by dsimp [r]; linarith
  have hpr : p < r := by dsimp [r]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt hp.1 hpr
  have hrbad : β < bernoulliRelativeEntropy p r := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [r]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hupper : ∀ x ∈ F, x ≤ r := by
    intro x hxF
    by_contra hxr
    have hrx : r < x := lt_of_not_ge hxr
    have hx1 : x < 1 := by
      have hxle := hxF.1.2
      exact lt_of_le_of_ne hxle (fun hxone ↦ by
        have hpone := hxF.2.2.2 hxone
        linarith [hpqlt, hq.2])
    have hmono :
        bernoulliRelativeEntropy p r ≤
          bernoulliRelativeEntropy p x :=
      bernoulliRelativeEntropy_mono_snd hpr.le hr0 hrx.le hx1
    linarith [hxF.2.1]
  have hsup : sSup F ≤ r := csSup_le hFne hupper
  have hseteq : F = {x ∈ Icc (0 : ℝ) 1 |
      bernoulliRelativeEntropy p x ≤ β ∧
        (x = 0 → p = 0) ∧ (x = 1 → p = 1)} := by
    rfl
  have hqle : q ≤ sSup F := by
    rw [hseteq]
    exact hindex
  linarith

lemma le_klucb_sSup_of_threshold_feasible
    {p β q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hfeas : bernoulliRelativeEntropy p q ≤ β) :
    q ≤ sSup {x ∈ Icc (0 : ℝ) 1 |
      bernoulliRelativeEntropy p x ≤ β ∧
        (x = 0 → p = 0) ∧ (x = 1 → p = 1)} := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro x hx
    exact hx.1.2
  · exact ⟨⟨hq.1.le, hq.2.le⟩, hfeas,
      (fun h ↦ (hq.1.ne' h).elim),
      (fun h ↦ (hq.2.ne h).elim)⟩

end BanditAlgorithm

theorem solution
    {k n : ℕ} (i : Fin k) (h : BanditAlgorithm.BanditHistory k n)
    (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : BanditAlgorithm.armEmpiricalMean i h ∈ Set.Icc (0 : ℝ) 1) :
    q ≤ BanditAlgorithm.klucbIndex i h ↔
      BanditAlgorithm.klucbTruncatedRelativeEntropy
          (BanditAlgorithm.armEmpiricalMean i h) q ≤
        Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
          BanditAlgorithm.armPullCount i h := by
  let p := BanditAlgorithm.armEmpiricalMean i h
  let β := Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
    BanditAlgorithm.armPullCount i h
  have hf : 1 ≤ BanditAlgorithm.klucbExploration (n + 1) := by
    rw [BanditAlgorithm.klucbExploration]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hβ : 0 ≤ β :=
    div_nonneg (Real.log_nonneg hf) (Nat.cast_nonneg _)
  constructor
  · intro hindex
    by_cases hpq : p ≤ q
    · rw [BanditAlgorithm.klucbTruncatedRelativeEntropy, if_pos hpq]
      apply BanditAlgorithm.klucb_threshold_feasible_of_le_sSup
        hp hβ hq hpq
      simpa [BanditAlgorithm.klucbIndex, p, β] using hindex
    · rw [BanditAlgorithm.klucbTruncatedRelativeEntropy, if_neg hpq]
      exact hβ
  · intro hfeas
    by_cases hpq : p ≤ q
    · rw [BanditAlgorithm.klucbTruncatedRelativeEntropy, if_pos hpq] at hfeas
      have hle := BanditAlgorithm.le_klucb_sSup_of_threshold_feasible hq hfeas
      simpa [BanditAlgorithm.klucbIndex, p, β] using hle
    · have hqp : q ≤ p := le_of_not_ge hpq
      apply hqp.trans
      rw [BanditAlgorithm.klucbIndex]
      apply le_csSup
      · refine ⟨1, ?_⟩
        intro x hx
        exact hx.1.2
      · refine ⟨hp, ?_, ?_, ?_⟩
        · rw [BanditAlgorithm.bernoulliRelativeEntropy_self_index hp]
          exact hβ
        · exact fun h0 ↦ h0
        · exact fun h1 ↦ h1
