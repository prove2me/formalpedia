-- Prove2me | solution 1 for ChitourPrescribedTime.Linear.timeChange_properties
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:46:06.827205+00:00
-- url     : https://prove2.me/submissions/ba81f24e-74eb-445e-bf9c-ede1e77be128

import Definitions.Def_ChitourPrescribedTime_Linear_timeChange
import Definitions.Def_ChitourPrescribedTime_Linear_chain
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
open ChitourPrescribedTime.Linear
open MeasureTheory Filter Matrix
open scoped Topology BigOperators

private theorem tail_deriv (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u => ∫ v in u..T, a v) (-a t) (Set.Icc 0 T) t := by
  haveI : Fact (t ∈ Set.Icc 0 T) := ⟨ht⟩
  apply intervalIntegral.integral_hasDerivWithinAt_left
  · exact (ha.continuousOn.mono (Set.Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc ht.2
  · exact ha.continuousOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  · exact ha.continuousOn t ht

private theorem lam_deriv (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
    HasDerivWithinAt (lam T a) (a t * lam T a t ^ 2) (Set.Ico 0 T) t := by
  have hd := (tail_deriv T a ha t ⟨ht.1,ht.2.le⟩).inv (ne_of_gt (ha.tail_pos t ht))
  unfold lam
  simp only [one_div]
  convert! hd.mono Set.Ico_subset_Icc_self using 1 <;> simp [div_eq_mul_inv] <;> ring


private theorem lam_pos (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) : 0 < lam T a t := one_div_pos.mpr (ha.tail_pos t ht)

private theorem lam_cont (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    ContinuousOn (lam T a) (Set.Ico 0 T) := fun t ht => (lam_deriv T a ha t ht).continuousWithinAt

private theorem s_deriv (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
    HasDerivWithinAt (sTime T a) (lam T a t) (Set.Ico 0 T) t := by
  let b := (t+T)/2
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hc : ContinuousOn (lam T a) (Set.Icc 0 b) :=
    (lam_cont T a ha).mono (by intro z hz; exact ⟨hz.1,lt_of_le_of_lt hz.2 hbT⟩)
  haveI : Fact (t ∈ Set.Icc 0 b) := ⟨ht.1,htb.le⟩
  have hd : HasDerivWithinAt (sTime T a) (lam T a t) (Set.Icc 0 b) t := by
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · exact (hc.mono (Set.Icc_subset_Icc le_rfl htb.le)).intervalIntegrable_of_Icc ht.1
    · exact hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    · exact hc t ⟨ht.1,htb.le⟩
  apply hd.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_lt_nhds htb)] with z hz hzb
  exact ⟨hz.1,hzb.le⟩

private theorem s_cont (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    ContinuousOn (sTime T a) (Set.Ico 0 T) := fun t ht => (s_deriv T a ha t ht).continuousWithinAt

private theorem s_strict (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    StrictMonoOn (sTime T a) (Set.Ico 0 T) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 T) (s_cont T a ha)
  intro t ht
  have ht' : t ∈ Set.Ioo 0 T := by simpa using ht
  rw [((s_deriv T a ha t ⟨ht'.1.le,ht'.2⟩).hasDerivAt (Ico_mem_nhds ht'.1 ht'.2)).deriv]
  exact lam_pos T a ha t ⟨ht'.1.le,ht'.2⟩

private theorem lam_mono (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    MonotoneOn (lam T a) (Set.Ico 0 T) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico 0 T) (lam_cont T a ha)
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 T := by simpa using ht
    exact ((lam_deriv T a ha t ⟨ht'.1.le,ht'.2⟩).hasDerivAt (Ico_mem_nhds ht'.1 ht'.2)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 T := by simpa using ht
    rw [((lam_deriv T a ha t ⟨ht'.1.le,ht'.2⟩).hasDerivAt (Ico_mem_nhds ht'.1 ht'.2)).deriv]
    exact mul_nonneg (ha.nonneg t ⟨ht'.1.le,ht'.2.le⟩) (sq_nonneg _)

private theorem tail_limit (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    Tendsto (fun t => ∫ v in t..T, a v) (𝓝[<] T) (𝓝[>] 0) := by
  have hc := (tail_deriv T a ha T ⟨ha.T_pos.le,le_rfl⟩).continuousWithinAt
  have hfilter : (𝓝[<] T) ≤ 𝓝[Set.Icc 0 T] T := by
    apply le_inf nhdsWithin_le_nhds
    exact Filter.le_principal_iff.mpr (Filter.mem_of_superset (Ico_mem_nhdsLT ha.T_pos) (by intro z hz; exact ⟨hz.1,hz.2.le⟩))
  have ht : Tendsto (fun t => ∫ v in t..T, a v) (𝓝[<] T) (𝓝 0) := by
    simpa using hc.mono_left hfilter
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨ht,?_⟩
  filter_upwards [Ico_mem_nhdsLT ha.T_pos] with t ht
  exact ha.tail_pos t ht

private theorem lam_limit (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    Tendsto (lam T a) (𝓝[<] T) atTop := by
  unfold lam
  simp only [one_div]
  convert! (tail_limit T a ha).inv_tendsto_nhdsGT_zero using 1

private theorem s_smooth (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    ContDiffOn ℝ 1 (sTime T a) (Set.Ico 0 T) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ico 0 T)]
  refine ⟨fun t ht => (s_deriv T a ha t ht).differentiableWithinAt,?_⟩
  apply (lam_cont T a ha).congr
  intro t ht
  exact (s_deriv T a ha t ht).derivWithin (uniqueDiffOn_Ico 0 T t ht)

private theorem s_limit (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    Tendsto (sTime T a) (𝓝[<] T) atTop := by
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image ha.continuousOn
  let M := |B|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMa (t : ℝ) (ht : t ∈ Set.Icc 0 T) : a t ≤ M := by
    have h := hB (Set.mem_image_of_mem a ht)
    have := le_abs_self B
    dsimp [M]
    linarith
  let A : ℝ → ℝ := fun t => ∫ v in t..T, a v
  let q : ℝ → ℝ := fun t => M*sTime T a t + Real.log (A t)
  have hqd (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
      HasDerivWithinAt q ((M-a t)/A t) (Set.Ico 0 T) t := by
    have hd := ((s_deriv T a ha t ht).const_mul M).add
      (((tail_deriv T a ha t ⟨ht.1,ht.2.le⟩).mono Set.Ico_subset_Icc_self).log (ne_of_gt (ha.tail_pos t ht)))
    convert! hd using 1 <;> dsimp [q,A,lam] <;> ring
  have hqm : MonotoneOn q (Set.Ico 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 T) (fun t ht => (hqd t ht).continuousWithinAt)
    · intro t ht
      have ht' : t ∈ Set.Ioo 0 T := by simpa using ht
      exact ((hqd t ⟨ht'.1.le,ht'.2⟩).hasDerivAt (Ico_mem_nhds ht'.1 ht'.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo 0 T := by simpa using ht
      rw [((hqd t ⟨ht'.1.le,ht'.2⟩).hasDerivAt (Ico_mem_nhds ht'.1 ht'.2)).deriv]
      exact div_nonneg (sub_nonneg.mpr (hMa t ⟨ht'.1.le,ht'.2.le⟩)) (ha.tail_pos t ⟨ht'.1.le,ht'.2⟩).le
  have hbound (t : ℝ) (ht : t ∈ Set.Ico 0 T) : (Real.log (A 0)-Real.log (A t))/M ≤ sTime T a t := by
    have hh := hqm (show 0∈Set.Ico 0 T from ⟨le_rfl,ha.T_pos⟩) ht ht.1
    simp only [q,sTime,intervalIntegral.integral_same,mul_zero,zero_add] at hh
    apply (div_le_iff₀ hM).mpr
    dsimp [sTime]
    linarith
  have hlog : Tendsto (fun t => Real.log (A t)) (𝓝[<] T) atBot := Real.tendsto_log_nhdsGT_zero.comp (tail_limit T a ha)
  apply tendsto_atTop.2
  intro R
  filter_upwards [hlog.eventually_le_atBot (Real.log (A 0)-M*R),Ico_mem_nhdsLT ha.T_pos] with t ht hct
  have hR : R ≤ (Real.log (A 0)-Real.log (A t))/M := by
    apply (le_div_iff₀ hM).mpr
    nlinarith
  exact hR.trans (hbound t hct)

private theorem s_image (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    sTime T a '' Set.Ico 0 T = Set.Ici 0 := by
  have h0 : sTime T a 0=0 := by simp [sTime]
  have hz : 0 ∈ Set.Ico 0 T := ⟨le_rfl,ha.T_pos⟩
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    have hh := (s_strict T a ha).monotoneOn hz ht ht.1
    simpa only [h0,Set.mem_Ici] using hh
  · intro y hy
    have he := (s_limit T a ha).eventually_ge_atTop y
    obtain ⟨t,ht,hyt⟩ := (he.and (Ico_mem_nhdsLT ha.T_pos)).exists
    exact (s_cont T a ha).surjOn_Icc hz hyt ⟨by simpa only [h0,Set.mem_Ici] using hy,ht⟩

theorem solution (T : ℝ) (a : ℝ → ℝ) (ha : AdmissibleWeight T a) :
    (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (lam T a) (a t * lam T a t ^ 2) (Set.Ico 0 T) t) ∧
    (∀ t ∈ Set.Ico 0 T, 0 < lam T a t) ∧
    MonotoneOn (lam T a) (Set.Ico 0 T) ∧
    Filter.Tendsto (lam T a) (nhdsWithin T (Set.Iio T)) Filter.atTop ∧
    (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (sTime T a) (lam T a t) (Set.Ico 0 T) t) ∧
    ContDiffOn ℝ 1 (sTime T a) (Set.Ico 0 T) ∧
    StrictMonoOn (sTime T a) (Set.Ico 0 T) ∧
    sTime T a '' Set.Ico 0 T = Set.Ici 0 := by
  exact ⟨lam_deriv T a ha,lam_pos T a ha,lam_mono T a ha,lam_limit T a ha,
    s_deriv T a ha,s_smooth T a ha,s_strict T a ha,s_image T a ha⟩
