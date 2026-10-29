-- Prove2me | solution 1 for BalkemaDeHaan.LimitTypes.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T01:46:41.212841+00:00
-- url     : https://prove2.me/submissions/7fb889ae-742e-4953-9c66-aa164f5d2780

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open BalkemaDeHaan.LimitTypes

namespace BdHLib

/-- Continuity points of a monotone function meet every open interval. -/
lemma exists_continuousAt_Ioo {G : ℝ → ℝ} (hG : Monotone G) {u v : ℝ} (h : u < v) :
    ∃ x ∈ Ioo u v, ContinuousAt G x := by
  by_contra hcon
  push Not at hcon
  have hsub : Ioo u v ⊆ {x | ¬ ContinuousAt G x} := fun x hx => hcon x hx
  have hc : (Ioo u v).Countable := hG.countable_not_continuousAt.mono hsub
  have h0 := hc.measure_zero volume
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- Level comparison: monotone families with limits `c < d` at `u i`, `v i` give `u i < v i`. -/
lemma eventually_lt_of_tendsto_mono {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ}
    (hF : ∀ i, Monotone (F i)) {u v : ι → ℝ} {c d : ℝ}
    (hu : Tendsto (fun i => F i (u i)) l (𝓝 c)) (hv : Tendsto (fun i => F i (v i)) l (𝓝 d))
    (hcd : c < d) : ∀ᶠ i in l, u i < v i := by
  filter_upwards [hu.eventually_lt hv hcd] with i hi
  exact (hF i).reflect_lt hi

/-- For a monotone right-continuous `G` crossing level `θ`, the crossing point `sInf {θ ≤ G}`. -/
lemma level_inf {G : ℝ → ℝ} (hG : Monotone G) (hrc : ∀ x, ContinuousWithinAt G (Ici x) x)
    {θ x0 x1 : ℝ} (h0 : G x0 < θ) (h1 : θ ≤ G x1) :
    θ ≤ G (sInf {x | θ ≤ G x}) ∧ ∀ x < sInf {x | θ ≤ G x}, G x < θ := by
  set S := {x | θ ≤ G x} with hS
  have hne : S.Nonempty := ⟨x1, h1⟩
  have hbdd : BddBelow S := by
    refine ⟨x0, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hG hlt.le
    simp only [hS, mem_ofPred_eq] at hx
    linarith
  refine ⟨?_, fun x hx => ?_⟩
  · have hev : ∀ᶠ x in 𝓝[>] (sInf S), θ ≤ G x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
      exact le_trans hs (hG hsx.le)
    have ht : Tendsto G (𝓝[>] (sInf S)) (𝓝 (G (sInf S))) :=
      ((hrc (sInf S)).mono Ioi_subset_Ici_self).tendsto
    exact ge_of_tendsto ht hev
  · by_contra hge
    push Not at hge
    have := csInf_le hbdd (show x ∈ S from hge)
    linarith

/-- A non-Dirac probability law has a point where its cdf lies strictly between `0` and `1`. -/
lemma exists_mid (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c) :
    ∃ x, 0 < cdf ν x ∧ cdf ν x < 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x1, hx1⟩ :=
    ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1))).exists
  obtain ⟨x0, hx0⟩ :=
    ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))).exists
  have h1 : 1 ≤ cdf ν x1 := hcon x1 (by linarith)
  obtain ⟨hc1, hlt⟩ := level_inf (monotone_cdf ν) (cdf ν).right_continuous'
    (show cdf ν x0 < 1 by linarith) h1
  apply hν (sInf {x | 1 ≤ cdf ν x})
  apply MeasureTheory.Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real (Measure.dirac _) x]
  by_cases hx : sInf {x | 1 ≤ cdf ν x} ≤ x
  · have : (Measure.dirac (sInf {x | 1 ≤ cdf ν x})).real (Iic x) = 1 := by
      simp [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, hx]
    rw [this]
    exact le_antisymm (cdf_le_one _ _) (hc1.trans (monotone_cdf ν hx))
  · push Not at hx
    have : (Measure.dirac (sInf {x | 1 ≤ cdf ν x})).real (Iic x) = 0 := by
      simp [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, not_le.mpr hx]
    rw [this]
    have h := hlt x hx
    rcases (cdf_nonneg ν x).lt_or_eq with h' | h'
    · exact absurd (hcon x h') (not_le.mpr h)
    · exact h'.symm

section residual

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma tail_pos (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (t : ℝ) : 0 < tail μ t :=
  ENNReal.toReal_pos (hF t).ne' (measure_ne_top _ _)

lemma tail_anti : Antitone (tail μ) := fun _ _ hxy =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioi_subset_Ioi hxy))

lemma residualCDF_of_nonpos (t : ℝ) {x : ℝ} (hx : x ≤ 0) : residualCDF μ t x = 0 := by
  unfold residualCDF
  rw [Set.Ioc_eq_empty (not_lt.mpr (by linarith))]
  simp

lemma residualCDF_eq (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    residualCDF μ t x = 1 - tail μ (t + x) / tail μ t := by
  have hsub : Ioi (t + x) ⊆ Ioi t := Ioi_subset_Ioi (by linarith)
  have h1 : Ioc t (t + x) = Ioi t \ Ioi (t + x) := by
    ext z; simp only [mem_Ioc, Set.mem_sdiff, mem_Ioi, not_lt]
  have h2 : (μ (Ioc t (t + x))).toReal = tail μ t - tail μ (t + x) := by
    rw [h1, measure_sdiff hsub measurableSet_Ioi.nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]
    rfl
  have hp := tail_pos hF t
  unfold residualCDF
  rw [h2]
  change (tail μ t - tail μ (t + x)) / tail μ t = _
  field_simp

lemma residualCDF_mono (t : ℝ) : Monotone (residualCDF μ t) := by
  intro x y hxy
  unfold residualCDF
  apply div_le_div_of_nonneg_right _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Ioc_subset_Ioc le_rfl (by linarith)))

/-- Along a continuity point `x` with `0 < G x`, the normed point is eventually to the right of `t`
and the tail ratio converges to `1 - G x`. -/
lemma ratio_tendsto (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x)) {a b G : ℝ → ℝ}
    (hconv : WeakConv (fun t x => residualCDF μ t (b t + x * a t)) G) {x : ℝ}
    (hx : ContinuousAt G x) (hpos : 0 < G x) :
    (∀ᶠ s in atTop, 0 < b s + x * a s) ∧
    Tendsto (fun s => tail μ (s + (b s + x * a s)) / tail μ s) atTop (𝓝 (1 - G x)) := by
  have h := hconv x hx
  have hev : ∀ᶠ s in atTop, 0 < b s + x * a s := by
    filter_upwards [h.eventually (lt_mem_nhds hpos)] with s hs
    by_contra hneg
    push Not at hneg
    rw [residualCDF_of_nonpos s hneg] at hs
    exact lt_irrefl _ hs
  refine ⟨hev, ?_⟩
  have h2 : Tendsto (fun s => 1 - residualCDF μ s (b s + x * a s)) atTop (𝓝 (1 - G x)) :=
    tendsto_const_nhds.sub h
  refine h2.congr' ?_
  filter_upwards [hev] with s hs
  rw [residualCDF_eq hF s hs.le]
  ring

end residual

/-- S2 (child C1): under `F(x) < 1` for all `x`, a nondegenerate residual-life limit law has no
finite right endpoint. -/
theorem endpoint (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (hconv : WeakConv (fun t x => residualCDF μ t (b t + x * a t)) (cdf ν)) :
    ∀ x, cdf ν x < 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr⟩ := hcon
  have hmono : Monotone (cdf ν) := monotone_cdf ν
  obtain ⟨x0, hx0p, hx0l⟩ := exists_mid ν hν
  obtain ⟨hr0, hlt⟩ := level_inf hmono (cdf ν).right_continuous' hx0l hr
  generalize sInf {x | 1 ≤ cdf ν x} = r0 at hr0 hlt
  have hx0r0 : x0 < r0 := by
    by_contra h
    push Not at h
    have := hmono h
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (r0 - x0) / 3 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨q, hq, hqc⟩ := exists_continuousAt_Ioo hmono (show x0 < x0 + δ by linarith)
  obtain ⟨q', hq', hq'c⟩ := exists_continuousAt_Ioo hmono (show r0 - δ < r0 by linarith)
  obtain ⟨y, hy, hyc⟩ := exists_continuousAt_Ioo hmono (show r0 - δ / 2 < r0 by linarith)
  obtain ⟨r', hr', hr'c⟩ := exists_continuousAt_Ioo hmono (show r0 < r0 + δ / 2 by linarith)
  have Gq : 0 < cdf ν q := lt_of_lt_of_le hx0p (hmono hq.1.le)
  have Gq' : 0 < cdf ν q' := lt_of_lt_of_le hx0p (hmono (by linarith [hq'.1]))
  have Gy : 0 < cdf ν y := lt_of_lt_of_le hx0p (hmono (by linarith [hy.1]))
  have Gq'l : cdf ν q' < 1 := hlt q' hq'.2
  have Gyl : cdf ν y < 1 := hlt y hy.2
  have Gr' : cdf ν r' = 1 := le_antisymm (cdf_le_one _ _) (hr0.trans (hmono hr'.1.le))
  have Gr'p : 0 < cdf ν r' := by rw [Gr']; norm_num
  obtain ⟨evq, -⟩ := ratio_tendsto hF hconv hqc Gq
  obtain ⟨-, tq'⟩ := ratio_tendsto hF hconv hq'c Gq'
  obtain ⟨evy, ty⟩ := ratio_tendsto hF hconv hyc Gy
  obtain ⟨-, tr'⟩ := ratio_tendsto hF hconv hr'c Gr'p
  rw [Gr', sub_self] at tr'
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 - cdf ν y := ⟨_, rfl⟩
  obtain ⟨p', hp'⟩ : ∃ p' : ℝ, p' = 1 - cdf ν q' := ⟨_, rfl⟩
  rw [← hp] at ty
  rw [← hp'] at tq'
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p < 1 := by rw [hp]; linarith
  have hp'0 : 0 < p' := by rw [hp']; linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (p / 2) * min (p / 2) (p' / 2) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hmin1 : η ≤ p / 2 * (p / 2) := by
    rw [hη]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  have hmin2 : η ≤ p / 2 * (p' / 2) := by
    rw [hη]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  have e1 := ty.eventually (gt_mem_nhds (show p < (1 + p) / 2 by linarith))
  have e2 := ty.eventually (lt_mem_nhds (show p / 2 < p by linarith))
  have e3 := tq'.eventually (lt_mem_nhds (show p' / 2 < p' by linarith))
  have e4 := tr'.eventually (gt_mem_nhds hη0)
  obtain ⟨T, hT⟩ := eventually_atTop.1 (evq.and (evy.and (e1.and (e2.and (e3.and e4)))))
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ → ℝ, ∀ s, τ s = s + (b s + y * a s) := ⟨_, fun _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = r' - y := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; linarith [hy.2, hr'.1]
  have hqq : δ < q' - q := by linarith [hq.2, hq'.1]
  have hκδ : κ < δ := by rw [hκ]; linarith [hy.1, hr'.2]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = κ / (q' - q) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; apply div_pos hκ0; linarith
  have hc1 : c < 1 := by rw [hc, div_lt_one (by linarith)]; linarith
  have tpos := tail_pos hF (μ := μ)
  have step : ∀ s, T ≤ s → s < τ s ∧ tail μ (τ s) ≤ (1 + p) / 2 * tail μ s ∧
      a (τ s) ≤ c * a s ∧ τ (τ s) - τ s ≤ κ * a s := by
    intro s hs
    obtain ⟨-, hys, h1, h2, -, h4⟩ := hT s hs
    rw [← hτ s] at h1 h2
    have hτs : s < τ s := by rw [hτ s]; linarith
    obtain ⟨hqs', -, -, h2', h3', -⟩ := hT (τ s) (le_trans hs hτs.le)
    rw [← hτ (τ s)] at h2'
    have tps := tpos s
    have tpτ := tpos (τ s)
    have h1' : tail μ (τ s) < (1 + p) / 2 * tail μ s := by
      rw [div_lt_iff₀ tps] at h1; exact h1
    have h2'' : p / 2 * tail μ s < tail μ (τ s) := by
      rw [lt_div_iff₀ tps] at h2; exact h2
    have h4' : tail μ (s + (b s + r' * a s)) < η * tail μ s := by
      rw [div_lt_iff₀ tps] at h4; exact h4
    have h3'' : p' / 2 * tail μ (τ s) < tail μ (τ s + (b (τ s) + q' * a (τ s))) := by
      rw [lt_div_iff₀ tpτ] at h3'; exact h3'
    have h2''' : p / 2 * tail μ (τ s) < tail μ (τ (τ s)) := by
      rw [lt_div_iff₀ tpτ] at h2'; exact h2'
    have hZ : τ s + (b (τ s) + q' * a (τ s)) < s + (b s + r' * a s) := by
      by_contra hge
      push Not at hge
      have hanti := tail_anti (μ := μ) hge
      have e5 : p' / 2 * (p / 2 * tail μ s) < p' / 2 * tail μ (τ s) :=
        mul_lt_mul_of_pos_left h2'' (by positivity)
      have e6 : η * tail μ s ≤ p / 2 * (p' / 2) * tail μ s := mul_le_mul_of_nonneg_right hmin2 tps.le
      have e7 : p' / 2 * (p / 2 * tail μ s) = p / 2 * (p' / 2) * tail μ s := by ring
      linarith
    have hYY : τ (τ s) < s + (b s + r' * a s) := by
      by_contra hge
      push Not at hge
      have hanti := tail_anti (μ := μ) hge
      have e5 : p / 2 * (p / 2 * tail μ s) < p / 2 * tail μ (τ s) :=
        mul_lt_mul_of_pos_left h2'' (by positivity)
      have e6 : η * tail μ s ≤ p / 2 * (p / 2) * tail μ s := mul_le_mul_of_nonneg_right hmin1 tps.le
      have e7 : p / 2 * (p / 2 * tail μ s) = p / 2 * (p / 2) * tail μ s := by ring
      linarith
    have hτs' := hτ s
    refine ⟨hτs, h1'.le, ?_, ?_⟩
    · have hτa : (q' - q) * a (τ s) < κ * a s := by
        rw [hκ]; linarith
      rw [hc, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith
    · rw [hκ]; linarith
  -- iterate
  obtain ⟨t, ht0, tsucc⟩ : ∃ t : ℕ → ℝ, t 0 = T ∧ ∀ n, t (n + 1) = τ (t n) :=
    ⟨fun n => τ^[n] T, rfl, fun n => Function.iterate_succ_apply' τ n T⟩
  have tge : ∀ n, T ≤ t n := by
    intro n
    induction n with
    | zero => rw [ht0]
    | succ n ih => rw [tsucc]; exact le_trans ih (step _ ih).1.le
  have abound : ∀ n, a (t n) ≤ c ^ n * a T := by
    intro n
    induction n with
    | zero => rw [ht0]; simp
    | succ n ih =>
      rw [tsucc, pow_succ]
      have h1 := (step _ (tge n)).2.2.1
      have h2 := mul_le_mul_of_nonneg_left ih hc0.le
      linarith
  have tailb : ∀ n, tail μ (t n) ≤ ((1 + p) / 2) ^ n * tail μ T := by
    intro n
    induction n with
    | zero => rw [ht0]; simp
    | succ n ih =>
      rw [tsucc, pow_succ]
      have h1 := (step _ (tge n)).2.1
      have h2 := mul_le_mul_of_nonneg_left ih (show 0 ≤ (1 + p) / 2 by linarith)
      linarith
  have tup : ∀ n, t (n + 1) ≤ t 1 + κ * a T * ((1 - c ^ n) / (1 - c)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := (step _ (tge n)).2.2.2
      rw [← tsucc, ← tsucc] at h
      have hab := mul_le_mul_of_nonneg_left (abound n) hκ0.le
      have hdiff : (1 - c ^ (n + 1)) / (1 - c) = (1 - c ^ n) / (1 - c) + c ^ n := by
        field_simp [show (1 - c) ≠ 0 by linarith]
        ring
      rw [hdiff]
      linarith
  have tU : ∀ n, t (n + 1) ≤ t 1 + κ * a T / (1 - c) := by
    intro n
    have hcn : 0 ≤ c ^ n := by positivity
    have h3 : (1 - c ^ n) / (1 - c) ≤ 1 / (1 - c) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_pos hκ0 (ha T)).le
    rw [mul_one_div] at h4
    linarith [tup n]
  have hlim : Tendsto (fun n : ℕ => ((1 + p) / 2) ^ n * tail μ T) atTop (𝓝 (0 * tail μ T)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).mul_const _
  rw [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (tpos (t 1 + κ * a T / (1 - c))))).exists
  have h1 := tailb (n + 1)
  have h2 := tail_anti (μ := μ) (tU n)
  have hpow : ((1 + p) / 2) ^ (n + 1) * tail μ T ≤ ((1 + p) / 2) ^ n * tail μ T :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) (by omega))
      (tpos T).le
  linarith

/-- `c ≤ f z` from `c ≤ f w` at the continuity points `w > z` (monotone, right-continuous `f`). -/
lemma le_of_forall_cont_gt {f : ℝ → ℝ} (hf : Monotone f)
    (hrc : ∀ x, ContinuousWithinAt f (Ici x) x) {c z : ℝ}
    (h : ∀ w, z < w → ContinuousAt f w → c ≤ f w) : c ≤ f z := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ w in 𝓝[≥] z, f w < c := (hrc z).eventually (gt_mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨w, hw, hwc⟩ := exists_continuousAt_Ioo hf (show z < z + δ / 2 by linarith)
  have hmem : w ∈ Metric.ball z δ ∩ Ici z := by
    refine ⟨?_, le_of_lt hw.1⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]
  have := hball hmem
  have := h w hw.1 hwc
  simp only [mem_setOf_eq] at *
  linarith

/-- Interior frame bound: if `F i (a1 i x + b1 i) → G1 x ∈ (0,1)`, the point `x` read in the second
frame stays bounded. -/
lemma frame_bound {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} (hF : ∀ i, Monotone (F i))
    {a1 b1 a2 b2 : ι → ℝ} (ha2 : ∀ i, 0 < a2 i) {G1 G2 : ℝ → ℝ} (hG2 : Monotone G2)
    (hG2bot : Tendsto G2 atBot (𝓝 0)) (hG2top : Tendsto G2 atTop (𝓝 1))
    (h2 : ∀ z, ContinuousAt G2 z → Tendsto (fun i => F i (a2 i * z + b2 i)) l (𝓝 (G2 z)))
    {x : ℝ} (hx : Tendsto (fun i => F i (a1 i * x + b1 i)) l (𝓝 (G1 x)))
    (h0 : 0 < G1 x) (h1 : G1 x < 1) :
    ∃ lo hi : ℝ, ∀ᶠ i in l, lo < (a1 i * x + b1 i - b2 i) / a2 i ∧
      (a1 i * x + b1 i - b2 i) / a2 i < hi := by
  obtain ⟨z0, hz0⟩ := eventually_atBot.1 (hG2bot.eventually (gt_mem_nhds h0))
  obtain ⟨z1, hz1⟩ := eventually_atTop.1 (hG2top.eventually (lt_mem_nhds h1))
  obtain ⟨zl, hzl, hzlc⟩ := exists_continuousAt_Ioo hG2 (show z0 - 1 < z0 by linarith)
  obtain ⟨zh, hzh, hzhc⟩ := exists_continuousAt_Ioo hG2 (show z1 < z1 + 1 by linarith)
  refine ⟨zl, zh, ?_⟩
  have el := eventually_lt_of_tendsto_mono hF (h2 zl hzlc) hx (hz0 zl hzl.2.le)
  have eh := eventually_lt_of_tendsto_mono hF hx (h2 zh hzhc) (hz1 zh hzh.1.le)
  filter_upwards [el, eh] with i hl hh
  constructor
  · rw [lt_div_iff₀ (ha2 i)]; linarith
  · rw [div_lt_iff₀ (ha2 i)]; linarith

/-- Two interior continuity points of a monotone right-continuous `G` with a mid value. -/
lemma two_mid_points {G : ℝ → ℝ} (hG : Monotone G) (hrc : ∀ x, ContinuousWithinAt G (Ici x) x)
    {x0 : ℝ} (h0 : 0 < G x0) (h1 : G x0 < 1) :
    ∃ x1 x2, x1 < x2 ∧ ContinuousAt G x1 ∧ ContinuousAt G x2 ∧ 0 < G x1 ∧ G x1 < 1 ∧
      0 < G x2 ∧ G x2 < 1 := by
  have hev : ∀ᶠ w in 𝓝[≥] x0, G w < 1 := (hrc x0).eventually (gt_mem_nhds h1)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨x1, hx1, hx1c⟩ := exists_continuousAt_Ioo hG (show x0 < x0 + δ / 2 by linarith)
  obtain ⟨x2, hx2, hx2c⟩ := exists_continuousAt_Ioo hG (show x0 + δ / 2 < x0 + δ by linarith)
  have hlt : ∀ w, x0 ≤ w → w < x0 + δ → G w < 1 := by
    intro w hw1 hw2
    have hmem : w ∈ Metric.ball x0 δ ∩ Ici x0 := by
      refine ⟨?_, hw1⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hball hmem
  refine ⟨x1, x2, by linarith [hx1.2, hx2.1], hx1c, hx2c, ?_, hlt x1 hx1.1.le (by linarith [hx1.2]),
    ?_, hlt x2 (by linarith [hx2.1]) hx2.2⟩
  · exact lt_of_lt_of_le h0 (hG hx1.1.le)
  · exact lt_of_lt_of_le h0 (hG (by linarith [hx2.1]))

/-- Convergence of types (cluster-point form): two affine normalizations of one monotone family
with nondegenerate limits give limits of the same type. -/
theorem type_ident {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℝ → ℝ}
    (hF : ∀ i, Monotone (F i))
    {a1 b1 a2 b2 : ι → ℝ} (ha1 : ∀ i, 0 < a1 i) (ha2 : ∀ i, 0 < a2 i)
    {G1 G2 : ℝ → ℝ} (hG1 : Monotone G1) (hG2 : Monotone G2)
    (hrc1 : ∀ x, ContinuousWithinAt G1 (Ici x) x) (hrc2 : ∀ x, ContinuousWithinAt G2 (Ici x) x)
    (hG1bot : Tendsto G1 atBot (𝓝 0)) (hG1top : Tendsto G1 atTop (𝓝 1))
    (hG2bot : Tendsto G2 atBot (𝓝 0)) (hG2top : Tendsto G2 atTop (𝓝 1))
    (hm1 : ∃ x, 0 < G1 x ∧ G1 x < 1) (hm2 : ∃ x, 0 < G2 x ∧ G2 x < 1)
    (h1 : ∀ x, ContinuousAt G1 x → Tendsto (fun i => F i (a1 i * x + b1 i)) l (𝓝 (G1 x)))
    (h2 : ∀ z, ContinuousAt G2 z → Tendsto (fun i => F i (a2 i * z + b2 i)) l (𝓝 (G2 z))) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, G1 x = G2 (A * x + B) := by
  obtain ⟨x0, hx0, hx0'⟩ := hm1
  obtain ⟨z0, hz0, hz0'⟩ := hm2
  obtain ⟨x1, x2, hx12, hx1c, hx2c, g1p, g1l, g2p, g2l⟩ := two_mid_points hG1 hrc1 hx0 hx0'
  obtain ⟨z1, z2, hz12, hz1c, hz2c, k1p, k1l, k2p, k2l⟩ := two_mid_points hG2 hrc2 hz0 hz0'
  obtain ⟨lo1, hi1, e1⟩ := frame_bound hF ha2 hG2 hG2bot hG2top h2 (h1 x1 hx1c) g1p g1l
  obtain ⟨lo2, hi2, e2⟩ := frame_bound hF ha2 hG2 hG2bot hG2top h2 (h1 x2 hx2c) g2p g2l
  obtain ⟨lo3, hi3, e3⟩ := frame_bound hF ha1 hG1 hG1bot hG1top h1 (h2 z1 hz1c) k1p k1l
  obtain ⟨lo4, hi4, e4⟩ := frame_bound hF ha1 hG1 hG1bot hG1top h1 (h2 z2 hz2c) k2p k2l
  -- ratio ρ = a1/a2 and offset σ = (b1 - b2)/a2
  set K1 := (hi2 - lo1) / (x2 - x1) with hK1
  set K2 := (hi4 - lo3) / (z2 - z1) with hK2
  have hbox : ∀ᶠ i in l, 0 < K2 ∧ (a1 i / a2 i, (b1 i - b2 i) / a2 i) ∈
      Icc (1 / K2) K1 ×ˢ Icc (lo1 - K1 * |x1|) (hi1 + K1 * |x1|) := by
    filter_upwards [e1, e2, e3, e4] with i h1i h2i h3i h4i
    have hpa1 := ha1 i
    have hpa2 := ha2 i
    have hu : (a1 i * x2 + b1 i - b2 i) / a2 i - (a1 i * x1 + b1 i - b2 i) / a2 i =
        a1 i / a2 i * (x2 - x1) := by field_simp; ring
    have hv : (a2 i * z2 + b2 i - b1 i) / a1 i - (a2 i * z1 + b2 i - b1 i) / a1 i =
        a2 i / a1 i * (z2 - z1) := by field_simp; ring
    have hρ : a1 i / a2 i ≤ K1 := by
      rw [hK1, le_div_iff₀ (by linarith)]; linarith
    have hρ' : a2 i / a1 i ≤ K2 := by
      rw [hK2, le_div_iff₀ (by linarith)]; linarith
    have hρpos : 0 < a1 i / a2 i := div_pos hpa1 hpa2
    have hK2pos : 0 < K2 := lt_of_lt_of_le (div_pos hpa2 hpa1) hρ'
    have hρl : 1 / K2 ≤ a1 i / a2 i := by
      rw [div_le_iff₀ hK2pos]
      have : a2 i / a1 i * (a1 i / a2 i) = 1 := by field_simp
      nlinarith
    have hσ : (b1 i - b2 i) / a2 i = (a1 i * x1 + b1 i - b2 i) / a2 i - a1 i / a2 i * x1 := by
      field_simp; ring
    have habs : |a1 i / a2 i * x1| ≤ K1 * |x1| := by
      rw [abs_mul, abs_of_pos hρpos]
      exact mul_le_mul_of_nonneg_right hρ (abs_nonneg _)
    have hab := abs_le.1 habs
    have hσ1 : lo1 - K1 * |x1| ≤ (b1 i - b2 i) / a2 i := by rw [hσ]; linarith [h1i.1, h1i.2]
    have hσ2 : (b1 i - b2 i) / a2 i ≤ hi1 + K1 * |x1| := by rw [hσ]; linarith [h1i.1, h1i.2]
    exact ⟨hK2pos, ⟨hρl, hρ⟩, hσ1, hσ2⟩
  have hcomp : IsCompact (Icc (1 / K2) K1 ×ˢ Icc (lo1 - K1 * |x1|) (hi1 + K1 * |x1|)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨⟨A, B⟩, hAB, hclus⟩ := hcomp.exists_mapClusterPt_of_frequently (hbox.mono fun i h => h.2).frequently
  have hK2pos : 0 < K2 := by
    obtain ⟨i, hi⟩ := hbox.exists
    exact hi.1
  have hA : 0 < A := lt_of_lt_of_le (one_div_pos.2 hK2pos) hAB.1.1
  -- core comparison at continuity points
  have key : ∀ x w, ContinuousAt G1 x → ContinuousAt G2 w →
      (A * x + B < w → G1 x ≤ G2 w) ∧ (w < A * x + B → G2 w ≤ G1 x) := by
    intro x w hxc hwc
    have hcont : Continuous (fun p : ℝ × ℝ => p.1 * x + p.2) := by fun_prop
    constructor
    · intro hlt
      by_contra hgt
      push Not at hgt
      have ev1 := eventually_lt_of_tendsto_mono hF (h2 w hwc) (h1 x hxc) hgt
      have nb : ∀ᶠ p in 𝓝 (A, B), p.1 * x + p.2 < w :=
        hcont.continuousAt.eventually_lt continuousAt_const hlt
      obtain ⟨i, hi1, hi2⟩ := ((hclus.frequently nb).and_eventually ev1).exists
      have hpa2 := ha2 i
      have : a1 i * x + b1 i = a2 i * (a1 i / a2 i * x + (b1 i - b2 i) / a2 i) + b2 i := by
        field_simp; ring
      simp only at hi1
      nlinarith
    · intro hlt
      by_contra hgt
      push Not at hgt
      have ev1 := eventually_lt_of_tendsto_mono hF (h1 x hxc) (h2 w hwc) hgt
      have nb : ∀ᶠ p in 𝓝 (A, B), w < p.1 * x + p.2 :=
        continuousAt_const.eventually_lt hcont.continuousAt hlt
      obtain ⟨i, hi1, hi2⟩ := ((hclus.frequently nb).and_eventually ev1).exists
      have hpa2 := ha2 i
      have : a1 i * x + b1 i = a2 i * (a1 i / a2 i * x + (b1 i - b2 i) / a2 i) + b2 i := by
        field_simp; ring
      simp only at hi1
      nlinarith
  refine ⟨A, hA, B, fun x => le_antisymm ?_ ?_⟩
  · -- G1 x ≤ G2 (A x + B)
    apply le_of_forall_cont_gt hG2 hrc2
    intro w hw hwc
    obtain ⟨x', hx', hx'c⟩ := exists_continuousAt_Ioo hG1
      (show x < x + (w - (A * x + B)) / (2 * A) by
        have : 0 < (w - (A * x + B)) / (2 * A) := div_pos (by linarith) (by linarith)
        linarith)
    have hAx' : A * x' + B < w := by
      have h := hx'.2
      have : A * x' < A * (x + (w - (A * x + B)) / (2 * A)) := mul_lt_mul_of_pos_left h hA
      have h2 : A * (x + (w - (A * x + B)) / (2 * A)) = A * x + (w - (A * x + B)) / 2 := by
        field_simp
      linarith
    exact le_trans (hG1 hx'.1.le) ((key x' w hx'c hwc).1 hAx')
  · -- G2 (A x + B) ≤ G1 x
    apply le_of_forall_cont_gt hG1 hrc1
    intro x' hx' hx'c
    obtain ⟨w, hw, hwc⟩ := exists_continuousAt_Ioo hG2
      (show A * x + B < A * x' + B by nlinarith)
    exact le_trans (hG2 hw.1.le) ((key x' w hx'c hwc).2 hw.2)


section stab

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- S4 (child C2): the residual of the limit law above a continuity point `y` with `0 < G y` is of
the same type as `G`. -/
theorem stability (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (hconv : WeakConv (fun t x => residualCDF μ t (b t + x * a t)) (cdf ν))
    (hlt1 : ∀ x, cdf ν x < 1) (y : ℝ) (hyc : ContinuousAt (cdf ν) y) (hy0 : 0 < cdf ν y) :
    ∃ A > 0, ∃ B : ℝ, ∀ x,
      max 0 ((cdf ν (y + x) - cdf ν y) / (1 - cdf ν y)) = cdf ν (A * x + B) := by
  have hmono : Monotone (cdf ν) := monotone_cdf ν
  have hd : 0 < 1 - cdf ν y := by linarith [hlt1 y]
  obtain ⟨evy, ty⟩ := ratio_tendsto hF hconv hyc hy0
  have hτtop : Tendsto (fun s => s + (b s + y * a s)) atTop atTop :=
    tendsto_atTop_mono' atTop (evy.mono fun s hs => by show s ≤ _; linarith) tendsto_id
  obtain ⟨Gy, hGy⟩ : ∃ Gy : ℝ → ℝ,
      Gy = fun x => max 0 ((cdf ν (y + x) - cdf ν y) / (1 - cdf ν y)) := ⟨_, rfl⟩
  have Gy_nonpos : ∀ x ≤ 0, Gy x = 0 := by
    intro x hx
    rw [hGy]
    apply max_eq_left
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    linarith [hmono (show y + x ≤ y by linarith)]
  have Gy_pos : ∀ x, 0 ≤ x → Gy x = (cdf ν (y + x) - cdf ν y) / (1 - cdf ν y) := by
    intro x hx
    rw [hGy]
    apply max_eq_right
    apply div_nonneg _ hd.le
    linarith [hmono (show y ≤ y + x by linarith)]
  have Gy_mono : Monotone Gy := by
    intro x x' h
    rw [hGy]
    exact max_le_max le_rfl (div_le_div_of_nonneg_right
      (by linarith [hmono (show y + x ≤ y + x' by linarith)]) hd.le)
  have Gy_rc : ∀ x, ContinuousWithinAt Gy (Ici x) x := by
    intro x
    have hc : ContinuousWithinAt (fun x => cdf ν (y + x)) (Ici x) x :=
      ((cdf ν).right_continuous' (y + x)).comp (continuous_const.add continuous_id).continuousWithinAt
        (fun z hz => by change x ≤ z at hz; change y + x ≤ y + z; linarith)
    rw [hGy]
    exact continuousWithinAt_const.max ((hc.sub continuousWithinAt_const).div_const _)
  have Gy_bot : Tendsto Gy atBot (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_le_atBot 0).mono fun x hx => (Gy_nonpos x hx).symm)
  have Gy_top : Tendsto Gy atTop (𝓝 1) := by
    have ht : Tendsto (fun x => cdf ν (y + x)) atTop (𝓝 1) :=
      (tendsto_cdf_atTop ν).comp (tendsto_atTop_add_const_left _ y tendsto_id)
    have h := (ht.sub (tendsto_const_nhds (x := cdf ν y))).div_const (1 - cdf ν y)
    rw [div_self hd.ne'] at h
    exact h.congr' ((eventually_ge_atTop 0).mono fun x hx => (Gy_pos x hx).symm)
  have Gy_mid : ∃ x, 0 < Gy x ∧ Gy x < 1 := by
    obtain ⟨x, hx1, hx2⟩ :=
      ((Gy_top.eventually (lt_mem_nhds (show (1:ℝ) / 2 < 1 by norm_num))).and
        (eventually_ge_atTop 0)).exists
    refine ⟨x, by linarith, ?_⟩
    rw [Gy_pos x hx2, div_lt_one hd]
    linarith [hlt1 (y + x)]
  have h1 : ∀ x, ContinuousAt Gy x → Tendsto (fun s => residualCDF μ (s + (b s + y * a s))
      (a s * x + 0)) atTop (𝓝 (Gy x)) := by
    intro x hxc
    rcases le_or_gt x 0 with hx | hx
    · rw [Gy_nonpos x hx]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun s => ?_)
      dsimp only
      rw [residualCDF_of_nonpos]
      have := ha s
      nlinarith
    · have hGc : ContinuousAt (cdf ν) (y + x) := by
        have heq : (fun z => cdf ν y + (1 - cdf ν y) * Gy (z - y)) =ᶠ[𝓝 (y + x)] cdf ν := by
          filter_upwards [lt_mem_nhds (show y < y + x by linarith)] with z hz
          rw [Gy_pos (z - y) (by linarith)]
          have : y + (z - y) = z := by ring
          rw [this]
          field_simp
          ring
        refine ContinuousAt.congr ?_ heq
        exact continuousAt_const.add (continuousAt_const.mul
          (hxc.comp_of_eq (continuousAt_id.sub continuousAt_const) (by simp)))
      have hpos' : 0 < cdf ν (y + x) := lt_of_lt_of_le hy0 (hmono (by linarith))
      obtain ⟨-, tyx⟩ := ratio_tendsto hF hconv hGc hpos'
      rw [Gy_pos x hx.le]
      have hlim := (tendsto_const_nhds (x := (1:ℝ))).sub (tyx.div ty hd.ne')
      have heq2 : 1 - (1 - cdf ν (y + x)) / (1 - cdf ν y) =
          (cdf ν (y + x) - cdf ν y) / (1 - cdf ν y) := by
        field_simp
        ring
      rw [heq2] at hlim
      refine hlim.congr' (Eventually.of_forall fun s => ?_)
      simp only [Pi.div_apply]
      have hax : 0 ≤ a s * x + 0 := by have := ha s; nlinarith
      rw [residualCDF_eq hF _ hax]
      have e : s + (b s + y * a s) + (a s * x + 0) = s + (b s + (y + x) * a s) := by ring
      rw [e]
      have t1 := tail_pos hF (μ := μ) s
      have t2 := tail_pos hF (μ := μ) (s + (b s + y * a s))
      field_simp
  have h2 : ∀ z, ContinuousAt (cdf ν) z → Tendsto (fun s => residualCDF μ (s + (b s + y * a s))
      (a (s + (b s + y * a s)) * z + b (s + (b s + y * a s)))) atTop (𝓝 (cdf ν z)) := by
    intro z hz
    refine ((hconv z hz).comp hτtop).congr fun s => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  have hF' : ∀ s, Monotone (residualCDF μ (s + (b s + y * a s))) := fun s => residualCDF_mono _
  obtain ⟨A, hA, B, hAB⟩ := type_ident (l := atTop) hF' (a1 := a) (b1 := fun _ => 0)
    (a2 := fun s => a (s + (b s + y * a s))) (b2 := fun s => b (s + (b s + y * a s)))
    ha (fun s => ha _) Gy_mono hmono Gy_rc (cdf ν).right_continuous' Gy_bot Gy_top
    (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν) Gy_mid (exists_mid ν hν) h1 h2
  refine ⟨A, hA, B, fun x => ?_⟩
  have := hAB x
  rw [hGy] at this
  exact this

end stab

/-! ### A Cauchy-type lemma on an additive subsemigroup with small elements -/

lemma mul_mem_of_add {M : Set ℝ} (hadd : ∀ m ∈ M, ∀ m' ∈ M, m + m' ∈ M) {m : ℝ} (hm : m ∈ M) :
    ∀ n : ℕ, ((n : ℝ) + 1) * m ∈ M := by
  intro n
  induction n with
  | zero => simpa using hm
  | succ k ih =>
    have := hadd _ ih _ hm
    have e : (((k + 1 : ℕ) : ℝ) + 1) * m = ((k : ℝ) + 1) * m + m := by push_cast; ring
    rw [e]
    exact this

lemma dense_of_small {M : Set ℝ} (hadd : ∀ m ∈ M, ∀ m' ∈ M, m + m' ∈ M)
    (hsmall : ∀ ε > 0, ∃ m ∈ M, 0 < m ∧ m < ε) {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∃ m ∈ M, s - ε < m ∧ m < s := by
  obtain ⟨m0, hm0, hm0pos, hm0lt⟩ := hsmall (min ε s) (lt_min hε hs)
  have hm0e : m0 < ε := lt_of_lt_of_le hm0lt (min_le_left _ _)
  have hm0s : m0 < s := lt_of_lt_of_le hm0lt (min_le_right _ _)
  have hex : ∃ n : ℕ, s ≤ ((n : ℝ) + 1) * m0 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (s / m0)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hm0pos] at hn
    nlinarith
  classical
  obtain ⟨N, hN, hmin⟩ : ∃ N : ℕ, s ≤ ((N : ℝ) + 1) * m0 ∧ ∀ k < N, ¬ s ≤ ((k : ℝ) + 1) * m0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, zero_add, one_mul] at hN
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hk := hmin k (Nat.lt_succ_self k)
  push Not at hk
  refine ⟨((k : ℝ) + 1) * m0, mul_mem_of_add hadd hm0 k, ?_, hk⟩
  push_cast at hN
  nlinarith

theorem cauchy_mono {V : ℝ → ℝ} {M : Set ℝ} (hM0 : ∀ m ∈ M, 0 < m)
    (hadd : ∀ m ∈ M, ∀ m' ∈ M, m + m' ∈ M) (hsmall : ∀ ε > 0, ∃ m ∈ M, 0 < m ∧ m < ε)
    (hV : ∀ s t, 0 < s → s ≤ t → V s ≤ V t) {V0 : ℝ} (hV0 : ∀ s > 0, V0 ≤ V s)
    (hV0' : ∀ η > 0, ∃ t > 0, V t < V0 + η)
    (heq : ∀ m ∈ M, ∃ e : ℝ, ∀ s > 0, V (m + s) = V s + e) :
    ∃ κ ≥ 0, ∀ s > 0, V s = V0 + κ * s := by
  obtain ⟨e, he_def⟩ : ∃ e : ℝ → ℝ, e = fun m => V (m + 1) - V 1 := ⟨_, rfl⟩
  have he : ∀ m ∈ M, ∀ s > 0, V (m + s) = V s + e m := by
    intro m hm s hs
    obtain ⟨e', he'⟩ := heq m hm
    have h1 := he' 1 one_pos
    rw [he' s hs, he_def]
    simp only
    linarith
  have e_nonneg : ∀ m ∈ M, 0 ≤ e m := fun m hm => by
    have h1 := he m hm 1 one_pos
    have h2 := hV 1 (m + 1) one_pos (by linarith [hM0 m hm])
    linarith
  have e_mono : ∀ m ∈ M, ∀ m' ∈ M, m ≤ m' → e m ≤ e m' := fun m hm m' hm' h => by
    have h1 := he m hm 1 one_pos
    have h2 := he m' hm' 1 one_pos
    have h3 := hV (m + 1) (m' + 1) (by linarith [hM0 m hm]) (by linarith)
    linarith
  have e_add : ∀ m ∈ M, ∀ m' ∈ M, e (m + m') = e m + e m' := by
    intro m hm m' hm'
    have h1 := he (m + m') (hadd m hm m' hm') 1 one_pos
    have h2 := he m hm (m' + 1) (by linarith [hM0 m' hm'])
    have h3 := he m' hm' 1 one_pos
    rw [add_assoc] at h1
    linarith
  have e_mul : ∀ m ∈ M, ∀ n : ℕ, e (((n : ℝ) + 1) * m) = ((n : ℝ) + 1) * e m := by
    intro m hm n
    induction n with
    | zero => simp
    | succ k ih =>
      have h := e_add _ (mul_mem_of_add hadd hm k) m hm
      have e1 : (((k + 1 : ℕ) : ℝ) + 1) * m = ((k : ℝ) + 1) * m + m := by push_cast; ring
      rw [e1, h, ih]
      push_cast
      ring
  have ratio : ∀ m ∈ M, ∀ m' ∈ M, e m * m' = e m' * m := by
    intro m hm m' hm'
    have hmpos := hM0 m hm
    have hm'pos := hM0 m' hm'
    have bound : ∀ n : ℕ, |((n : ℝ) + 1) * (e m * m' - e m' * m)| ≤ m' * e m' := by
      intro n
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊((n : ℝ) + 1) * m / m'⌋₊ := ⟨_, rfl⟩
      have hk1 : (k : ℝ) * m' ≤ ((n : ℝ) + 1) * m := by
        have h := Nat.floor_le (show 0 ≤ ((n : ℝ) + 1) * m / m' by positivity)
        rw [← hk, le_div_iff₀ hm'pos] at h
        exact h
      have hk2 : ((n : ℝ) + 1) * m < ((k : ℝ) + 1) * m' := by
        have h := Nat.lt_floor_add_one (((n : ℝ) + 1) * m / m')
        rw [← hk, div_lt_iff₀ hm'pos] at h
        exact h
      have hup : ((n : ℝ) + 1) * e m ≤ ((k : ℝ) + 1) * e m' := by
        rw [← e_mul m hm n, ← e_mul m' hm' k]
        exact e_mono _ (mul_mem_of_add hadd hm n) _ (mul_mem_of_add hadd hm' k) hk2.le
      have hlo : (k : ℝ) * e m' ≤ ((n : ℝ) + 1) * e m := by
        by_cases hk0 : k = 0
        · rw [hk0, Nat.cast_zero, zero_mul]
          have := e_nonneg m hm
          positivity
        · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          have hkj : (k : ℝ) = (j : ℝ) + 1 := by rw [hj]; push_cast; ring
          rw [hkj] at hk1 ⊢
          rw [← e_mul m' hm' j, ← e_mul m hm n]
          exact e_mono _ (mul_mem_of_add hadd hm' j) _ (mul_mem_of_add hadd hm n) hk1
      have a1 := mul_le_mul_of_nonneg_left hup hm'pos.le
      have a2 := mul_le_mul_of_nonneg_left hlo hm'pos.le
      have a3 := mul_le_mul_of_nonneg_left hk1 (e_nonneg m' hm')
      have a4 := mul_le_mul_of_nonneg_left hk2.le (e_nonneg m' hm')
      rw [abs_le]
      constructor <;> nlinarith
    by_contra hne
    have hΔ : 0 < |e m * m' - e m' * m| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (m' * e m' / |e m * m' - e m' * m|)
    have h := bound n
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h
    rw [div_lt_iff₀ hΔ] at hn
    nlinarith
  obtain ⟨m1, hm1, hm1pos, -⟩ := hsmall 1 one_pos
  have hκ : 0 ≤ e m1 / m1 := div_nonneg (e_nonneg m1 hm1) hm1pos.le
  have hlin : ∀ m ∈ M, e m = e m1 / m1 * m := by
    intro m hm
    have := ratio m hm m1 hm1
    field_simp
    linarith
  refine ⟨e m1 / m1, hκ, fun s hs => ?_⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨t, ht, hVt⟩ := hV0' η hη
    obtain ⟨m, hm, hm1', hm2'⟩ := dense_of_small hadd hsmall hs (lt_min ht hs)
    have h := he m hm (s - m) (by linarith)
    rw [show m + (s - m) = s by ring] at h
    have h2 : V (s - m) ≤ V t := hV _ _ (by linarith) (by linarith [min_le_left t s])
    rw [h, hlin m hm]
    nlinarith [mul_le_mul_of_nonneg_left hm2'.le hκ]
  · apply le_of_forall_pos_le_add
    intro η hη
    have hq : 0 < η / (e m1 / m1 + 1) := div_pos hη (by linarith)
    obtain ⟨m, hm, hm1', hm2'⟩ := dense_of_small hadd hsmall hs (lt_min hs hq)
    have h := he m hm (s - m) (by linarith)
    rw [show m + (s - m) = s by ring] at h
    have h2 := hV0 (s - m) (by linarith)
    have h3 : min s (η / (e m1 / m1 + 1)) ≤ η / (e m1 / m1 + 1) := min_le_right _ _
    have h4 : (e m1 / m1 + 1) * min s (η / (e m1 / m1 + 1)) ≤ η := by
      rw [le_div_iff₀ (by linarith)] at h3
      linarith
    have h5 : 0 ≤ min s (η / (e m1 / m1 + 1)) := le_of_lt (lt_min hs hq)
    rw [h, hlin m hm]
    nlinarith [mul_le_mul_of_nonneg_left hm1'.le hκ]

/-! ### Abstract survival functions -/

/-- Abstract survival-function hypotheses (`S = 1 - G`) for the classification step. -/
structure SurvHyp (S : ℝ → ℝ) : Prop where
  anti : Antitone S
  rc : ∀ x, ContinuousWithinAt S (Ici x) x
  pos : ∀ x, 0 < S x
  le1 : ∀ x, S x ≤ 1
  lim0 : Tendsto S atTop (𝓝 0)
  nondeg : ∃ x, S x < 1
  stab : ∀ y, ContinuousAt S y → S y < 1 → ∃ c > 0, ∃ B : ℝ,
    (∀ u < B, S u = 1) ∧ ∀ u, B ≤ u → S (y + c * (u - B)) = S y * S u

lemma exp_neg_lt_one {s : ℝ} (hs : 0 < s) : Real.exp (-s) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

noncomputable def lowEnd (S : ℝ → ℝ) : ℝ := sInf {x | S x < 1}

noncomputable def lev (S : ℝ → ℝ) (s : ℝ) : ℝ := sInf {x | 1 - Real.exp (-s) ≤ 1 - S x}

section surv
variable {S : ℝ → ℝ}

lemma SurvHyp.exists_cont (H : SurvHyp S) {u v : ℝ} (h : u < v) :
    ∃ x ∈ Ioo u v, ContinuousAt S x := by
  obtain ⟨x, hx, hc⟩ := exists_continuousAt_Ioo (G := fun x => -S x)
    (fun a b hab => neg_le_neg (H.anti hab)) h
  exact ⟨x, hx, by have h2 : ContinuousAt (fun x => -(-S x)) x := hc.neg; simpa using h2⟩

lemma SurvHyp.bdd (H : SurvHyp S) : BddBelow {x | S x < 1} := by
  obtain ⟨x0, hx0⟩ := H.nondeg
  obtain ⟨y, hy, hyc⟩ := H.exists_cont (lt_add_one x0)
  have hy1 : S y < 1 := lt_of_le_of_lt (H.anti hy.1.le) hx0
  obtain ⟨c, hc, B, hB1, -⟩ := H.stab y hyc hy1
  refine ⟨B, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  have := hB1 x hlt
  simp only [mem_ofPred_eq] at hx
  linarith

lemma SurvHyp.low_le (H : SurvHyp S) {x : ℝ} (hx : S x < 1) : lowEnd S ≤ x :=
  csInf_le H.bdd hx

lemma SurvHyp.eq_one_of_lt (H : SurvHyp S) {x : ℝ} (hx : x < lowEnd S) : S x = 1 := by
  by_contra h
  have := H.low_le (lt_of_le_of_ne (H.le1 x) h)
  linarith

lemma SurvHyp.lt_one_of_gt (H : SurvHyp S) {x : ℝ} (hx : lowEnd S < x) : S x < 1 := by
  obtain ⟨z, hz, hzx⟩ := exists_lt_of_csInf_lt
    (show ({x | S x < 1} : Set ℝ).Nonempty from H.nondeg) hx
  exact lt_of_le_of_lt (H.anti hzx.le) hz

lemma SurvHyp.B_le (H : SurvHyp S) {B : ℝ} (hB : ∀ u < B, S u = 1) : B ≤ lowEnd S := by
  by_contra h
  push Not at h
  have h1 := H.lt_one_of_gt (show lowEnd S < (lowEnd S + B) / 2 by linarith)
  have h2 := hB ((lowEnd S + B) / 2) (by linarith)
  linarith

lemma SurvHyp.lev_spec (H : SurvHyp S) {s : ℝ} (hs : 0 < s) :
    S (lev S s) ≤ Real.exp (-s) ∧ ∀ x < lev S s, Real.exp (-s) < S x := by
  have hmono : Monotone (fun x => 1 - S x) := fun a b h => by linarith [H.anti h]
  have hrc : ∀ x, ContinuousWithinAt (fun x => 1 - S x) (Ici x) x :=
    fun x => continuousWithinAt_const.sub (H.rc x)
  have he1 := exp_neg_lt_one hs
  have hep : 0 < Real.exp (-s) := Real.exp_pos _
  obtain ⟨x1, hx1⟩ := (H.lim0.eventually (gt_mem_nhds hep)).exists
  have h0 : 1 - S (lowEnd S - 1) < 1 - Real.exp (-s) := by
    rw [H.eq_one_of_lt (show lowEnd S - 1 < lowEnd S by linarith)]
    linarith
  have h1 : 1 - Real.exp (-s) ≤ 1 - S x1 := by linarith
  obtain ⟨hA, hB⟩ := level_inf (G := fun x => 1 - S x) hmono hrc h0 h1
  have hA' : 1 - Real.exp (-s) ≤ 1 - S (lev S s) := hA
  have hB' : ∀ x < lev S s, 1 - S x < 1 - Real.exp (-s) := hB
  refine ⟨by linarith, fun x hx => ?_⟩
  have := hB' x hx
  linarith

lemma SurvHyp.lev_le (H : SurvHyp S) {s x : ℝ} (hs : 0 < s) (hx : S x ≤ Real.exp (-s)) :
    lev S s ≤ x := by
  by_contra h
  push Not at h
  have := (H.lev_spec hs).2 x h
  linarith

lemma SurvHyp.low_le_lev (H : SurvHyp S) {s : ℝ} (hs : 0 < s) : lowEnd S ≤ lev S s :=
  H.low_le (lt_of_le_of_lt (H.lev_spec hs).1 (exp_neg_lt_one hs))

lemma SurvHyp.lev_mono (H : SurvHyp S) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    lev S s ≤ lev S t :=
  H.lev_le hs (le_trans (H.lev_spec (lt_of_lt_of_le hs hst)).1 (Real.exp_le_exp.mpr (by linarith)))

lemma SurvHyp.exists_lev_gt (H : SurvHyp S) (x : ℝ) : ∃ s > 0, x < lev S s := by
  have hp : (0 : ℝ) < |Real.log (S x)| + 1 := by positivity
  refine ⟨|Real.log (S x)| + 1, hp, ?_⟩
  by_contra h
  push Not at h
  have h1 : S x ≤ S (lev S (|Real.log (S x)| + 1)) := H.anti h
  have h2 := (H.lev_spec hp).1
  have h3 : Real.exp (-(|Real.log (S x)| + 1)) < S x := by
    rw [← Real.lt_log_iff_exp_lt (H.pos x)]
    linarith [neg_abs_le (Real.log (S x))]
  linarith

lemma SurvHyp.lev_near (H : SurvHyp S) {η : ℝ} (hη : 0 < η) :
    ∃ t > 0, lev S t < lowEnd S + η := by
  have hx1 : S (lowEnd S + η / 2) < 1 := H.lt_one_of_gt (by linarith)
  have hl := Real.log_neg (H.pos (lowEnd S + η / 2)) hx1
  refine ⟨-Real.log (S (lowEnd S + η / 2)), by linarith, ?_⟩
  have := H.lev_le (s := -Real.log (S (lowEnd S + η / 2))) (by linarith)
    (by rw [neg_neg, Real.exp_log (H.pos _)])
  linarith

lemma SurvHyp.lev_shift (H : SurvHyp S) {y c B : ℝ} (hc : 0 < c) (hB1 : ∀ u < B, S u = 1)
    (hB2 : ∀ u, B ≤ u → S (y + c * (u - B)) = S y * S u) {s : ℝ} (hs : 0 < s) :
    lev S (-Real.log (S y) + s) = y + c * (lev S s - B) := by
  have hy0 := H.pos y
  have hr : 0 < -Real.log (S y) + s := by
    have := Real.log_nonpos hy0.le (H.le1 y)
    linarith
  have hexp : Real.exp (-(-Real.log (S y) + s)) = S y * Real.exp (-s) := by
    rw [show -(-Real.log (S y) + s) = Real.log (S y) + -s by ring, Real.exp_add,
      Real.exp_log hy0]
  have hBW : B ≤ lev S s := le_trans (H.B_le hB1) (H.low_le_lev hs)
  obtain ⟨hW1, hW2⟩ := H.lev_spec hs
  obtain ⟨hR1, -⟩ := H.lev_spec hr
  obtain ⟨w, hw⟩ : ∃ w, w = lev S (-Real.log (S y) + s) := ⟨_, rfl⟩
  rw [← hw] at hR1 ⊢
  rw [hexp] at hR1
  apply le_antisymm
  · rw [hw]
    apply H.lev_le hr
    rw [hexp, hB2 _ hBW]
    exact mul_le_mul_of_nonneg_left hW1 hy0.le
  · by_contra hlt
    push Not at hlt
    have hes := Real.exp_pos (-s)
    have hes1 := exp_neg_lt_one hs
    rcases lt_or_ge w y with h | h
    · have := H.anti h.le
      nlinarith
    · have hd : 0 ≤ (w - y) / c := div_nonneg (by linarith) hc.le
      have hu : B ≤ B + (w - y) / c := by linarith
      have heq := hB2 _ hu
      have hcw : c * ((w - y) / c) = w - y := by field_simp
      rw [show y + c * (B + (w - y) / c - B) = w by rw [add_sub_cancel_left, hcw]; ring] at heq
      have hult : B + (w - y) / c < lev S s := by
        have : (w - y) / c < lev S s - B := by
          rw [div_lt_iff₀ hc]
          linarith
        linarith
      have := hW2 _ hult
      rw [heq] at hR1
      nlinarith

end surv

section dense
variable {S : ℝ → ℝ}

lemma SurvHyp.add_mem (H : SurvHyp S) {y y' : ℝ} (hyc : ContinuousAt S y) (hy : lowEnd S < y)
    (hyc' : ContinuousAt S y') (hy' : lowEnd S < y') :
    ∃ z, ContinuousAt S z ∧ lowEnd S < z ∧
      -Real.log (S z) = -Real.log (S y) + -Real.log (S y') := by
  obtain ⟨c, hc, B, hB1, hB2⟩ := H.stab y hyc (H.lt_one_of_gt hy)
  have hBL := H.B_le hB1
  have hyB : B < y' := lt_of_le_of_lt hBL hy'
  have hzy : y < y + c * (y' - B) := by nlinarith
  refine ⟨y + c * (y' - B), ?_, by linarith, ?_⟩
  · have hin : B + (y + c * (y' - B) - y) / c = y' := by
      have h1 : c * (y' - B) / c = y' - B := by field_simp
      rw [show y + c * (y' - B) - y = c * (y' - B) by ring, h1]
      ring
    have hg : ContinuousAt (fun x : ℝ => B + (x - y) / c) (y + c * (y' - B)) := by fun_prop
    have hS' : ContinuousAt S (B + (y + c * (y' - B) - y) / c) := by rw [hin]; exact hyc'
    have hcomp : ContinuousAt (fun x => S (B + (x - y) / c)) (y + c * (y' - B)) :=
      ContinuousAt.comp (g := S) hS' hg
    have hfun : ContinuousAt (fun x => S y * S (B + (x - y) / c)) (y + c * (y' - B)) :=
      continuousAt_const.mul hcomp
    apply hfun.congr
    filter_upwards [lt_mem_nhds hzy] with x hx
    have hu : B ≤ B + (x - y) / c := by
      have := div_nonneg (show (0 : ℝ) ≤ x - y by linarith) hc.le
      linarith
    have h2 := hB2 _ hu
    have hcw : c * ((x - y) / c) = x - y := by field_simp
    rw [show y + c * (B + (x - y) / c - B) = x by rw [add_sub_cancel_left, hcw]; ring] at h2
    exact h2.symm
  · rw [hB2 y' hyB.le, Real.log_mul (H.pos y).ne' (H.pos y').ne']
    ring

lemma SurvHyp.small (H : SurvHyp S) (hL : S (lowEnd S) = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, ContinuousAt S y ∧ lowEnd S < y ∧ -Real.log (S y) < ε := by
  have hev : ∀ᶠ x in 𝓝[≥] (lowEnd S), Real.exp (-ε) < S x :=
    (H.rc (lowEnd S)).eventually
      (lt_mem_nhds (show Real.exp (-ε) < S (lowEnd S) by rw [hL]; exact exp_neg_lt_one hε))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp hev
  obtain ⟨y, hy, hyc⟩ := H.exists_cont (show lowEnd S < u from hu)
  refine ⟨y, hyc, hy.1, ?_⟩
  have h1 : Real.exp (-ε) < S y := hsub ⟨hy.1.le, hy.2⟩
  have := (Real.lt_log_iff_exp_lt (H.pos y)).mpr h1
  linarith

lemma SurvHyp.formula (H : SurvHyp S) {F : ℝ → ℝ} (hF : ∀ s > 0, lev S s = F s) {x s : ℝ}
    (hx : lowEnd S < x) (hs : 0 < s) (hFs : F s = x) (hmono : ∀ t > 0, F t ≤ x → t ≤ s) :
    S x = Real.exp (-s) := by
  have hx1 := H.lt_one_of_gt hx
  have hl := Real.log_neg (H.pos x) hx1
  have ht : 0 < -Real.log (S x) := by linarith
  have hWt : lev S (-Real.log (S x)) ≤ x :=
    H.lev_le ht (by rw [neg_neg, Real.exp_log (H.pos x)])
  rw [hF _ ht] at hWt
  have hts := hmono _ ht hWt
  have h1 : S x ≤ Real.exp (-s) := by
    have := (H.lev_spec hs).1
    rw [hF s hs, hFs] at this
    exact this
  have h2 : Real.exp (-s) ≤ S x := by
    have := Real.exp_le_exp.mpr (show -s ≤ -(-Real.log (S x)) by linarith)
    rw [neg_neg, Real.exp_log (H.pos x)] at this
    exact this
  linarith

theorem SurvHyp.dense_class (H : SurvHyp S) (hL : S (lowEnd S) = 1) :
    (∃ κ > 0, ∀ x, lowEnd S < x → S x = Real.exp (-((x - lowEnd S) / κ))) ∨
    (∃ p < lowEnd S, ∃ κ > 0, ∀ x, lowEnd S < x →
      S x = Real.exp (-(Real.log ((x - p) / (lowEnd S - p)) / κ))) := by
  set L := lowEnd S with hLdef
  obtain ⟨M, hMdef⟩ : ∃ M : Set ℝ,
      M = {m | ∃ y, ContinuousAt S y ∧ L < y ∧ m = -Real.log (S y)} := ⟨_, rfl⟩
  have hM0 : ∀ m ∈ M, 0 < m := by
    intro m hm
    rw [hMdef] at hm
    obtain ⟨y, -, hy, rfl⟩ := hm
    have := Real.log_neg (H.pos y) (H.lt_one_of_gt hy)
    linarith
  have hadd : ∀ m ∈ M, ∀ m' ∈ M, m + m' ∈ M := by
    intro m hm m' hm'
    rw [hMdef] at hm hm' ⊢
    obtain ⟨y, hyc, hy, rfl⟩ := hm
    obtain ⟨y', hyc', hy', rfl⟩ := hm'
    obtain ⟨z, hzc, hz, hzeq⟩ := H.add_mem hyc hy hyc' hy'
    exact ⟨z, hzc, hz, hzeq.symm⟩
  have hsmall : ∀ ε > 0, ∃ m ∈ M, 0 < m ∧ m < ε := by
    intro ε hε
    obtain ⟨y, hyc, hy, hlt⟩ := H.small hL hε
    have hm : -Real.log (S y) ∈ M := by rw [hMdef]; exact ⟨y, hyc, hy, rfl⟩
    exact ⟨_, hm, hM0 _ hm, hlt⟩
  have haff : ∀ m ∈ M, ∃ c > 0, ∃ d : ℝ, ∀ s > 0, lev S (m + s) = c * lev S s + d := by
    intro m hm
    rw [hMdef] at hm
    obtain ⟨y, hyc, hy, rfl⟩ := hm
    obtain ⟨c, hc, B, hB1, hB2⟩ := H.stab y hyc (H.lt_one_of_gt hy)
    refine ⟨c, hc, y - c * B, fun s hs => ?_⟩
    rw [H.lev_shift hc hB1 hB2 hs]
    ring
  have comm : ∀ m ∈ M, ∀ m' ∈ M, ∀ c d c' d' : ℝ,
      (∀ s > 0, lev S (m + s) = c * lev S s + d) →
      (∀ s > 0, lev S (m' + s) = c' * lev S s + d') → c * d' + d = c' * d + d' := by
    intro m hm m' hm' c d c' d' h h'
    have hmp := hM0 m hm
    have hm'p := hM0 m' hm'
    have h1 := h (m' + 1) (by linarith)
    have h2 := h' 1 one_pos
    have h3 := h' (m + 1) (by linarith)
    have h4 := h 1 one_pos
    rw [show m + (m' + 1) = m' + (m + 1) by ring] at h1
    linear_combination h3 - h1 - c * h2 + c' * h4
  have hunb : ∀ x : ℝ, ∃ s > 0, x < lev S s := H.exists_lev_gt
  by_cases hall : ∀ m ∈ M, ∀ c > 0, ∀ d : ℝ, (∀ s > 0, lev S (m + s) = c * lev S s + d) → c = 1
  · left
    obtain ⟨κ, hκ0, hκ⟩ := cauchy_mono (V := lev S) (V0 := L) hM0 hadd hsmall
      (fun s t hs hst => H.lev_mono hs hst) (fun s hs => H.low_le_lev hs)
      (fun η hη => H.lev_near hη) (by
        intro m hm
        obtain ⟨c, hc, d, hcd⟩ := haff m hm
        have h1 := hall m hm c hc d hcd
        refine ⟨d, fun s hs => ?_⟩
        rw [hcd s hs, h1]
        ring)
    have hκpos : 0 < κ := by
      rcases hκ0.lt_or_eq with h | h
      · exact h
      · obtain ⟨s, hs, hlt⟩ := hunb L
        rw [hκ s hs, ← h] at hlt
        linarith
    refine ⟨κ, hκpos, fun x hx => ?_⟩
    apply H.formula (F := fun s => L + κ * s) hκ hx (div_pos (by linarith) hκpos)
    · field_simp
      ring
    · intro t ht hFt
      rw [le_div_iff₀ hκpos]
      linarith
  · right
    push Not at hall
    obtain ⟨m0, hm0, c0, hc0, d0, hcd0, hc01⟩ := hall
    have hc01' : 1 - c0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hc01)
    set p := d0 / (1 - c0) with hp
    have hrel : ∀ m ∈ M, ∃ c > 0, ∀ s > 0, lev S (m + s) - p = c * (lev S s - p) := by
      intro m hm
      obtain ⟨c, hc, d, hcd⟩ := haff m hm
      have hcm := comm m0 hm0 m hm c0 d0 c d hcd0 hcd
      have hdp : d = p * (1 - c) := by
        rw [hp]
        field_simp
        linarith
      refine ⟨c, hc, fun s hs => ?_⟩
      rw [hcd s hs, hdp]
      ring
    have hWp : ∀ s > 0, p < lev S s := by
      intro s0 hs0
      by_contra hle
      push Not at hle
      obtain ⟨s1, hs1, hlt1⟩ := hunb p
      obtain ⟨m, hm, hm1, -⟩ := dense_of_small hadd hsmall (show (0 : ℝ) < s1 + 1 by linarith)
        one_pos
      obtain ⟨c, hc, hceq⟩ := hrel m hm
      have h1 := hceq s0 hs0
      have h2 := H.lev_mono hs1 (show s1 ≤ m + s0 by linarith)
      have h3 : c * (lev S s0 - p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)
      linarith
    have hpL : p < L := by
      rcases lt_or_ge p L with h | h
      · exact h
      exfalso
      rcases h.lt_or_eq with h' | h'
      · obtain ⟨t, ht, hlt⟩ := H.lev_near (show 0 < p - L by linarith)
        have := hWp t ht
        linarith
      · obtain ⟨c, hc, hceq⟩ := hrel m0 hm0
        have hm0p := hM0 m0 hm0
        have hg := hWp m0 hm0p
        obtain ⟨t, ht, hlt⟩ := H.lev_near
          (show 0 < (lev S m0 - p) / (c + 1) from div_pos (by linarith) (by linarith))
        have h1 := hceq t ht
        have h2 := H.lev_mono hm0p (show m0 ≤ m0 + t by linarith)
        have h3 := hWp t ht
        have h4 : (c + 1) * ((lev S m0 - p) / (c + 1)) = lev S m0 - p := by field_simp
        rw [← hLdef, h'] at hlt
        have h5 := mul_lt_mul_of_pos_left
          (show lev S t - p < (lev S m0 - p) / (c + 1) by linarith) hc
        have h6 : 0 < (lev S m0 - p) / (c + 1) := div_pos (by linarith) (by linarith)
        nlinarith
    have hLp : 0 < L - p := by linarith
    obtain ⟨κ, hκ0, hκ⟩ := cauchy_mono (V := fun s => Real.log (lev S s - p))
      (V0 := Real.log (L - p)) hM0 hadd hsmall
      (fun s t hs hst => Real.log_le_log (by linarith [hWp s hs])
        (by linarith [H.lev_mono hs hst]))
      (fun s hs => Real.log_le_log hLp (by linarith [H.low_le_lev hs]))
      (by
        intro η hη
        have he : 1 < Real.exp η := Real.one_lt_exp_iff.mpr hη
        obtain ⟨t, ht, hlt⟩ := H.lev_near
          (show 0 < (L - p) * (Real.exp η - 1) from mul_pos hLp (by linarith))
        refine ⟨t, ht, ?_⟩
        have h1 : lev S t - p < (L - p) * Real.exp η := by nlinarith
        have h2 := Real.log_lt_log (by linarith [hWp t ht]) h1
        rw [Real.log_mul hLp.ne' (Real.exp_pos η).ne', Real.log_exp] at h2
        exact h2)
      (by
        intro m hm
        obtain ⟨c, hc, hceq⟩ := hrel m hm
        refine ⟨Real.log c, fun s hs => ?_⟩
        have hpos : 0 < lev S s - p := by linarith [hWp s hs]
        show Real.log (lev S (m + s) - p) = Real.log (lev S s - p) + Real.log c
        rw [hceq s hs, Real.log_mul hc.ne' hpos.ne']
        ring)
    have hW : ∀ s > 0, lev S s = p + (L - p) * Real.exp (κ * s) := by
      intro s hs
      have h1 := hκ s hs
      have hpos : 0 < lev S s - p := by linarith [hWp s hs]
      have h2 := congrArg Real.exp h1
      rw [Real.exp_log hpos, Real.exp_add, Real.exp_log hLp] at h2
      linarith
    have hκpos : 0 < κ := by
      rcases hκ0.lt_or_eq with h | h
      · exact h
      · obtain ⟨s, hs, hlt⟩ := hunb L
        rw [hW s hs, ← h, zero_mul, Real.exp_zero] at hlt
        linarith
    refine ⟨p, hpL, κ, hκpos, fun x hx => ?_⟩
    have hrat : 1 < (x - p) / (L - p) := by rw [lt_div_iff₀ hLp]; linarith
    have hrpos : 0 < (x - p) / (L - p) := by linarith
    have hlogpos : 0 < Real.log ((x - p) / (L - p)) := Real.log_pos hrat
    apply H.formula (F := fun s => p + (L - p) * Real.exp (κ * s)) hW hx
      (div_pos hlogpos hκpos)
    · rw [show κ * (Real.log ((x - p) / (L - p)) / κ) = Real.log ((x - p) / (L - p)) by
        field_simp, Real.exp_log hrpos]
      field_simp
      ring
    · intro t ht hFt
      rw [le_div_iff₀ hκpos]
      have h1 : Real.exp (κ * t) ≤ (x - p) / (L - p) := by
        rw [le_div_iff₀ hLp]
        linarith
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      linarith

end dense

section lattice
variable {S : ℝ → ℝ}

lemma step_ind (_hS : Antitone S) {q c e : ℝ} (hc : 0 < c) (z : ℕ → ℝ)
    (hz : ∀ n, z (n + 1) = c * z n + e) (h01 : z 0 < z 1)
    (h0 : ∀ x, z 0 ≤ x → x < z 1 → S x = q)
    (hφ : ∀ u, z 0 ≤ u → S (c * u + e) = q * S u) :
    ∀ n : ℕ, ∀ x, z n ≤ x → x < z (n + 1) → S x = q ^ (n + 1) := by
  have hinc : ∀ n, z n < z (n + 1) := by
    intro n
    induction n with
    | zero => exact h01
    | succ k ih =>
      rw [hz (k + 1)]
      have h1 := hz k
      have h2 := mul_lt_mul_of_pos_left ih hc
      linarith
  have hmono : Monotone z := monotone_nat_of_le_succ (fun n => (hinc n).le)
  intro n
  induction n with
  | zero =>
    intro x hx1 hx2
    rw [zero_add, pow_one]
    exact h0 x hx1 hx2
  | succ k ih =>
    intro x hx1 hx2
    have hu0 : c * ((x - e) / c) = x - e := by field_simp
    have hu : c * ((x - e) / c) + e = x := by rw [hu0]; ring
    have hk1 : z k ≤ (x - e) / c := by
      rw [le_div_iff₀ hc]
      rw [hz k] at hx1
      linarith
    have hk2 : (x - e) / c < z (k + 1) := by
      rw [div_lt_iff₀ hc]
      rw [hz (k + 1)] at hx2
      linarith
    have h := hφ ((x - e) / c) (le_trans (hmono (Nat.zero_le k)) hk1)
    rw [hu] at h
    rw [h, ih _ hk1 hk2]
    ring

lemma SurvHyp.flat (H : SurvHyp S) (hL : S (lowEnd S) < 1) {y c B : ℝ} (hc : 0 < c)
    (hB1 : ∀ u < B, S u = 1) (hB2 : ∀ u, B ≤ u → S (y + c * (u - B)) = S y * S u) :
    B < lowEnd S ∧ (∀ x, y ≤ x → x < y + c * (lowEnd S - B) → S x = S y) ∧
      S (y + c * (lowEnd S - B)) = S y * S (lowEnd S) := by
  have hBL := H.B_le hB1
  have hy0 := H.pos y
  have hBlt : B < lowEnd S := by
    rcases hBL.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hB2 B le_rfl
      rw [sub_self, mul_zero, add_zero] at h1
      have h2 : S B = 1 := by
        have : S y * (S B - 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h3 | h3
        · linarith
        · linarith
      rw [h] at h2
      linarith
  refine ⟨hBlt, fun x hx1 hx2 => ?_, hB2 _ hBL⟩
  have hcw : c * ((x - y) / c) = x - y := by field_simp
  have hu : B ≤ B + (x - y) / c := by
    have := div_nonneg (show (0 : ℝ) ≤ x - y by linarith) hc.le
    linarith
  have hu2 : B + (x - y) / c < lowEnd S := by
    have : (x - y) / c < lowEnd S - B := by
      rw [div_lt_iff₀ hc]
      linarith
    linarith
  have h := hB2 _ hu
  rw [show y + c * (B + (x - y) / c - B) = x by rw [add_sub_cancel_left, hcw]; ring,
    H.eq_one_of_lt hu2, mul_one] at h
  exact h

lemma SurvHyp.gap (H : SurvHyp S) (hL : S (lowEnd S) < 1) :
    ∃ y0, ContinuousAt S y0 ∧ lowEnd S < y0 ∧ S y0 = S (lowEnd S) := by
  have hq0 := H.pos (lowEnd S)
  have hqq : S (lowEnd S) * S (lowEnd S) < S (lowEnd S) := by nlinarith
  have rc_above : ∀ θ < S (lowEnd S), ∃ u, lowEnd S < u ∧ ∀ x, lowEnd S ≤ x → x < u → θ < S x := by
    intro θ hθ
    have hev : ∀ᶠ x in 𝓝[≥] (lowEnd S), θ < S x := (H.rc (lowEnd S)).eventually (lt_mem_nhds hθ)
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp hev
    exact ⟨u, hu, fun x hx1 hx2 => hsub ⟨hx1, hx2⟩⟩
  obtain ⟨u, hu, hu2⟩ := rc_above _ hqq
  obtain ⟨y1, hy1, hy1c⟩ := H.exists_cont hu
  refine ⟨y1, hy1c, hy1.1, ?_⟩
  have hy1q : S y1 ≤ S (lowEnd S) := H.anti hy1.1.le
  have hy1big := hu2 y1 hy1.1.le hy1.2
  by_contra hne
  have hlt : S y1 < S (lowEnd S) := lt_of_le_of_ne hy1q hne
  obtain ⟨u', hu', hu'2⟩ := rc_above _ hlt
  obtain ⟨y', hy', hy'c⟩ := H.exists_cont (lt_min hu' hy1.1)
  have hy'L : lowEnd S < y' := hy'.1
  have hy'u : y' < u' := lt_of_lt_of_le hy'.2 (min_le_left _ _)
  have hy'y1 : y' < y1 := lt_of_lt_of_le hy'.2 (min_le_right _ _)
  have hSy' := hu'2 y' hy'L.le hy'u
  have hSy'q : S y' ≤ S (lowEnd S) := H.anti hy'L.le
  obtain ⟨c, hc, B, hB1, hB2⟩ := H.stab y' hy'c (H.lt_one_of_gt hy'L)
  obtain ⟨hBL, hflat, hj⟩ := H.flat hL hc hB1 hB2
  rcases lt_or_ge y1 (y' + c * (lowEnd S - B)) with h | h
  · have := hflat y1 hy'y1.le h
    linarith
  · have h1 := H.anti h
    rw [hj] at h1
    have h2 : S y' * S (lowEnd S) ≤ S (lowEnd S) * S (lowEnd S) :=
      mul_le_mul_of_nonneg_right hSy'q hq0.le
    linarith

theorem SurvHyp.lattice_class (H : SurvHyp S) (hL : S (lowEnd S) < 1) :
    (∃ e > 0, ∀ n : ℕ, ∀ x, lowEnd S + n * e ≤ x → x < lowEnd S + (n + 1) * e →
      S x = S (lowEnd S) ^ (n + 1)) ∨
    (∃ p < lowEnd S, ∃ c > 1, ∀ n : ℕ, ∀ x, p + c ^ n * (lowEnd S - p) ≤ x →
      x < p + c ^ (n + 1) * (lowEnd S - p) → S x = S (lowEnd S) ^ (n + 1)) := by
  obtain ⟨y0, hy0c, hy0L, hy0q⟩ := H.gap hL
  obtain ⟨c, hc, B, hB1, hB2⟩ := H.stab y0 hy0c (H.lt_one_of_gt hy0L)
  obtain ⟨hBL, hflat, hj⟩ := H.flat hL hc hB1 hB2
  have hq0 := H.pos (lowEnd S)
  have h0 : ∀ x, lowEnd S ≤ x → x < c * lowEnd S + (y0 - c * B) → S x = S (lowEnd S) := by
    intro x hx1 hx2
    rcases le_or_gt x y0 with h | h
    · have h1 := H.anti hx1
      have h2 := H.anti h
      linarith
    · rw [hflat x h.le (by linarith), hy0q]
  have hφ : ∀ u, lowEnd S ≤ u → S (c * u + (y0 - c * B)) = S (lowEnd S) * S u := by
    intro u hu
    have h := hB2 u (by linarith)
    rw [show y0 + c * (u - B) = c * u + (y0 - c * B) by ring, hy0q] at h
    exact h
  have hφL : lowEnd S < c * lowEnd S + (y0 - c * B) := by nlinarith
  rcases lt_trichotomy c 1 with hc1 | hc1 | hc1
  · exfalso
    have h1c : 0 < 1 - c := by linarith
    set p := (y0 - c * B) / (1 - c) with hp
    have hpe : p * (1 - c) = y0 - c * B := by rw [hp]; field_simp
    have hLp : lowEnd S < p := by nlinarith
    have hstep := step_ind H.anti (q := S (lowEnd S)) (e := y0 - c * B) hc (fun n => p + c ^ n * (lowEnd S - p))
      (fun n => by simp only [pow_succ]; linear_combination hpe)
      (by simp only [pow_zero, one_mul, pow_one]; nlinarith)
      (fun x hx1 hx2 => h0 x (by simpa using hx1) (by simp only [pow_one] at hx2; nlinarith))
      (fun u hu => hφ u (by simpa using hu))
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (H.pos p) hL
    have hcn := pow_pos hc n
    have hz1 : p + c ^ n * (lowEnd S - p) < p + c ^ (n + 1) * (lowEnd S - p) := by
      rw [pow_succ]
      nlinarith
    have h1 := hstep n (p + c ^ n * (lowEnd S - p)) le_rfl hz1
    have h2 : S p ≤ S (p + c ^ n * (lowEnd S - p)) := H.anti (by nlinarith)
    have h3 : S (lowEnd S) ^ (n + 1) ≤ S (lowEnd S) ^ n := by
      rw [pow_succ]
      have := pow_pos hq0 n
      nlinarith
    linarith
  · left
    subst hc1
    refine ⟨y0 - B, by linarith, fun n x hx1 hx2 => ?_⟩
    have hstep := step_ind H.anti (q := S (lowEnd S)) (e := y0 - 1 * B) one_pos
      (fun n => lowEnd S + n * (y0 - B))
      (fun n => by push_cast; ring)
      (by simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul]; linarith)
      (fun x hx1 hx2 => h0 x (by simpa using hx1) (by simp only [Nat.cast_one, one_mul] at hx2; linarith))
      (fun u hu => hφ u (by simpa using hu))
    exact hstep n x hx1 (by push_cast; linarith)
  · right
    have h1c : 1 - c < 0 := by linarith
    have hne : 1 - c ≠ 0 := ne_of_lt h1c
    set p := (y0 - c * B) / (1 - c) with hp
    have hpe : p * (1 - c) = y0 - c * B := by rw [hp]; field_simp
    have hLp : p < lowEnd S := by nlinarith
    refine ⟨p, hLp, c, hc1, ?_⟩
    exact step_ind H.anti (q := S (lowEnd S)) (e := y0 - c * B) hc (fun n => p + c ^ n * (lowEnd S - p))
      (fun n => by simp only [pow_succ]; linear_combination hpe)
      (by simp only [pow_zero, one_mul, pow_one]; nlinarith)
      (fun x hx1 hx2 => h0 x (by simpa using hx1) (by simp only [pow_one] at hx2; nlinarith))
      (fun u hu => hφ u (by simpa using hu))

end lattice


section classify
open MeasureTheory ProbabilityTheory BalkemaDeHaan.LimitTypes

theorem classify (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmid : ∃ x, 0 < cdf ν x ∧ cdf ν x < 1) (hlt1 : ∀ x, cdf ν x < 1)
    (hstab : ∀ y, ContinuousAt (cdf ν) y → 0 < cdf ν y → ∃ A > 0, ∃ B : ℝ, ∀ x,
       max 0 ((cdf ν (y + x) - cdf ν y) / (1 - cdf ν y)) = cdf ν (A * x + B)) :
    IsResidualLimitType (cdf ν) := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → ℝ, S = fun x => 1 - cdf ν x := ⟨_, rfl⟩
  have hcdf : ∀ x, cdf ν x = 1 - S x := fun x => by rw [hSdef]; ring
  have H : SurvHyp S := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      simp only [hSdef]
      linarith [monotone_cdf ν hab]
    · intro x
      simp only [hSdef]
      exact continuousWithinAt_const.sub ((cdf ν).right_continuous x)
    · intro x
      simp only [hSdef]
      linarith [hlt1 x]
    · intro x
      simp only [hSdef]
      linarith [cdf_nonneg ν x]
    · have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub
        (tendsto_cdf_atTop ν)
      rw [sub_self] at h
      rw [hSdef]
      exact h
    · obtain ⟨x, hx0, -⟩ := hmid
      exact ⟨x, by simp only [hSdef]; linarith⟩
    · intro y hyc hy1
      have hyc' : ContinuousAt (cdf ν) y := by
        have h2 : ContinuousAt (fun x => 1 - S x) y := continuousAt_const.sub hyc
        have h3 : (fun x => 1 - S x) = fun x => cdf ν x := by
          funext x
          rw [hcdf]
        rw [h3] at h2
        exact h2
      have hy0 : 0 < cdf ν y := by rw [hcdf]; linarith
      obtain ⟨A, hA, B, hAB⟩ := hstab y hyc' hy0
      have hd : 0 < 1 - cdf ν y := by linarith [hlt1 y]
      have hAu : ∀ u, A * ((u - B) / A) + B = u := fun u => by field_simp; ring
      refine ⟨1 / A, by positivity, B, fun u hu => ?_, fun u hu => ?_⟩
      · have h := hAB ((u - B) / A)
        rw [hAu u] at h
        have hneg : (u - B) / A < 0 := div_neg_of_neg_of_pos (by linarith) hA
        have hle : cdf ν (y + (u - B) / A) ≤ cdf ν y := monotone_cdf ν (by linarith)
        have hnp : (cdf ν (y + (u - B) / A) - cdf ν y) / (1 - cdf ν y) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
        rw [max_eq_left hnp] at h
        simp only [hSdef]
        linarith
      · have h := hAB ((u - B) / A)
        rw [hAu u] at h
        have hnn : 0 ≤ (u - B) / A := div_nonneg (by linarith) hA.le
        have hle : cdf ν y ≤ cdf ν (y + (u - B) / A) := monotone_cdf ν (by linarith)
        have hp : 0 ≤ (cdf ν (y + (u - B) / A) - cdf ν y) / (1 - cdf ν y) :=
          div_nonneg (by linarith) hd.le
        rw [max_eq_right hp, div_eq_iff hd.ne'] at h
        rw [show y + 1 / A * (u - B) = y + (u - B) / A by ring]
        simp only [hSdef]
        linear_combination -h
  have hcdfL : ∀ x, x < lowEnd S → cdf ν x = 0 := fun x hx => by
    rw [hcdf, H.eq_one_of_lt hx]
    ring
  unfold IsResidualLimitType IsOfType
  rcases (H.le1 (lowEnd S)).lt_or_eq with hL | hL
  · have hq0 := H.pos (lowEnd S)
    have hγ : 0 < -Real.log (S (lowEnd S)) := by linarith [Real.log_neg hq0 hL]
    have hqexp : ∀ n : ℕ, S (lowEnd S) ^ (n + 1) =
        Real.exp (-(-Real.log (S (lowEnd S))) * (((n + 1 : ℕ) : ℤ) : ℝ)) := by
      intro n
      rw [neg_neg, show (((n + 1 : ℕ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
    rcases H.lattice_class hL with ⟨e, he, hS⟩ | ⟨p, hpL, c, hc, hS⟩
    · right; left
      refine ⟨_, hγ, 1 / e, by positivity, -lowEnd S / e, fun x => ?_⟩
      unfold PiDiscreteLaw
      rw [show 1 / e * x + -lowEnd S / e = (x - lowEnd S) / e by ring]
      rcases lt_or_ge x (lowEnd S) with hx | hx
      · rw [if_pos (div_neg_of_neg_of_pos (by linarith) he), hcdfL x hx]
      · have hz : 0 ≤ (x - lowEnd S) / e := div_nonneg (by linarith) he.le
        rw [if_neg (not_lt.mpr hz)]
        obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊(x - lowEnd S) / e⌋₊ := ⟨_, rfl⟩
        have hn1 : (n : ℝ) ≤ (x - lowEnd S) / e := by rw [hn]; exact Nat.floor_le hz
        have hn2 : (x - lowEnd S) / e < n + 1 := by rw [hn]; exact Nat.lt_floor_add_one _
        have hfl : ⌊1 + (x - lowEnd S) / e⌋ = ((n + 1 : ℕ) : ℤ) := by
          rw [Int.floor_eq_iff]
          push_cast
          constructor <;> linarith
        rw [le_div_iff₀ he] at hn1
        rw [div_lt_iff₀ he] at hn2
        rw [hfl, hcdf, hS n x (by linarith) (by linarith), hqexp n]
    · right; right; right
      have hlc : 0 < Real.log c := Real.log_pos hc
      have hLp : 0 < lowEnd S - p := by linarith
      refine ⟨_, hγ, 1 / Real.log c, by positivity, 1 / (lowEnd S - p), by positivity,
        -lowEnd S / (lowEnd S - p), fun x => ?_⟩
      unfold GammaDiscreteLaw
      rw [show 1 / (lowEnd S - p) * x + -lowEnd S / (lowEnd S - p) =
        (x - lowEnd S) / (lowEnd S - p) by ring]
      rcases lt_or_ge x (lowEnd S) with hx | hx
      · rw [if_pos (div_neg_of_neg_of_pos (by linarith) hLp), hcdfL x hx]
      · have hz : 0 ≤ (x - lowEnd S) / (lowEnd S - p) := div_nonneg (by linarith) hLp.le
        rw [if_neg (not_lt.mpr hz)]
        have hr : 1 + (x - lowEnd S) / (lowEnd S - p) = (x - p) / (lowEnd S - p) := by
          field_simp
          ring
        rw [hr]
        have hr1 : 1 ≤ (x - p) / (lowEnd S - p) := by rw [le_div_iff₀ hLp]; linarith
        have hrpos : 0 < (x - p) / (lowEnd S - p) := by linarith
        have ht : 0 ≤ 1 / Real.log c * Real.log ((x - p) / (lowEnd S - p)) := by
          have := Real.log_nonneg hr1
          positivity
        obtain ⟨n, hn⟩ : ∃ n : ℕ,
            n = ⌊1 / Real.log c * Real.log ((x - p) / (lowEnd S - p))⌋₊ := ⟨_, rfl⟩
        have hn1 : (n : ℝ) ≤ 1 / Real.log c * Real.log ((x - p) / (lowEnd S - p)) := by
          rw [hn]; exact Nat.floor_le ht
        have hn2 : 1 / Real.log c * Real.log ((x - p) / (lowEnd S - p)) < n + 1 := by
          rw [hn]; exact Nat.lt_floor_add_one _
        have hfl : ⌊1 + 1 / Real.log c * Real.log ((x - p) / (lowEnd S - p))⌋ =
            ((n + 1 : ℕ) : ℤ) := by
          rw [Int.floor_eq_iff]
          push_cast
          constructor <;> linarith
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlc] at hn1
        rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hlc] at hn2
        have hc0 : 0 < c := by linarith
        have hcn : c ^ n ≤ (x - p) / (lowEnd S - p) := by
          rw [← Real.exp_log hc0, ← Real.exp_nat_mul, ← Real.le_log_iff_exp_le hrpos]
          linarith
        have hcn1 : (x - p) / (lowEnd S - p) < c ^ (n + 1) := by
          rw [← Real.exp_log hc0, ← Real.exp_nat_mul, ← Real.log_lt_iff_lt_exp hrpos]
          push_cast
          linarith
        rw [le_div_iff₀ hLp] at hcn
        rw [div_lt_iff₀ hLp] at hcn1
        rw [hfl, hcdf, hS n x (by linarith) (by linarith), hqexp n]
  · rcases H.dense_class hL with ⟨κ, hκ, hS⟩ | ⟨p, hpL, κ, hκ, hS⟩
    · left
      refine ⟨1 / κ, by positivity, -lowEnd S / κ, fun x => ?_⟩
      unfold PiLaw
      rw [show 1 / κ * x + -lowEnd S / κ = (x - lowEnd S) / κ by ring]
      rcases lt_trichotomy x (lowEnd S) with hx | hx | hx
      · rw [if_pos (div_neg_of_neg_of_pos (by linarith) hκ), hcdfL x hx]
      · rw [hx]
        simp [hcdf, hL]
      · rw [if_neg (not_lt.mpr (div_nonneg (by linarith) hκ.le)), hcdf, hS x hx]
    · right; right; left
      have hLp : 0 < lowEnd S - p := by linarith
      refine ⟨1 / κ, by positivity, 1 / (lowEnd S - p), by positivity,
        -lowEnd S / (lowEnd S - p), fun x => ?_⟩
      unfold GammaLaw
      rw [show 1 / (lowEnd S - p) * x + -lowEnd S / (lowEnd S - p) =
        (x - lowEnd S) / (lowEnd S - p) by ring]
      rcases lt_trichotomy x (lowEnd S) with hx | hx | hx
      · rw [if_pos (div_neg_of_neg_of_pos (by linarith) hLp), hcdfL x hx]
      · rw [hx]
        simp [hcdf, hL]
      · rw [if_neg (not_lt.mpr (div_nonneg (by linarith) hLp.le)), hcdf, hS x hx]
        have hr : 1 + (x - lowEnd S) / (lowEnd S - p) = (x - p) / (lowEnd S - p) := by
          field_simp
          ring
        have hrpos : 0 < (x - p) / (lowEnd S - p) := by rw [lt_div_iff₀ hLp]; linarith
        rw [hr, Real.rpow_def_of_pos hrpos]
        congr 2
        ring

end classify

end BdHLib

open MeasureTheory ProbabilityTheory Filter Topology BalkemaDeHaan.LimitTypes in
theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (hconv : WeakConv (fun t x => residualCDF μ t (b t + x * a t)) (cdf ν)) :
    IsResidualLimitType (cdf ν) := by
  have hlt1 := BdHLib.endpoint μ hF a b ha ν hν hconv
  exact BdHLib.classify ν (BdHLib.exists_mid ν hν) hlt1
    (fun y hyc hy0 => BdHLib.stability hF a b ha ν hν hconv hlt1 y hyc hy0)
