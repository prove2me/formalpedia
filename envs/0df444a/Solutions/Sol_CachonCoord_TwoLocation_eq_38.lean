-- Prove2me | solution 1 for CachonCoord.TwoLocation.eq_38
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:13:22.641818+00:00
-- url     : https://prove2.me/submissions/88f1d4f8-f997-4fbf-a944-4e0660542718

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Game
import Definitions.Def_CachonCoord_TwoLocation_Contracts

open MeasureTheory
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace CachonCoord.TwoLocation

section Gen

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma tl_singleton (hc : Continuous (cdf μ)) (a : ℝ) : μ {a} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  have : Function.leftLim (cdf μ) a = cdf μ a :=
    ((cdf μ).mono.continuousWithinAt_Iio_iff_leftLim_eq).1 hc.continuousAt.continuousWithinAt
  simp [this]

lemma tl_real_Iio (hc : Continuous (cdf μ)) (a : ℝ) : μ.real (Iio a) = cdf μ a := by
  rw [cdf_eq_real]
  have : NullSingletonClass μ := ⟨tl_singleton hc⟩
  exact measureReal_congr Iio_ae_eq_Iic

lemma tl_real_Ioi (a : ℝ) : μ.real (Ioi a) = 1 - cdf μ a := by
  rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma tl_cdf_nonpos (h0 : cdf μ 0 = 0) {u : ℝ} (hu : u ≤ 0) :
    cdf μ u = 0 :=
  le_antisymm (h0 ▸ monotone_cdf μ hu) (cdf_nonneg μ u)

lemma tl_cdf_lt (h0 : cdf μ 0 = 0) (hst : StrictMonoOn (cdf μ) (Ici 0)) {u v : ℝ}
    (huv : u < v) (hv : 0 < v) : cdf μ u < cdf μ v := by
  rcases le_or_gt 0 u with hu | hu
  · exact hst hu (le_of_lt (hu.trans_lt huv)) huv
  · calc cdf μ u ≤ cdf μ 0 := monotone_cdf μ hu.le
      _ < cdf μ v := hst (mem_Ici.2 (le_refl _)) (mem_Ici.2 hv.le) hv

lemma tl_cdf_lt_one (h0 : cdf μ 0 = 0) (hst : StrictMonoOn (cdf μ) (Ici 0)) (u : ℝ) :
    cdf μ u < 1 :=
  (tl_cdf_lt h0 hst (lt_add_one (max u 0)) (by positivity) |>.trans_le' (monotone_cdf μ
    (le_max_left u 0))).trans_le (cdf_le_one μ _)

lemma tl_meas_Ioo (h0 : cdf μ 0 = 0) (hst : StrictMonoOn (cdf μ) (Ici 0))
    (hc : Continuous (cdf μ)) {a b : ℝ} (hab : a < b) (hb : 0 < b) : μ (Ioo a b) ≠ 0 := by
  intro h
  have : NullSingletonClass μ := ⟨tl_singleton hc⟩
  have h2 : μ (Ioc a b) = 0 := by rw [measure_congr Ioo_ae_eq_Ioc.symm]; exact h
  rw [← measure_cdf μ, StieltjesFunction.measure_Ioc, ENNReal.ofReal_eq_zero] at h2
  have := tl_cdf_lt h0 hst hab hb
  linarith

/-- derivative under the integral sign, global Lipschitz version -/
lemma tl_hasDerivAt_int {ν : Measure ℝ} [IsFiniteMeasure ν] {F : ℝ → ℝ → ℝ} {F' : ℝ → ℝ}
    {s0 K : ℝ} (hFc : ∀ s, Continuous (F s)) (hF'm : AEStronglyMeasurable F' ν)
    (hint : Integrable (F s0) ν) (hlip : ∀ x s t, |F s x - F t x| ≤ K * |s - t|)
    (hd : ∀ᵐ x ∂ν, HasDerivAt (fun s => F s x) (F' x) s0) :
    Integrable F' ν ∧ HasDerivAt (fun s => ∫ x, F s x ∂ν) (∫ x, F' x ∂ν) s0 := by
  refine hasDerivAt_integral_of_dominated_loc_of_lip (s := univ) (bound := fun _ => K)
    univ_mem (Eventually.of_forall fun s => (hFc s).aestronglyMeasurable) hint hF'm
    (ae_of_all _ fun x => ?_) (integrable_const K) hd
  refine LipschitzOnWith.of_dist_le_mul fun s _ t _ => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs]
  exact (hlip x s t).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _))

lemma tl_int_lip {ν : Measure ℝ} [IsProbabilityMeasure ν] (hm : Integrable (id : ℝ → ℝ) ν)
    {g : ℝ → ℝ} (hgc : Continuous g) {K : ℝ} (hK : ∀ a b, |g a - g b| ≤ K * |a - b|)
    (sr ss : ℝ) : Integrable (fun x => g (sr - max (x - ss) 0)) ν := by
  refine Integrable.mono' (g := fun x => |g sr| + |K| * (|x| + |ss|))
    ((integrable_const _).add ((hm.abs.add (integrable_const _)).const_mul _))
    (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hK (sr - max (x - ss) 0) sr
  have h2 : |sr - max (x - ss) 0 - sr| ≤ |x| + |ss| := by
    rw [show sr - max (x - ss) 0 - sr = -max (x - ss) 0 by ring, abs_neg]
    rw [abs_le]; constructor
    · have := le_max_right (x - ss) 0; have := abs_nonneg x; have := abs_nonneg ss; linarith
    · rw [max_le_iff]; constructor
      · have := le_abs_self x; have := neg_abs_le ss; linarith
      · positivity
  have h3 : |g (sr - max (x - ss) 0)| ≤ |g sr| + |g (sr - max (x - ss) 0) - g sr| := by
    have := abs_sub_abs_le_abs_sub (g (sr - max (x - ss) 0)) (g sr); linarith
  have h4 : K * |sr - max (x - ss) 0 - sr| ≤ |K| * (|x| + |ss|) :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg K))
  linarith

lemma tl_lip_of_deriv {g g' : ℝ → ℝ} (hd : ∀ y, HasDerivAt g (g' y) y) {K : ℝ}
    (hb : ∀ y, |g' y| ≤ K) (a b : ℝ) : |g a - g b| ≤ K * |a - b| := by
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := K) (fun x _ => (hd x).hasDerivWithinAt) (fun x _ => hb x)
    (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

/-- `I(y) = E (y - D)^+` has derivative `F(y)`. -/
lemma tl_hasDerivAt_I (hc : Continuous (cdf μ)) (hm : Integrable (id : ℝ → ℝ) μ) (y : ℝ) :
    HasDerivAt (fun y => ∫ x, max (y - x) 0 ∂μ) (cdf μ y) y := by
  have key := tl_hasDerivAt_int (ν := μ) (F := fun s x => max (s - x) 0)
    (F' := (Iio y).indicator (fun _ => (1:ℝ))) (s0 := y) (K := 1) (fun s => by fun_prop)
    ((measurable_const.indicator measurableSet_Iio).aestronglyMeasurable)
    (by
      refine Integrable.mono' (g := fun x => |y| + |x|) ((integrable_const _).add hm.abs)
        (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
      constructor
      · have := le_abs_self y; have := neg_abs_le x; linarith
      · positivity)
    (fun x s t => by
      rw [one_mul]
      have := abs_max_sub_max_le_abs (s - x) (t - x) (0:ℝ)
      rwa [show s - x - (t - x) = s - t by ring] at this)
    (by
      have : ∀ᵐ x ∂μ, x ≠ y := by
        rw [ae_iff]; simpa using tl_singleton hc y
      filter_upwards [this] with x hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [indicator_of_mem (mem_Iio.2 h)]
        have : (fun s => max (s - x) 0) =ᶠ[𝓝 y] fun s => s - x := by
          filter_upwards [Ioi_mem_nhds h] with s hs
          exact max_eq_left (by simp at hs; linarith)
        exact ((hasDerivAt_id y).sub_const x).congr_of_eventuallyEq this
      · rw [indicator_of_notMem (by simp; linarith)]
        have : (fun s => max (s - x) 0) =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
          filter_upwards [Iio_mem_nhds h] with s hs
          exact max_eq_right (by simp at hs; linarith)
        exact (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq this)
  convert key.2 using 1
  rw [integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_one, tl_real_Iio hc]

/-- `B(y) = E (D - y)^+` has derivative `F(y) - 1`. -/
lemma tl_hasDerivAt_B (hc : Continuous (cdf μ)) (hm : Integrable (id : ℝ → ℝ) μ) (y : ℝ) :
    HasDerivAt (fun y => ∫ x, max (x - y) 0 ∂μ) (cdf μ y - 1) y := by
  have key := tl_hasDerivAt_int (ν := μ) (F := fun s x => max (x - s) 0)
    (F' := (Ioi y).indicator (fun _ => (-1:ℝ))) (s0 := y) (K := 1) (fun s => by fun_prop)
    ((measurable_const.indicator measurableSet_Ioi).aestronglyMeasurable)
    (by
      refine Integrable.mono' (g := fun x => |y| + |x|) ((integrable_const _).add hm.abs)
        (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
      constructor
      · have := le_abs_self x; have := neg_abs_le y; linarith
      · positivity)
    (fun x s t => by
      rw [one_mul]
      have := abs_max_sub_max_le_abs (x - s) (x - t) (0:ℝ)
      rwa [show x - s - (x - t) = -(s - t) by ring, abs_neg] at this)
    (by
      have : ∀ᵐ x ∂μ, x ≠ y := by
        rw [ae_iff]; simpa using tl_singleton hc y
      filter_upwards [this] with x hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [indicator_of_notMem (by simp; linarith)]
        have : (fun s => max (x - s) 0) =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
          filter_upwards [Ioi_mem_nhds h] with s hs
          exact max_eq_right (by simp at hs; linarith)
        exact (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq this
      · rw [indicator_of_mem (mem_Ioi.2 h)]
        have : (fun s => max (x - s) 0) =ᶠ[𝓝 y] fun s => x - s := by
          filter_upwards [Iio_mem_nhds h] with s hs
          exact max_eq_left (by simp at hs; linarith)
        exact ((hasDerivAt_id y).const_sub x).congr_of_eventuallyEq this)
  convert key.2 using 1
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, tl_real_Ioi]; ring

end Gen


section Gen2

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma tl_int_bdd {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ} (hc : Continuous f) {K : ℝ} (hb : ∀ x, |f x| ≤ K) :
    Integrable f ν :=
  Integrable.mono' (integrable_const K) hc.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

lemma tl_AR1 (hm : Integrable (id : ℝ → ℝ) ν) {g g' : ℝ → ℝ} (hd : ∀ y, HasDerivAt g (g' y) y)
    (hg'c : Continuous g') {K : ℝ} (hb : ∀ y, |g' y| ≤ K) (sr ss : ℝ) :
    HasDerivAt (fun s => ∫ x, g (s - max (x - ss) 0) ∂ν)
      (∫ x, g' (sr - max (x - ss) 0) ∂ν) sr := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hlip := tl_lip_of_deriv hd hb
  refine (tl_hasDerivAt_int (ν := ν) (F := fun s x => g (s - max (x - ss) 0))
    (F' := fun x => g' (sr - max (x - ss) 0)) (K := K) (fun s => by fun_prop)
    (by fun_prop : Continuous fun x => g' (sr - max (x - ss) 0)).aestronglyMeasurable
    (tl_int_lip hm hgc hlip sr ss) (fun x s t => ?_) (ae_of_all _ fun x => ?_)).2
  · have := hlip (s - max (x - ss) 0) (t - max (x - ss) 0)
    rwa [show s - max (x - ss) 0 - (t - max (x - ss) 0) = s - t by ring] at this
  · exact (hd (sr - max (x - ss) 0)).comp_sub_const sr (max (x - ss) 0)

lemma tl_AR2 (hm : Integrable (id : ℝ → ℝ) ν) {g g' : ℝ → ℝ} (hd : ∀ y, HasDerivAt g (g' y) y)
    (hg'c : Continuous g') {K : ℝ} (hb : ∀ y, |g' y| ≤ K) (sr ss : ℝ) (hat : ν {ss} = 0) :
    HasDerivAt (fun s => ∫ x, g (sr - max (x - s) 0) ∂ν)
      (∫ x in Ioi ss, g' (sr + ss - x) ∂ν) ss := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hlip := tl_lip_of_deriv hd hb
  have key := tl_hasDerivAt_int (ν := ν) (F := fun s x => g (sr - max (x - s) 0))
    (F' := (Ioi ss).indicator fun x => g' (sr + ss - x)) (K := K) (s0 := ss)
    (fun s => by fun_prop)
    (((by fun_prop : Continuous fun x => g' (sr + ss - x)).measurable.indicator
      measurableSet_Ioi).aestronglyMeasurable)
    (tl_int_lip hm hgc hlip sr ss) (fun x s t => ?_) ?_
  · rw [← integral_indicator measurableSet_Ioi]; exact key.2
  · have h1 := hlip (sr - max (x - s) 0) (sr - max (x - t) 0)
    have h2 := abs_max_sub_max_le_abs (x - t) (x - s) (0:ℝ)
    rw [show x - t - (x - s) = s - t by ring] at h2
    rw [show sr - max (x - s) 0 - (sr - max (x - t) 0) = max (x - t) 0 - max (x - s) 0 by ring]
      at h1
    have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)
  · have : ∀ᵐ x ∂ν, x ≠ ss := by
      rw [ae_iff]; simpa using hat
    filter_upwards [this] with x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [indicator_of_notMem (by simp; linarith)]
      have : (fun s => g (sr - max (x - s) 0)) =ᶠ[𝓝 ss] fun _ => g sr := by
        filter_upwards [Ioi_mem_nhds h] with s hs
        rw [max_eq_right (by simp at hs; linarith), sub_zero]
      exact (hasDerivAt_const ss (g sr)).congr_of_eventuallyEq this
    · rw [indicator_of_mem (mem_Ioi.2 h)]
      have : (fun s => g (sr - max (x - s) 0)) =ᶠ[𝓝 ss] fun s => g (s + (sr - x)) := by
        filter_upwards [Iio_mem_nhds h] with s hs
        rw [max_eq_left (by simp at hs; linarith)]; congr 1; ring
      have hd' := (hd (ss + (sr - x))).comp_add_const ss (sr - x)
      rw [show ss + (sr - x) = sr + ss - x by ring] at hd'
      exact hd'.congr_of_eventuallyEq this

lemma tl_split {g' : ℝ → ℝ} (hg'c : Continuous g') {K : ℝ} (hb : ∀ y, |g' y| ≤ K)
    (sr ss : ℝ) :
    ∫ x, g' (sr - max (x - ss) 0) ∂ν = cdf ν ss * g' sr + ∫ x in Ioi ss, g' (sr + ss - x) ∂ν := by
  have hi : Integrable (fun x => g' (sr - max (x - ss) 0)) ν :=
    tl_int_bdd (by fun_prop) (fun x => hb _)
  rw [← integral_add_compl (measurableSet_Iic (a := ss)) hi, compl_Iic]
  congr 1
  · rw [setIntegral_congr_fun measurableSet_Iic (g := fun _ => g' sr) (fun x hx => by
      simp only [mem_Iic] at hx; simp [max_eq_right (by linarith : x - ss ≤ 0)]),
      setIntegral_const, smul_eq_mul, cdf_eq_real]
  · exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      simp only [mem_Ioi] at hx; simp only [max_eq_left (by linarith : 0 ≤ x - ss)]
      congr 1; ring)

end Gen2

namespace Model

variable (M : Model)

instance instPR : IsProbabilityMeasure M.lawR := M.probR
instance instPS : IsProbabilityMeasure M.lawS := M.probS

lemma FR_cont : Continuous M.FR := M.cdfR_cont
lemma FS_cont : Continuous M.FS := M.cdfS_cont
lemma FR_lt {u v : ℝ} (h : u < v) (hv : 0 < v) : M.FR u < M.FR v :=
  tl_cdf_lt M.cdfR_zero M.cdfR_strict h hv
lemma FS_lt {u v : ℝ} (h : u < v) (hv : 0 < v) : M.FS u < M.FS v :=
  tl_cdf_lt M.cdfS_zero M.cdfS_strict h hv
lemma FR_nonpos {u : ℝ} (h : u ≤ 0) : M.FR u = 0 := tl_cdf_nonpos M.cdfR_zero h
lemma FS_nonpos {u : ℝ} (h : u ≤ 0) : M.FS u = 0 := tl_cdf_nonpos M.cdfS_zero h
lemma FR_lt_one (u : ℝ) : M.FR u < 1 := tl_cdf_lt_one M.cdfR_zero M.cdfR_strict u
lemma FS_lt_one (u : ℝ) : M.FS u < 1 := tl_cdf_lt_one M.cdfS_zero M.cdfS_strict u
lemma FR_nonneg (u : ℝ) : 0 ≤ M.FR u := cdf_nonneg _ _
lemma FS_nonneg (u : ℝ) : 0 ≤ M.FS u := cdf_nonneg _ _
lemma FR_pos {u : ℝ} (h : 0 < u) : 0 < M.FR u := by
  have := M.FR_lt h h; rwa [M.FR_nonpos le_rfl] at this
lemma FS_pos {u : ℝ} (h : 0 < u) : 0 < M.FS u := by
  have := M.FS_lt h h; rwa [M.FS_nonpos le_rfl] at this
lemma beta_pos : 0 < M.beta := by unfold beta; linarith [M.br_pos, M.bs_pos]
lemma hr_pos : 0 < M.hr := M.hs_pos.trans M.hs_lt_hr

/-- derivative of `c_r` -/
noncomputable def dR (y : ℝ) : ℝ := (M.hr + M.br) * M.FR y - M.br
/-- derivative of `c_s` -/
noncomputable def dS (y : ℝ) : ℝ := M.bs * (M.FR y - 1)

lemma hasDerivAt_IR (y : ℝ) : HasDerivAt M.IR (M.FR y) y :=
  tl_hasDerivAt_I M.cdfR_cont M.meanR y
lemma hasDerivAt_BR (y : ℝ) : HasDerivAt M.BR (M.FR y - 1) y :=
  tl_hasDerivAt_B M.cdfR_cont M.meanR y
lemma hasDerivAt_IS (y : ℝ) : HasDerivAt M.IS (M.FS y) y :=
  tl_hasDerivAt_I M.cdfS_cont M.meanS y

lemma hasDerivAt_cR (y : ℝ) : HasDerivAt M.cR (M.dR y) y := by
  have := ((M.hasDerivAt_IR y).const_mul M.hr).add ((M.hasDerivAt_BR y).const_mul M.br)
  exact this.congr_deriv (by unfold dR; ring)
lemma hasDerivAt_cS (y : ℝ) : HasDerivAt M.cS (M.dS y) y :=
  (M.hasDerivAt_BR y).const_mul M.bs
lemma hasDerivAt_c (y : ℝ) : HasDerivAt M.c (M.cDeriv y) y := by
  have := (M.hasDerivAt_cR y).add (M.hasDerivAt_cS y)
  exact this.congr_deriv (by unfold dR dS cDeriv beta; ring)

lemma dR_cont : Continuous M.dR := by unfold dR; have := M.FR_cont; fun_prop
lemma dS_cont : Continuous M.dS := by unfold dS; have := M.FR_cont; fun_prop
lemma cDeriv_cont : Continuous M.cDeriv := by unfold cDeriv; have := M.FR_cont; fun_prop

lemma dR_bd (y : ℝ) : |M.dR y| ≤ M.hr + M.br := by
  unfold dR; have := M.FR_nonneg y; have := (M.FR_lt_one y).le
  have := M.hr_pos; have := M.br_pos
  rw [abs_le]; constructor <;> nlinarith
lemma dS_bd (y : ℝ) : |M.dS y| ≤ M.bs := by
  unfold dS; have := M.FR_nonneg y; have := (M.FR_lt_one y).le; have := M.bs_pos
  rw [abs_le]; constructor <;> nlinarith
lemma cDeriv_bd (y : ℝ) : |M.cDeriv y| ≤ M.hr + M.beta := by
  unfold cDeriv; have := M.FR_nonneg y; have := (M.FR_lt_one y).le
  have := M.hr_pos; have := M.beta_pos
  rw [abs_le]; constructor <;> nlinarith

lemma cDeriv_eq (y : ℝ) : M.cDeriv y = M.dR y + M.dS y := by
  unfold cDeriv dR dS beta; ring

lemma S_atom (a : ℝ) : M.lawS {a} = 0 := tl_singleton M.cdfS_cont a

lemma hasDerivAt_cR2L (sr ss : ℝ) : HasDerivAt (fun x => M.cR2 x ss)
    (∫ x, M.dR (sr - max (x - ss) 0) ∂M.lawS) sr :=
  tl_AR1 M.meanS M.hasDerivAt_cR M.dR_cont M.dR_bd sr ss

lemma hasDerivAt_cS2L (sr ss : ℝ) : HasDerivAt (fun x => M.cS2 x ss)
    (∫ x, M.dS (sr - max (x - ss) 0) ∂M.lawS) sr :=
  tl_AR1 M.meanS M.hasDerivAt_cS M.dS_cont M.dS_bd sr ss

lemma hasDerivAt_cS2R (sr ss : ℝ) : HasDerivAt (fun y => M.cS2 sr y)
    (∫ x in Ioi ss, M.dS (sr + ss - x) ∂M.lawS) ss :=
  tl_AR2 M.meanS M.hasDerivAt_cS M.dS_cont M.dS_bd sr ss (M.S_atom ss)

lemma hasDerivAt_cR2R (sr ss : ℝ) : HasDerivAt (fun y => M.cR2 sr y)
    (∫ x in Ioi ss, M.dR (sr + ss - x) ∂M.lawS) ss :=
  tl_AR2 M.meanS M.hasDerivAt_cR M.dR_cont M.dR_bd sr ss (M.S_atom ss)

lemma hasDerivAt_c2L (sr ss : ℝ) : HasDerivAt (fun x => M.c2 x ss)
    (∫ x, M.cDeriv (sr - max (x - ss) 0) ∂M.lawS) sr := by
  have := (M.hasDerivAt_cR2L sr ss).add (M.hasDerivAt_cS2L sr ss)
  refine this.congr_deriv ?_
  rw [← integral_add (tl_int_bdd (by have := M.dR_cont; fun_prop) (fun x => M.dR_bd _))
    (tl_int_bdd (by have := M.dS_cont; fun_prop) (fun x => M.dS_bd _))]
  simp only [cDeriv_eq]

lemma hasDerivAt_c2R (sr ss : ℝ) : HasDerivAt (fun y => M.c2 sr y)
    (∫ x in Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) ss := by
  have := (M.hasDerivAt_cR2R sr ss).add (M.hasDerivAt_cS2R sr ss)
  refine this.congr_deriv ?_
  rw [← integral_add (tl_int_bdd (by have := M.dR_cont; fun_prop) (fun x => M.dR_bd _))
    (tl_int_bdd (by have := M.dS_cont; fun_prop) (fun x => M.dS_bd _))]
  simp only [cDeriv_eq]

lemma Pi_eq (sr ss : ℝ) : M.Pi sr ss = M.c2 sr ss + M.hs * M.IS ss := by
  unfold Pi piR piS c2; ring

lemma hasDerivAt_PiL (sr ss : ℝ) : HasDerivAt (fun x => M.Pi x ss)
    (M.FS ss * M.cDeriv sr + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) sr := by
  have := (M.hasDerivAt_c2L sr ss).add_const (M.hs * M.IS ss)
  simp only [← Pi_eq] at this
  rwa [tl_split M.cDeriv_cont M.cDeriv_bd] at this

lemma hasDerivAt_PiR (sr ss : ℝ) : HasDerivAt (fun y => M.Pi sr y)
    (M.FS ss * M.hs + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) ss := by
  have := (M.hasDerivAt_c2R sr ss).add ((M.hasDerivAt_IS ss).const_mul M.hs)
  rw [show (fun y => M.Pi sr y) = fun y => M.c2 sr y + M.hs * M.IS y from funext (M.Pi_eq sr)]
  exact this.congr_deriv (by ring)


lemma FR_abs (y : ℝ) : |M.FR y| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [M.FR_nonneg y, M.FR_lt_one y]
lemma FR_sub_abs (y : ℝ) : |M.FR y - 1| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [M.FR_nonneg y, M.FR_lt_one y]

lemma int_IR (sr ss : ℝ) : Integrable (fun x => M.IR (sr - max (x - ss) 0)) M.lawS :=
  tl_int_lip M.meanS (continuous_iff_continuousAt.2 fun y => (M.hasDerivAt_IR y).continuousAt)
    (tl_lip_of_deriv M.hasDerivAt_IR M.FR_abs) sr ss
lemma int_BR (sr ss : ℝ) : Integrable (fun x => M.BR (sr - max (x - ss) 0)) M.lawS :=
  tl_int_lip M.meanS (continuous_iff_continuousAt.2 fun y => (M.hasDerivAt_BR y).continuousAt)
    (tl_lip_of_deriv M.hasDerivAt_BR M.FR_sub_abs) sr ss

lemma cR2_eq (sr ss : ℝ) : M.cR2 sr ss = M.hr * M.IR2 sr ss + M.br * M.BR2 sr ss := by
  unfold cR2 IR2 BR2 atRetail cR
  rw [integral_add ((M.int_IR sr ss).const_mul _) ((M.int_BR sr ss).const_mul _),
    integral_const_mul, integral_const_mul]
lemma cS2_eq (sr ss : ℝ) : M.cS2 sr ss = M.bs * M.BR2 sr ss := by
  unfold cS2 BR2 atRetail cS
  rw [integral_const_mul]

theorem eq4243_core (lam ssOpt : ℝ) :
    ∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss) := by
  intro sr ss
  constructor
  · unfold czPiR contractedPiR transfer piR tI tBr c2
    rw [M.cR2_eq, M.cS2_eq]; unfold beta; ring
  · unfold czPiS contractedPiS transfer piS tI tBr c2 BS
    rw [M.cR2_eq, M.cS2_eq]; unfold beta; ring


lemma ae_S_nonneg : ∀ᵐ x ∂M.lawS, 0 ≤ x := by
  have := (measure_eq_zero_iff_ae_notMem).1 M.nonnegS
  filter_upwards [this] with x hx; simpa using hx

lemma cDeriv_mono {u v : ℝ} (h : u ≤ v) : M.cDeriv u ≤ M.cDeriv v := by
  unfold cDeriv
  have := monotone_cdf M.lawR h
  have := M.hr_pos; have := M.beta_pos
  unfold FR; nlinarith

lemma cDeriv_lt {u v : ℝ} (h : u < v) (hv : 0 < v) : M.cDeriv u < M.cDeriv v := by
  unfold cDeriv
  have := M.FR_lt h hv
  have := M.hr_pos; have := M.beta_pos
  nlinarith

lemma cDeriv_nonpos {u : ℝ} (h : u ≤ 0) : M.cDeriv u = -M.beta := by
  unfold cDeriv; rw [M.FR_nonpos h]; ring

lemma intc_neg {arg : ℝ → ℝ} (h : ∀ x, 0 ≤ x → arg x ≤ 0) :
    ∫ x, M.cDeriv (arg x) ∂M.lawS = -M.beta := by
  rw [integral_congr_ae (g := fun _ => -M.beta)]
  · simp
  · filter_upwards [M.ae_S_nonneg] with x hx
    exact M.cDeriv_nonpos (h x hx)

lemma tl_int_lt {ν : Measure ℝ} {f g : ℝ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (hle : ∀ x, f x ≤ g x) (hlt : ν {x | f x < g x} ≠ 0) : ∫ x, f x ∂ν < ∫ x, g x ∂ν := by
  have : 0 < ∫ x, (g x - f x) ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => sub_nonneg.2 (hle x))
      (hg.sub hf)]
    refine pos_iff_ne_zero.2 fun h0 => hlt (measure_mono_null (fun x hx => ?_) h0)
    simp only [mem_setOf_eq] at hx
    simp only [Function.mem_support]; linarith
  rw [integral_sub hg hf] at this; linarith

lemma int_cD (arg : ℝ → ℝ) (ha : Continuous arg) : Integrable (fun x => M.cDeriv (arg x)) M.lawS :=
  tl_int_bdd (by have := M.cDeriv_cont; fun_prop) (fun x => M.cDeriv_bd _)

lemma FR_inj {a b : ℝ} (h : M.FR a = M.FR b) (hp : 0 < M.FR a) : a = b := by
  have ha : 0 < a := by
    by_contra h'; push_neg at h'; rw [M.FR_nonpos h'] at hp; exact lt_irrefl _ hp
  have hb : 0 < b := by
    by_contra h'; push_neg at h'; rw [h, M.FR_nonpos h'] at hp; exact lt_irrefl _ hp
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact absurd h (ne_of_lt (M.FR_lt h1 hb))
  · exact h1
  · exact absurd h (ne_of_gt (M.FR_lt h1 ha))

lemma FR_surj {v : ℝ} (h0 : 0 < v) (h1 : v < 1) : ∃ a, M.FR a = v := by
  obtain ⟨t, ht, ht0⟩ := (((tendsto_cdf_atTop M.lawR).eventually (lt_mem_nhds h1)).and
    (eventually_ge_atTop 0)).exists
  have := intermediate_value_Icc ht0 M.FR_cont.continuousOn
  obtain ⟨a, -, ha⟩ := this ⟨by rw [M.FR_nonpos le_rfl]; exact h0.le, ht.le⟩
  exact ⟨a, ha⟩

/-- `G(r, s) = E c'(r - (D_s - s)^+)` -/
noncomputable def Gf (r s : ℝ) : ℝ := ∫ x, M.cDeriv (r - max (x - s) 0) ∂M.lawS

lemma Gf_cont_right (r : ℝ) : Continuous fun s => M.Gf r s := by
  unfold Gf
  refine continuous_of_dominated (bound := fun _ => M.hr + M.beta)
    (fun s => (by have := M.cDeriv_cont; fun_prop : Continuous fun x =>
      M.cDeriv (r - max (x - s) 0)).aestronglyMeasurable)
    (fun s => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact M.cDeriv_bd _)
    (integrable_const _) (ae_of_all _ fun x => by have := M.cDeriv_cont; fun_prop)

lemma Gf_cont_left (s : ℝ) : Continuous fun r => M.Gf r s := by
  unfold Gf
  refine continuous_of_dominated (bound := fun _ => M.hr + M.beta)
    (fun r => (by have := M.cDeriv_cont; fun_prop : Continuous fun x =>
      M.cDeriv (r - max (x - s) 0)).aestronglyMeasurable)
    (fun r => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact M.cDeriv_bd _)
    (integrable_const _) (ae_of_all _ fun x => by have := M.cDeriv_cont; fun_prop)

lemma Gf_split (r s : ℝ) : M.Gf r s =
    M.FS s * M.cDeriv r + ∫ x in Ioi s, M.cDeriv (r + s - x) ∂M.lawS :=
  tl_split M.cDeriv_cont M.cDeriv_bd r s

lemma Gf_mono {r r' s s' : ℝ} (hr : r ≤ r') (hs : s ≤ s') (x : ℝ) :
    M.cDeriv (r - max (x - s) 0) ≤ M.cDeriv (r' - max (x - s') 0) :=
  M.cDeriv_mono (by have := max_le_max (by linarith : x - s' ≤ x - s) (le_refl (0:ℝ)); linarith)

lemma Gf_tendsto (r : ℝ) : Tendsto (fun s => M.Gf r s) atTop (𝓝 (M.cDeriv r)) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := M.lawS) (l := atTop)
    (F := fun s x => M.cDeriv (r - max (x - s) 0)) (f := fun _ => M.cDeriv r)
    (fun _ => M.hr + M.beta)
    (Eventually.of_forall fun s => (by have := M.cDeriv_cont; fun_prop : Continuous fun x =>
      M.cDeriv (r - max (x - s) 0)).aestronglyMeasurable)
    (Eventually.of_forall fun s => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact M.cDeriv_bd _)
    (integrable_const _)
    (ae_of_all _ fun x => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop x] with s hs
      rw [max_eq_right (by linarith), sub_zero]))
  unfold Gf; simpa using this

lemma isMinOn_left {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (h : IsMinOn (fun p : ℝ × ℝ => f p.1 p.2) Set.univ (a, b)) :
    IsMinOn (fun x => f x b) Set.univ a := fun x _ => h (mem_univ (x, b))
lemma isMinOn_right {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (h : IsMinOn (fun p : ℝ × ℝ => f p.1 p.2) Set.univ (a, b)) :
    IsMinOn (fun y => f a y) Set.univ b := fun y _ => h (mem_univ (a, y))

lemma deriv_zero_of_min {f : ℝ → ℝ} {a f' : ℝ} (h : IsMinOn f Set.univ a)
    (hd : HasDerivAt f f' a) : f' = 0 :=
  (h.isLocalMin univ_mem).hasDerivAt_eq_zero hd

theorem eq3537_core :
    (∀ sr ss : ℝ, HasDerivAt (fun x => M.Pi x ss)
      (M.FS ss * M.cDeriv sr + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) sr) ∧
    (∀ sr ss : ℝ, HasDerivAt (fun y => M.Pi sr y)
      (M.FS ss * M.hs + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) ss) ∧
    (∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → 0 < ss →
      M.cDeriv sr = M.hs ∧ M.FR sr = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∃! s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∀ s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta) →
      ∃! s1s : ℝ, M.FS s1s * M.hs + ∫ x in Set.Ioi s1s, M.cDeriv (s1r + s1s - x) ∂M.lawS = 0) := by
  have hb := M.beta_pos; have hr := M.hr_pos; have hs := M.hs_pos; have hsr := M.hs_lt_hr
  have hv0 : 0 < (M.hs + M.beta) / (M.hr + M.beta) := by positivity
  have hv1 : (M.hs + M.beta) / (M.hr + M.beta) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hcd : ∀ r, M.FR r = (M.hs + M.beta) / (M.hr + M.beta) ↔ M.cDeriv r = M.hs := by
    intro r; unfold cDeriv
    rw [eq_div_iff (by positivity : M.hr + M.beta ≠ 0)]; constructor <;> intro h <;> linarith
  refine ⟨M.hasDerivAt_PiL, M.hasDerivAt_PiR, ?_, ?_, ?_⟩
  · intro sr ss hmin hss
    have h1 := deriv_zero_of_min (isMinOn_left hmin) (M.hasDerivAt_PiL sr ss)
    have h2 := deriv_zero_of_min (isMinOn_right hmin) (M.hasDerivAt_PiR sr ss)
    have hF := M.FS_pos hss
    have : M.FS ss * (M.cDeriv sr - M.hs) = 0 := by linarith
    have hc : M.cDeriv sr = M.hs := by
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    exact ⟨hc, (hcd sr).2 hc⟩
  · obtain ⟨a, ha⟩ := M.FR_surj hv0 hv1
    exact ⟨a, ha, fun b hb' => M.FR_inj (hb'.trans ha.symm) (by rw [hb']; exact hv0)⟩
  · intro r hr1
    have hc := (hcd r).1 hr1
    have hrpos : 0 < r := by
      by_contra h'; push_neg at h'; rw [M.FR_nonpos h'] at hr1; linarith
    have hG : ∀ s, M.FS s * M.hs + ∫ x in Set.Ioi s, M.cDeriv (r + s - x) ∂M.lawS = M.Gf r s := by
      intro s; rw [Gf_split, hc]
    simp only [hG]
    have hlow : ∀ u, u ≤ -r → M.Gf r u = -M.beta := by
      intro u hu; unfold Gf
      exact M.intc_neg fun x hx => by
        have := le_max_left (x - u) 0; linarith
    refine existsUnique_of_exists_of_unique ?_ ?_
    · obtain ⟨t, ht, ht0⟩ := (((M.Gf_tendsto r).eventually (lt_mem_nhds (hc ▸ hs))).and
        (eventually_ge_atTop (-r))).exists
      obtain ⟨a, -, ha⟩ := intermediate_value_Icc ht0 (M.Gf_cont_right r).continuousOn
        ⟨by rw [hlow _ le_rfl]; linarith, ht.le⟩
      exact ⟨a, ha⟩
    · have key : ∀ s s', s < s' → M.Gf r s = 0 → M.Gf r s' = 0 → False := by
        intro s s' hlt h1 h2
        rcases le_or_gt s' (-r) with h3 | h3
        · rw [hlow _ h3] at h2; linarith
        · have : M.Gf r s < M.Gf r s' := by
            unfold Gf
            refine tl_int_lt (M.int_cD _ (by fun_prop)) (M.int_cD _ (by fun_prop))
              (M.Gf_mono le_rfl hlt.le) ?_
            refine fun h0 => tl_meas_Ioo M.cdfS_zero M.cdfS_strict M.cdfS_cont
              (by linarith : s < r + s') (by linarith : 0 < r + s')
              (measure_mono_null (fun x hx => ?_) h0)
            simp only [mem_Ioo] at hx
            simp only [mem_setOf_eq]
            apply M.cDeriv_lt
            · rw [max_eq_left (by linarith : 0 ≤ x - s)]
              have := max_le (by linarith : x - s' ≤ x - s) (by linarith : (0:ℝ) ≤ x - s)
              rcases lt_or_ge s' x with h4 | h4
              · rw [max_eq_left (by linarith : 0 ≤ x - s')]; linarith
              · rw [max_eq_right (by linarith : x - s' ≤ 0)]; linarith
            · have : max (x - s') 0 < r := max_lt (by linarith) hrpos
              linarith
          linarith
      intro a b ha hb'
      rcases lt_trichotomy a b with h | h | h
      · exact (key a b h ha hb').elim
      · exact h
      · exact (key b a h hb' ha).elim


lemma Gf_pos_set {r s : ℝ} (h : M.Gf r s = 0) :
    M.lawS {x | 0 < r - max (x - s) 0} ≠ 0 := by
  intro h0
  have hae := (measure_eq_zero_iff_ae_notMem).1 h0
  have : M.Gf r s = -M.beta := by
    unfold Gf
    rw [integral_congr_ae (g := fun _ => -M.beta)]
    · simp
    · filter_upwards [hae] with x hx
      simp only [mem_setOf_eq, not_lt] at hx
      exact M.cDeriv_nonpos hx
  have := M.beta_pos; linarith

lemma Gf_strict {a a' b b' : ℝ} (ha : a < a') (hb : b ≤ b') (h : M.Gf a' b' = 0) :
    M.Gf a b < M.Gf a' b' := by
  unfold Gf
  refine tl_int_lt (M.int_cD _ (by fun_prop)) (M.int_cD _ (by fun_prop))
    (M.Gf_mono ha.le hb) ?_
  refine fun h0 => M.Gf_pos_set h (measure_mono_null (fun x hx => ?_) h0)
  simp only [mem_setOf_eq] at hx ⊢
  apply M.cDeriv_lt _ hx
  have := max_le_max (by linarith : x - b' ≤ x - b) (le_refl (0:ℝ)); linarith

lemma br_anti {a1 a2 b1 b2 : ℝ} (hb : b1 ≤ b2) (h1 : M.Gf a1 b1 = 0) (h2 : M.Gf a2 b2 = 0) :
    a2 ≤ a1 := by
  by_contra h; push_neg at h
  have := M.Gf_strict h hb h2; linarith

lemma br_unique {a1 a2 b : ℝ} (h1 : M.Gf a1 b = 0) (h2 : M.Gf a2 b = 0) : a1 = a2 :=
  le_antisymm (M.br_anti le_rfl h2 h1) (M.br_anti le_rfl h1 h2)

lemma czR_fun (lam ssOpt b : ℝ) : (fun x => M.czPiR lam ssOpt x b) =
    fun x => lam * M.c2 x b - M.tBs lam ssOpt * M.BS b :=
  funext fun x => (M.eq4243_core lam ssOpt x b).1

lemma czS_fun (lam ssOpt a : ℝ) : (fun y => M.czPiS lam ssOpt a y) =
    fun y => (M.hs + M.tBs lam ssOpt) * M.IS y + (1 - lam) * M.c2 a y
        + M.tBs lam ssOpt * (M.muS - y) :=
  funext fun y => (M.eq4243_core lam ssOpt a y).2

lemma czR_deriv (lam ssOpt a b : ℝ) :
    HasDerivAt (fun x => M.czPiR lam ssOpt x b) (lam * M.Gf a b) a := by
  rw [czR_fun]
  exact ((M.hasDerivAt_c2L a b).const_mul lam).sub_const _

lemma czR_min_Gf {lam ssOpt a b : ℝ} (hlam : 0 < lam)
    (h : IsMinOn (fun x => M.czPiR lam ssOpt x b) Set.univ a) : M.Gf a b = 0 := by
  have := deriv_zero_of_min h (M.czR_deriv lam ssOpt a b)
  rcases mul_eq_zero.1 this with h' | h'
  · linarith
  · exact h'

lemma czS_deriv {lam ssOpt a b : ℝ} (hG : M.Gf a b = 0) :
    HasDerivAt (fun y => M.czPiS lam ssOpt a y)
      (M.FS b * (M.hs - (1 - lam) * M.cDeriv a + M.tBs lam ssOpt) - M.tBs lam ssOpt) b := by
  rw [czS_fun]
  have h1 := (((M.hasDerivAt_IS b).const_mul (M.hs + M.tBs lam ssOpt)).add
    ((M.hasDerivAt_c2R a b).const_mul (1 - lam))).add
    (((hasDerivAt_id b).const_sub M.muS).const_mul (M.tBs lam ssOpt))
  rw [Gf_split] at hG
  refine h1.congr_deriv ?_
  have : ∫ x in Ioi b, M.cDeriv (a + b - x) ∂M.lawS = -(M.FS b * M.cDeriv a) := by linarith
  rw [this]; ring

theorem p84_core (lam ssOpt : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∀ b1 b2 a1 a2 : ℝ, b1 ≤ b2 →
      IsMinOn (fun x => M.czPiR lam ssOpt x b1) Set.univ a1 →
      IsMinOn (fun x => M.czPiR lam ssOpt x b2) Set.univ a2 → a2 ≤ a1) ∧
    (∀ a b : ℝ, IsMinOn (fun x => M.czPiR lam ssOpt x b) Set.univ a →
      HasDerivAt (fun y => M.czPiS lam ssOpt a y)
        (M.FS b * (M.hs - (1 - lam) * M.cDeriv a + M.tBs lam ssOpt) - M.tBs lam ssOpt) b) :=
  ⟨fun _ _ _ _ hb h1 h2 => M.br_anti hb (M.czR_min_Gf hlam0 h1) (M.czR_min_Gf hlam0 h2),
   fun _ _ h => M.czS_deriv (M.czR_min_Gf hlam0 h)⟩


lemma int_maxS (y : ℝ) : Integrable (fun x => max (y - x) 0) M.lawS := by
  refine Integrable.mono' (g := fun x => |y| + |x|) ((integrable_const _).add M.meanS.abs)
    (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
  constructor
  · have := le_abs_self y; have := neg_abs_le x; linarith
  · positivity

lemma IS_subgrad (y s0 : ℝ) : M.IS s0 + M.FS s0 * (y - s0) ≤ M.IS y := by
  have h : ∫ x, ((Iic s0).indicator (fun _ => y - s0) x + max (s0 - x) 0) ∂M.lawS ≤ M.IS y := by
    unfold IS
    refine integral_mono (((integrable_const _).indicator measurableSet_Iic).add (M.int_maxS s0))
      (M.int_maxS y) (fun x => ?_)
    by_cases hx : x ≤ s0
    · rw [indicator_of_mem (mem_Iic.2 hx)]
      rw [max_eq_left (by linarith : 0 ≤ s0 - x)]
      exact (le_max_left _ _).trans_eq' (by ring)
    · rw [indicator_of_notMem (show x ∉ Iic s0 by simpa using hx)]
      rw [max_eq_right (by push_neg at hx; linarith : s0 - x ≤ 0), add_zero]
      exact le_max_right _ _
  rw [integral_add ((integrable_const _).indicator measurableSet_Iic) (M.int_maxS s0),
    integral_indicator_const _ measurableSet_Iic, smul_eq_mul] at h
  unfold FS IS at *; rw [cdf_eq_real]; linarith

theorem goal_core (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (srOpt ssOpt : ℝ)
    (hopt : IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt))
    (hss : 0 < ssOpt) :
    (∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss)) ∧
    IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) srOpt ssOpt ∧
    (∀ sr ss : ℝ, IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) sr ss →
      sr = srOpt ∧ ss = ssOpt) := by
  have hs := M.hs_pos
  set F0 := M.FS ssOpt with hF0
  have hF0p : 0 < F0 := M.FS_pos hss
  have hF01 : F0 < 1 := M.FS_lt_one _
  have htB : M.tBs lam ssOpt = lam * M.hs * (F0 / (1 - F0)) := rfl
  have htBpos : 0 < M.tBs lam ssOpt := by
    rw [htB]; have : 0 < 1 - F0 := by linarith
    positivity
  have hkey : (lam * M.hs + M.tBs lam ssOpt) * F0 = M.tBs lam ssOpt := by
    rw [htB]; have : 1 - F0 ≠ 0 := by linarith
    field_simp; ring
  -- Nash at the optimum
  have hNash : IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) srOpt ssOpt := by
    constructor
    · intro x _
      have h1 := hopt (mem_univ (x, ssOpt))
      simp only [mem_setOf_eq, M.Pi_eq] at h1
      simp only [mem_setOf_eq, (M.eq4243_core lam ssOpt _ _).1]
      have : M.c2 srOpt ssOpt ≤ M.c2 x ssOpt := by linarith
      have := mul_le_mul_of_nonneg_left this hlam0.le
      linarith
    · intro y _
      have h1 := hopt (mem_univ (srOpt, y))
      simp only [mem_setOf_eq, M.Pi_eq] at h1
      simp only [mem_setOf_eq, (M.eq4243_core lam ssOpt _ _).2]
      have h2 := M.IS_subgrad y ssOpt
      rw [← hF0] at h2
      have h3 : 0 ≤ lam * M.hs + M.tBs lam ssOpt := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      have h5 : 0 ≤ 1 - lam := by linarith
      have h6 := mul_le_mul_of_nonneg_left h1 h5
      have h7 : (lam * M.hs + M.tBs lam ssOpt) * (M.IS ssOpt + F0 * (y - ssOpt)) =
          (lam * M.hs + M.tBs lam ssOpt) * M.IS ssOpt + M.tBs lam ssOpt * (y - ssOpt) := by
        linear_combination (y - ssOpt) * hkey
      linarith
  refine ⟨M.eq4243_core lam ssOpt, hNash, ?_⟩
  -- uniqueness
  have hp84 := M.p84_core lam ssOpt hlam0 hlam1
  have hEq : ∀ a b, IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) a b →
      M.Gf a b = 0 ∧
      M.FS b * (M.hs - (1 - lam) * M.cDeriv a + M.tBs lam ssOpt) - M.tBs lam ssOpt = 0 :=
    fun a b h => ⟨M.czR_min_Gf hlam0 h.1, deriv_zero_of_min h.2 (hp84.2 a b h.1)⟩
  have hcmp : ∀ a1 b1 a2 b2, IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) a1 b1 →
      IsNashMin (M.czPiR lam ssOpt) (M.czPiS lam ssOpt) a2 b2 → b1 < b2 → False := by
    intro a1 b1 a2 b2 h1 h2 hb
    obtain ⟨g1, e1⟩ := hEq a1 b1 h1
    obtain ⟨g2, e2⟩ := hEq a2 b2 h2
    have ha : a2 ≤ a1 := M.br_anti hb.le g1 g2
    have hc : M.cDeriv a2 ≤ M.cDeriv a1 := M.cDeriv_mono ha
    set B1 := M.hs - (1 - lam) * M.cDeriv a1 + M.tBs lam ssOpt
    set B2 := M.hs - (1 - lam) * M.cDeriv a2 + M.tBs lam ssOpt
    have hB : B1 ≤ B2 := by
      have : (1 - lam) * M.cDeriv a2 ≤ (1 - lam) * M.cDeriv a1 :=
        mul_le_mul_of_nonneg_left hc (by linarith)
      linarith
    have hFn := M.FS_nonneg b1
    have hF1 : 0 < M.FS b1 := by
      rcases hFn.lt_or_eq with h | h
      · exact h
      · rw [← h] at e1; linarith
    have hb1 : 0 < b1 := by
      by_contra h'; push_neg at h'; rw [M.FS_nonpos h'] at hF1; linarith
    have hF12 : M.FS b1 < M.FS b2 := M.FS_lt hb (hb1.trans hb)
    have hB1 : 0 < B1 := by
      by_contra h'; push_neg at h'
      have : M.FS b1 * B1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hFn h'
      linarith
    nlinarith
  intro sr ss hN
  have hss' : ss = ssOpt := by
    rcases lt_trichotomy ss ssOpt with h | h | h
    · exact (hcmp _ _ _ _ hN hNash h).elim
    · exact h
    · exact (hcmp _ _ _ _ hNash hN h).elim
  subst hss'
  exact ⟨M.br_unique (hEq _ _ hN).1 (hEq _ _ hNash).1, rfl⟩


lemma S_Ioi_ne (a : ℝ) : M.lawS (Ioi a) ≠ 0 := by
  intro h
  have h1 : M.lawS.real (Ioi a) = 0 := by simp [measureReal_def, h]
  rw [tl_real_Ioi] at h1
  have := M.FS_lt_one a; unfold FS at this; linarith

lemma R_Ioi_ne (a : ℝ) : M.lawR (Ioi a) ≠ 0 := by
  intro h
  have h1 : M.lawR.real (Ioi a) = 0 := by simp [measureReal_def, h]
  rw [tl_real_Ioi] at h1
  have := M.FR_lt_one a; unfold FR at this; linarith

lemma dR_mono {u v : ℝ} (h : u ≤ v) : M.dR u ≤ M.dR v := by
  unfold dR
  have := monotone_cdf M.lawR h
  have := M.hr_pos; have := M.br_pos
  unfold FR; nlinarith

lemma dR_lt {u v : ℝ} (h : u < v) (hv : 0 < v) : M.dR u < M.dR v := by
  unfold dR
  have := M.FR_lt h hv
  have := M.hr_pos; have := M.br_pos
  nlinarith

lemma dS_neg (u : ℝ) : M.dS u < 0 := by
  unfold dS; have := M.FR_lt_one u; have := M.bs_pos; nlinarith

lemma int_neg {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ} (hc : Continuous f) {K : ℝ}
    (hb : ∀ x, |f x| ≤ K) (hle : ∀ x, f x ≤ 0) (hlt : ν {x | f x < 0} ≠ 0) :
    ∫ x, f x ∂ν < 0 := by
  have := tl_int_lt (tl_int_bdd hc hb) (integrable_const (0:ℝ)) hle hlt
  simpa using this

theorem feas_core (shat : ℝ)
    (hshat : M.FR shat = M.br / (M.hr + M.br)) :
    0 < shat ∧
    (∀ ss sr : ℝ, IsMinOn (fun x => M.piR x ss) Set.univ sr → shat < sr) ∧
    (∀ sr ss : ℝ, IsMinOn (fun y => M.piS sr y) Set.univ ss → 0 < ss) := by
  have hr := M.hr_pos; have hbr := M.br_pos
  have hv : 0 < M.br / (M.hr + M.br) := by positivity
  have hshat0 : 0 < shat := by
    by_contra h; push_neg at h; rw [M.FR_nonpos h] at hshat; linarith
  have hdR : M.dR shat = 0 := by
    unfold dR; rw [hshat]; field_simp; ring
  refine ⟨hshat0, ?_, ?_⟩
  · intro ss sr hmin
    have h0 := deriv_zero_of_min hmin (M.hasDerivAt_cR2L sr ss)
    by_contra hle; push_neg at hle
    have hlt : ∫ x, M.dR (sr - max (x - ss) 0) ∂M.lawS < 0 := by
      refine int_neg (by have := M.dR_cont; fun_prop) (fun x => M.dR_bd _) (fun x => ?_) ?_
      · exact (M.dR_mono (by have := le_max_right (x - ss) 0; linarith)).trans
          ((M.dR_mono hle).trans_eq hdR)
      · rcases le_or_gt sr 0 with h1 | h1
        · refine fun h0' => (by simp : M.lawS univ ≠ 0) (measure_mono_null (fun x _ => ?_) h0')
          simp only [mem_setOf_eq]
          unfold dR; rw [M.FR_nonpos (by have := le_max_right (x - ss) 0; linarith)]
          linarith
        · refine fun h0' => M.S_Ioi_ne (max ss 0) (measure_mono_null (fun x hx => ?_) h0')
          simp only [mem_Ioi, max_lt_iff] at hx
          simp only [mem_setOf_eq]
          rw [max_eq_left (by linarith : 0 ≤ x - ss)]
          exact (M.dR_lt (by linarith) h1).trans_le ((M.dR_mono hle).trans_eq hdR)
    linarith
  · intro sr ss hmin
    have hd := ((M.hasDerivAt_IS ss).const_mul M.hs).add (M.hasDerivAt_cS2R sr ss)
    have h0 := deriv_zero_of_min hmin hd
    by_contra hle; push_neg at hle
    rw [M.FS_nonpos hle, mul_zero, zero_add] at h0
    have : ∫ x in Ioi ss, M.dS (sr + ss - x) ∂M.lawS < 0 := by
      refine int_neg (by have := M.dS_cont; fun_prop) (fun x => M.dS_bd _)
        (fun x => (M.dS_neg _).le) ?_
      have : {x | M.dS (sr + ss - x) < 0} = univ := by
        ext x; simp [M.dS_neg]
      rw [this, Measure.restrict_apply_univ]; exact M.S_Ioi_ne ss
    linarith

lemma BR_pos (y : ℝ) : 0 < M.BR y := by
  unfold BR
  have hint : Integrable (fun x => max (x - y) 0) M.lawR := by
    refine Integrable.mono' (g := fun x => |y| + |x|) ((integrable_const _).add M.meanR.abs)
      (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
    constructor
    · have := le_abs_self x; have := neg_abs_le y; linarith
    · positivity
  rw [integral_pos_iff_support_of_nonneg (f := fun x => max (x - y) 0)
    (fun x => le_max_right _ _) hint]
  have : Function.support (fun x => max (x - y) 0) = Ioi y := by
    ext x; simp only [Function.mem_support, mem_Ioi]
    constructor
    · intro h; by_contra h'; push_neg at h'; exact h (max_eq_right (by linarith))
    · intro h; rw [max_eq_left (by linarith)]; linarith
  rw [this]; exact pos_iff_ne_zero.2 (M.R_Ioi_ne y)

lemma IR_nonneg (y : ℝ) : 0 ≤ M.IR y := integral_nonneg fun _ => le_max_right _ _
lemma IS_nonneg (y : ℝ) : 0 ≤ M.IS y := integral_nonneg fun _ => le_max_right _ _

lemma cR_pos (y : ℝ) : 0 < M.cR y := by
  unfold cR
  have := M.BR_pos y; have := M.IR_nonneg y; have := M.hr_pos; have := M.br_pos
  positivity

lemma Pi_pos (sr ss : ℝ) : 0 < M.Pi sr ss := by
  have h1 : 0 < M.cR2 sr ss := by
    unfold cR2 atRetail
    rw [integral_pos_iff_support_of_nonneg (fun x => (M.cR_pos _).le)
      (tl_int_lip M.meanS (continuous_iff_continuousAt.2 fun y => (M.hasDerivAt_cR y).continuousAt)
        (tl_lip_of_deriv M.hasDerivAt_cR M.dR_bd) sr ss)]
    have : Function.support (fun x => M.cR (sr - max (x - ss) 0)) = univ := by
      ext x; simp [(M.cR_pos _).ne']
    rw [this]; simp
  have h2 : 0 ≤ M.cS2 sr ss := by
    unfold cS2 atRetail cS
    exact integral_nonneg fun x => mul_nonneg M.bs_pos.le (M.BR_pos _).le
  have h3 := M.IS_nonneg ss
  unfold Pi piR piS; have := M.hs_pos; positivity

lemma c2_min_Gf {a b : ℝ} (h : IsMinOn (fun x => M.c2 x b) Set.univ a) : M.Gf a b = 0 :=
  deriv_zero_of_min h (M.hasDerivAt_c2L a b)

lemma Pi_min_c2 {a b : ℝ} (h : IsMinOn (fun x => M.Pi x b) Set.univ a) :
    IsMinOn (fun x => M.c2 x b) Set.univ a := by
  intro x _
  have := h (mem_univ x)
  simp only [mem_setOf_eq, M.Pi_eq] at this ⊢; linarith

lemma comp1 {ss a b : ℝ} (ha : IsMinOn (fun x => M.cR2 x ss) Set.univ a)
    (hb : IsMinOn (fun x => M.c2 x ss) Set.univ b) : a < b := by
  have h1 := deriv_zero_of_min ha (M.hasDerivAt_cR2L a ss)
  have h2 := M.c2_min_Gf hb
  by_contra hle; push_neg at hle
  have h3 : M.Gf b ss ≤ M.Gf a ss := by
    unfold Gf
    exact integral_mono (M.int_cD _ (by fun_prop)) (M.int_cD _ (by fun_prop))
      (fun x => M.Gf_mono hle le_rfl x)
  have h4 : M.Gf a ss = ∫ x, M.dR (a - max (x - ss) 0) ∂M.lawS +
      ∫ x, M.dS (a - max (x - ss) 0) ∂M.lawS := by
    unfold Gf
    rw [← integral_add (tl_int_bdd (by have := M.dR_cont; fun_prop) (fun x => M.dR_bd _))
      (tl_int_bdd (by have := M.dS_cont; fun_prop) (fun x => M.dS_bd _))]
    simp only [cDeriv_eq]
  have h5 : ∫ x, M.dS (a - max (x - ss) 0) ∂M.lawS < 0 := by
    refine int_neg (by have := M.dS_cont; fun_prop) (fun x => M.dS_bd _)
      (fun x => (M.dS_neg _).le) ?_
    have : {x | M.dS (a - max (x - ss) 0) < 0} = univ := by
      ext x; simp [M.dS_neg]
    rw [this]; simp
  linarith

theorem pen_core :
    (∀ ss a b : ℝ, IsMinOn (fun x => M.cR2 x ss) Set.univ a →
      IsMinOn (fun x => M.c2 x ss) Set.univ b → a < b) ∧
    (∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ a : ℝ, IsMinOn (fun x => M.piR x ssOpt) Set.univ a → a < srOpt) ∧
    (∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ srN ssN : ℝ, IsNashMin M.piR M.piS srN ssN →
        0 < (M.Pi srN ssN - M.Pi srOpt ssOpt) / M.Pi srOpt ssOpt) := by
  have h2 : ∀ srOpt ssOpt : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srOpt, ssOpt) →
      ∀ a : ℝ, IsMinOn (fun x => M.piR x ssOpt) Set.univ a → a < srOpt :=
    fun srOpt ssOpt hopt a ha => M.comp1 ha (M.Pi_min_c2 (isMinOn_left hopt))
  refine ⟨fun ss a b ha hb => M.comp1 ha hb, h2, ?_⟩
  intro srOpt ssOpt hopt srN ssN hN
  have hle : M.Pi srOpt ssOpt ≤ M.Pi srN ssN := hopt (mem_univ (srN, ssN))
  have hlt : M.Pi srOpt ssOpt < M.Pi srN ssN := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have hopt' : IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (srN, ssN) := by
      intro p _
      have := hopt (mem_univ p)
      simp only [mem_setOf_eq] at this ⊢; linarith
    exact lt_irrefl _ (h2 srN ssN hopt' srN hN.1)
  exact div_pos (by linarith) (M.Pi_pos _ _)


lemma H_eq (t ss : ℝ) (hss : ss ≤ 0) :
    ∫ x, M.cDeriv (t - x) ∂M.lawS = M.Gf (t - ss) ss := by
  unfold Gf
  refine integral_congr_ae ?_
  filter_upwards [M.ae_S_nonneg] with x hx
  rw [max_eq_left (by linarith : 0 ≤ x - ss)]; congr 1; ring

lemma Gf_tendsto_left (s : ℝ) : Tendsto (fun r => M.Gf r s) atTop (𝓝 M.hr) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := M.lawS) (l := atTop)
    (F := fun r x => M.cDeriv (r - max (x - s) 0)) (f := fun _ => M.hr)
    (fun _ => M.hr + M.beta)
    (Eventually.of_forall fun r => (by have := M.cDeriv_cont; fun_prop : Continuous fun x =>
      M.cDeriv (r - max (x - s) 0)).aestronglyMeasurable)
    (Eventually.of_forall fun r => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact M.cDeriv_bd _)
    (integrable_const _)
    (ae_of_all _ fun x => by
      have h1 : Tendsto (fun r => M.FR (r - max (x - s) 0)) atTop (𝓝 1) :=
        (tendsto_cdf_atTop M.lawR).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
      have h2 := (h1.const_mul (M.hr + M.beta)).sub_const M.beta
      simp only [mul_one, add_sub_cancel_right] at h2
      exact h2)
  unfold Gf; simpa using this

lemma conv_eq (s : ℝ) :
    (M.lawR.conv M.lawS).real (Set.Iic s) = ∫ x, M.FR (s - x) ∂M.lawS := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ s} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : (M.lawR.conv M.lawS) (Set.Iic s) = ∫⁻ y, M.lawR (Iic (s - y)) ∂M.lawS := by
    rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rw [show (fun x : ℝ × ℝ => x.1 + x.2) ⁻¹' Iic s = {p : ℝ × ℝ | p.1 + p.2 ≤ s} from rfl,
      Measure.prod_apply_symm hm]
    congr 1; funext y; congr 1; ext x; simp [le_sub_iff_add_le]
  have h2 : ∫⁻ y, M.lawR (Iic (s - y)) ∂M.lawS =
      ∫⁻ y, ENNReal.ofReal (M.FR (s - y)) ∂M.lawS := by
    congr 1; funext y; unfold FR; rw [ofReal_cdf]
  have hint : Integrable (fun y => M.FR (s - y)) M.lawS :=
    tl_int_bdd (by have := M.FR_cont; fun_prop) (fun y => M.FR_abs _)
  rw [measureReal_def, h1, h2, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun y => M.FR_nonneg _), ENNReal.toReal_ofReal
    (integral_nonneg fun y => M.FR_nonneg _)]

theorem eq38_core :
    (∃! sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0) ∧
    (∀ s : ℝ, ∫ x, M.cDeriv (s - x) ∂M.lawS = 0 ↔
      (M.lawR.conv M.lawS).real (Set.Iic s) = M.beta / (M.hr + M.beta)) ∧
    (∀ sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0 →
      ∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → ss ≤ 0 →
        sr + ss = sbar) := by
  have hb := M.beta_pos; have hr := M.hr_pos
  have hH : ∀ t, ∫ x, M.cDeriv (t - x) ∂M.lawS = M.Gf t 0 := by
    intro t; rw [M.H_eq t 0 le_rfl, sub_zero]
  simp only [hH]
  refine ⟨?_, ?_, ?_⟩
  · refine existsUnique_of_exists_of_unique ?_ (fun a b ha hb' => M.br_unique ha hb')
    have h0 : M.Gf 0 0 = -M.beta := by
      unfold Gf
      exact M.intc_neg fun x hx => by have := le_max_left (x - 0) 0; linarith
    obtain ⟨t, ht, ht0⟩ := (((M.Gf_tendsto_left 0).eventually (lt_mem_nhds hr)).and
      (eventually_ge_atTop 0)).exists
    obtain ⟨a, -, ha⟩ := intermediate_value_Icc ht0 (M.Gf_cont_left 0).continuousOn
      ⟨by rw [h0]; linarith, ht.le⟩
    exact ⟨a, ha⟩
  · intro s
    rw [M.conv_eq, ← hH]
    have : ∫ x, M.cDeriv (s - x) ∂M.lawS = (M.hr + M.beta) * ∫ x, M.FR (s - x) ∂M.lawS - M.beta := by
      unfold cDeriv
      rw [integral_sub ((tl_int_bdd (by have := M.FR_cont; fun_prop)
        (fun y => M.FR_abs _)).const_mul _) (integrable_const _), integral_const_mul]
      simp
    rw [this, eq_div_iff (by positivity : M.hr + M.beta ≠ 0)]
    constructor <;> intro h <;> linarith
  · intro sbar hsbar sr ss hmin hss
    have h1 := M.c2_min_Gf (M.Pi_min_c2 (isMinOn_left hmin))
    have h2 : M.Gf (sr + ss) 0 = 0 := by
      rw [← hH, M.H_eq (sr + ss) ss hss, add_sub_cancel_right]; exact h1
    exact M.br_unique h2 hsbar

end Model


end CachonCoord.TwoLocation

open CachonCoord.TwoLocation


theorem solution (M : Model) :
    (∃! sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0) ∧
    (∀ s : ℝ, ∫ x, M.cDeriv (s - x) ∂M.lawS = 0 ↔
      (M.lawR.conv M.lawS).real (Set.Iic s) = M.beta / (M.hr + M.beta)) ∧
    (∀ sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0 →
      ∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → ss ≤ 0 →
        sr + ss = sbar) := by
  exact M.eq38_core
