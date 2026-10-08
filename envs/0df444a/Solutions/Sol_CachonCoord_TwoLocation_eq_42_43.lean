-- Prove2me | solution 1 for CachonCoord.TwoLocation.eq_42_43
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T05:59:39.07347+00:00
-- url     : https://prove2.me/submissions/8739e088-6a4d-4512-8fbf-0f456072cb0c

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model
import Definitions.Def_CachonCoord_TwoLocation_Game
import Definitions.Def_CachonCoord_TwoLocation_Contracts

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

end Model


end CachonCoord.TwoLocation

open CachonCoord.TwoLocation


theorem solution (M : Model) (lam ssOpt : ℝ) :
    ∀ sr ss : ℝ,
      M.czPiR lam ssOpt sr ss = lam * M.c2 sr ss - M.tBs lam ssOpt * M.BS ss ∧
      M.czPiS lam ssOpt sr ss = (M.hs + M.tBs lam ssOpt) * M.IS ss + (1 - lam) * M.c2 sr ss
        + M.tBs lam ssOpt * (M.muS - ss) := by
  exact M.eq4243_core lam ssOpt
