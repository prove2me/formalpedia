-- Prove2me | solution 1 for CachonCoord.TwoLocation.eq_35_37
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:02:35.100216+00:00
-- url     : https://prove2.me/submissions/4d2902c2-b45e-496b-8b9f-381de55d1b91

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

end Model


end CachonCoord.TwoLocation

open CachonCoord.TwoLocation


theorem solution (M : Model) :
    (∀ sr ss : ℝ, HasDerivAt (fun x => M.Pi x ss)
      (M.FS ss * M.cDeriv sr + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) sr) ∧
    (∀ sr ss : ℝ, HasDerivAt (fun y => M.Pi sr y)
      (M.FS ss * M.hs + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) ss) ∧
    (∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → 0 < ss →
      M.cDeriv sr = M.hs ∧ M.FR sr = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∃! s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∀ s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta) →
      ∃! s1s : ℝ, M.FS s1s * M.hs + ∫ x in Set.Ioi s1s, M.cDeriv (s1r + s1s - x) ∂M.lawS = 0) := by
  exact M.eq3537_core
