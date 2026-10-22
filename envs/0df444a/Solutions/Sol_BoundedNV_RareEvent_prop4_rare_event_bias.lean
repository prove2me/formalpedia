-- Prove2me | solution 1 for BoundedNV.RareEvent.prop4_rare_event_bias
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:14:00.609584+00:00
-- url     : https://prove2.me/submissions/6f203441-55ff-4c7e-88d5-2f400726b02f

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit

set_option autoImplicit false

open MeasureTheory Filter Topology

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_minf_int (f : ℝ → ℝ) (hf : IsDemandDensity f) (v : ℝ) :
    Integrable (fun t => min t v * f t) := by
  refine Integrable.mono' (hf.integrable.norm.const_mul |v|) ?_ ?_
  · exact ((continuous_id.min continuous_const).aestronglyMeasurable).mul
      hf.integrable.aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    rcases lt_or_ge t 0 with ht | ht
    · rw [hf.zero_of_neg t ht]; simp
    · have habs : |min t v| ≤ |v| := by
        rw [abs_le]; constructor
        · rcases le_total t v with h | h
          · rw [min_eq_left h]; linarith [abs_nonneg v]
          · rw [min_eq_right h]; exact neg_abs_le v
        · exact (min_le_right t v).trans (le_abs_self v)
      exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_up (f : ℝ → ℝ) (hf : IsDemandDensity f) (m t : ℝ) (ht : 0 ≤ t) :
    expMin f (m + t) - expMin f m =
      t * (∫ u in Set.Ioi m, f u) - ∫ u in Set.Ioo m (m + t), (m + t - u) * f u := by
  have hpt : (fun u => min u (m + t) * f u - min u m * f u) =
      fun u => t * (Set.Ioi m).indicator f u
        - (Set.Ioo m (m + t)).indicator (fun u => (m + t - u) * f u) u := by
    funext u
    rcases le_or_gt u m with h1 | h1
    · rw [min_eq_left h1, min_eq_left (by linarith : u ≤ m + t),
        Set.indicator_of_notMem (show u ∉ Set.Ioi m from fun h => absurd h (not_lt.mpr h1)),
        Set.indicator_of_notMem (show u ∉ Set.Ioo m (m + t) from fun h => absurd h.1 (not_lt.mpr h1))]
      ring
    · rcases lt_or_ge u (m + t) with h2 | h2
      · rw [min_eq_left h2.le, min_eq_right h1.le,
          Set.indicator_of_mem (show u ∈ Set.Ioi m from h1),
          Set.indicator_of_mem (show u ∈ Set.Ioo m (m + t) from ⟨h1, h2⟩)]
        ring
      · rw [min_eq_right h2, min_eq_right h1.le,
          Set.indicator_of_mem (show u ∈ Set.Ioi m from h1),
          Set.indicator_of_notMem (show u ∉ Set.Ioo m (m + t) from fun h => absurd h.2 (not_lt.mpr h2))]
        ring
  have hI2 : Integrable ((Set.Ioo m (m + t)).indicator (fun u => (m + t - u) * f u)) := by
    refine Integrable.mono' (hf.integrable.const_mul t) ?_ ?_
    · exact (((continuous_const.sub continuous_id).aestronglyMeasurable.mul
        hf.integrable.aestronglyMeasurable)).indicator measurableSet_Ioo
    · refine Eventually.of_forall (fun u => ?_)
      by_cases h : u ∈ Set.Ioo m (m + t)
      · rw [Set.indicator_of_mem h, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith [h.2]) (hf.nonneg u))]
        exact mul_le_mul_of_nonneg_right (by linarith [h.1]) (hf.nonneg u)
      · rw [Set.indicator_of_notMem h, norm_zero]; exact mul_nonneg ht (hf.nonneg u)
  unfold expMin
  rw [← integral_sub (bnv2d_minf_int f hf _) (bnv2d_minf_int f hf _), hpt,
    integral_sub ((hf.integrable.indicator measurableSet_Ioi).const_mul t) hI2,
    integral_const_mul, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioo]

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_down (f : ℝ → ℝ) (hf : IsDemandDensity f) (m t : ℝ) (ht : 0 ≤ t) :
    expMin f m - expMin f (m - t) =
      t * (∫ u in Set.Ioi m, f u) + ∫ u in Set.Ioc (m - t) m, (u - m + t) * f u := by
  have hpt : (fun u => min u m * f u - min u (m - t) * f u) =
      fun u => t * (Set.Ioi m).indicator f u
        + (Set.Ioc (m - t) m).indicator (fun u => (u - m + t) * f u) u := by
    funext u
    rcases le_or_gt u (m - t) with h1 | h1
    · rw [min_eq_left h1, min_eq_left (by linarith : u ≤ m),
        Set.indicator_of_notMem (show u ∉ Set.Ioi m from fun h => by
          have : m < u := h; linarith),
        Set.indicator_of_notMem (show u ∉ Set.Ioc (m - t) m from fun h => absurd h.1 (not_lt.mpr h1))]
      ring
    · rcases le_or_gt u m with h2 | h2
      · rw [min_eq_left h2, min_eq_right h1.le,
          Set.indicator_of_notMem (show u ∉ Set.Ioi m from fun h => absurd h (not_lt.mpr h2)),
          Set.indicator_of_mem (show u ∈ Set.Ioc (m - t) m from ⟨h1, h2⟩)]
        ring
      · rw [min_eq_right h2.le, min_eq_right h1.le,
          Set.indicator_of_mem (show u ∈ Set.Ioi m from h2),
          Set.indicator_of_notMem (show u ∉ Set.Ioc (m - t) m from fun h => absurd h.2 (not_le.mpr h2))]
        ring
  have hI2 : Integrable ((Set.Ioc (m - t) m).indicator (fun u => (u - m + t) * f u)) := by
    refine Integrable.mono' (hf.integrable.const_mul t) ?_ ?_
    · exact (((continuous_id.sub continuous_const).add continuous_const).aestronglyMeasurable.mul
        hf.integrable.aestronglyMeasurable).indicator measurableSet_Ioc
    · refine Eventually.of_forall (fun u => ?_)
      by_cases h : u ∈ Set.Ioc (m - t) m
      · rw [Set.indicator_of_mem h, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith [h.1]) (hf.nonneg u))]
        exact mul_le_mul_of_nonneg_right (by linarith [h.2]) (hf.nonneg u)
      · rw [Set.indicator_of_notMem h, norm_zero]; exact mul_nonneg ht (hf.nonneg u)
  unfold expMin
  rw [← integral_sub (bnv2d_minf_int f hf _) (bnv2d_minf_int f hf _), hpt,
    integral_add ((hf.integrable.indicator measurableSet_Ioi).const_mul t) hI2,
    integral_const_mul, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioc]

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_bound (f : ℝ → ℝ) (hf : IsDemandDensity f) (M : ℝ) (hM : ∀ x, f x ≤ M)
    (g : ℝ → ℝ) (hg : Continuous g) (s : Set ℝ) (hs : MeasurableSet s) (t : ℝ) (ht : 0 ≤ t)
    (hgs : ∀ u ∈ s, 0 ≤ g u ∧ g u ≤ t) (hvol : volume s = ENNReal.ofReal t) :
    ∫ u in s, g u * f u ≤ t * (t * M) := by
  have hfin : volume s ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn (fun u => g u * f u) s := by
    refine Integrable.mono' (hf.integrable.integrableOn.const_mul t) ?_ ?_
    · exact (hg.aestronglyMeasurable.mul hf.integrable.aestronglyMeasurable).restrict
    · refine ae_restrict_of_forall_mem hs (fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgs u hu).1 (hf.nonneg u))]
      exact mul_le_mul_of_nonneg_right (hgs u hu).2 (hf.nonneg u)
  calc ∫ u in s, g u * f u ≤ ∫ u in s, t * M :=
        setIntegral_mono_on hint (integrableOn_const hfin) hs
          (fun u hu => mul_le_mul (hgs u hu).2 (hM u) (hf.nonneg u) ht)
    _ = t * (t * M) := by
        rw [setIntegral_const, Measure.real, hvol, ENNReal.toReal_ofReal ht, smul_eq_mul]

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_kappa (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c m M : ℝ) (hp : 0 < p)
    (hM : ∀ x, f x ≤ M) (hm : IsMaxOn (nvProfit f p c) Set.univ m) :
    p * (∫ u in Set.Ioi m, f u) - c = 0 := by
  have hM0 : 0 ≤ M := (hf.nonneg 0).trans (hM 0)
  have hPM : 0 ≤ p * M := mul_nonneg hp.le hM0
  have key : ∀ t > 0, p * (∫ u in Set.Ioi m, f u) - c ≤ p * M * t := by
    intro t ht
    have h1 : nvProfit f p c (m + t) ≤ nvProfit f p c m := hm (Set.mem_univ _)
    have hu := bnv2d_up f hf m t ht.le
    have hb := bnv2d_bound f hf M hM (fun u => m + t - u) (continuous_const.sub continuous_id)
      (Set.Ioo m (m + t)) measurableSet_Ioo t ht.le
      (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      (by rw [Real.volume_Ioo]; congr 1; ring)
    unfold nvProfit at h1
    have h2 : t * (p * (∫ u in Set.Ioi m, f u) - c) ≤ t * (p * M * t) := by nlinarith
    exact le_of_mul_le_mul_left h2 ht
  have key2 : ∀ t > 0, -(p * (∫ u in Set.Ioi m, f u) - c) ≤ p * M * t := by
    intro t ht
    have h1 : nvProfit f p c (m - t) ≤ nvProfit f p c m := hm (Set.mem_univ _)
    have hd := bnv2d_down f hf m t ht.le
    have hb := bnv2d_bound f hf M hM (fun u => u - m + t)
      ((continuous_id.sub continuous_const).add continuous_const)
      (Set.Ioc (m - t) m) measurableSet_Ioc t ht.le
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (by rw [Real.volume_Ioc]; congr 1; ring)
    unfold nvProfit at h1
    have h2 : t * (-(p * (∫ u in Set.Ioi m, f u) - c)) ≤ t * (p * M * t) := by nlinarith
    exact le_of_mul_le_mul_left h2 ht
  set κ := p * (∫ u in Set.Ioi m, f u) - c with hκ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have ht : 0 < -κ / (p * M + 1) := div_pos (by linarith) (by linarith)
    have h := key2 _ ht
    rw [mul_div_assoc', le_div_iff₀ (by linarith)] at h
    nlinarith
  · have ht : 0 < κ / (p * M + 1) := div_pos hpos (by linarith)
    have h := key _ ht
    rw [mul_div_assoc', le_div_iff₀ (by linarith)] at h
    nlinarith

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_iip (f : ℝ → ℝ) (hf : IsDemandDensity f) (m t : ℝ) :
    IntervalIntegrable (fun v => (t - v) * f (m + v)) volume 0 t :=
  (hf.integrable.comp_add_left m).intervalIntegrable.continuousOn_mul
    (continuous_const.sub continuous_id).continuousOn

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_iim (f : ℝ → ℝ) (hf : IsDemandDensity f) (m t : ℝ) :
    IntervalIntegrable (fun v => (t - v) * f (m - v)) volume 0 t :=
  (hf.integrable.comp_sub_left m).intervalIntegrable.continuousOn_mul
    (continuous_const.sub continuous_id).continuousOn

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_phi (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c m t : ℝ) (ht : 0 ≤ t)
    (hκ : p * (∫ u in Set.Ioi m, f u) - c = 0) :
    nvProfit f p c (m + t) - nvProfit f p c (m - t) =
      p * ∫ v in (0:ℝ)..t, (t - v) * (f (m - v) - f (m + v)) := by
  have hu := bnv2d_up f hf m t ht
  have hd := bnv2d_down f hf m t ht
  have hP : ∫ u in Set.Ioo m (m + t), (m + t - u) * f u = ∫ v in (0:ℝ)..t, (t - v) * f (m + v) := by
    have e := intervalIntegral.integral_comp_add_left (fun x => (m + t - x) * f x) m (a := 0) (b := t)
    rw [add_zero] at e
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), ← e]
    congr 1; funext v; congr 1; ring
  have hN : ∫ u in Set.Ioc (m - t) m, (u - m + t) * f u = ∫ v in (0:ℝ)..t, (t - v) * f (m - v) := by
    have e := intervalIntegral.integral_comp_sub_left (fun x => (x - m + t) * f x) m (a := 0) (b := t)
    rw [sub_zero] at e
    rw [← intervalIntegral.integral_of_le (by linarith), ← e]
    congr 1; funext v; congr 1; ring
  have hsplit : ∫ v in (0:ℝ)..t, (t - v) * (f (m - v) - f (m + v)) =
      (∫ v in (0:ℝ)..t, (t - v) * f (m - v)) - ∫ v in (0:ℝ)..t, (t - v) * f (m + v) := by
    rw [← intervalIntegral.integral_sub (bnv2d_iim f hf m t) (bnv2d_iip f hf m t)]
    congr 1; funext v; ring
  rw [hsplit, ← hP, ← hN]
  unfold nvProfit
  linear_combination p * hu + p * hd + 2 * t * hκ

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_D_pos (f : ℝ → ℝ) (hf : IsDemandDensity f) (m t : ℝ) (ht : 0 < t)
    (h : ∀ v ∈ Set.Ioo 0 t, f (m + v) < f (m - v)) :
    0 < ∫ v in (0:ℝ)..t, (t - v) * (f (m - v) - f (m + v)) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_
    (fun v hv => mul_pos (by linarith [hv.2]) (by linarith [h v hv])) ht
  exact ((hf.integrable.comp_sub_left m).sub (hf.integrable.comp_add_left m)).intervalIntegrable.continuousOn_mul
    (continuous_const.sub continuous_id).continuousOn

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_D_neg (f : ℝ → ℝ) (hf : IsDemandDensity f) (m t : ℝ) (ht : 0 < t)
    (h : ∀ v ∈ Set.Ioo 0 t, f (m - v) < f (m + v)) :
    ∫ v in (0:ℝ)..t, (t - v) * (f (m - v) - f (m + v)) < 0 := by
  have hpos : 0 < ∫ v in (0:ℝ)..t, (t - v) * (f (m + v) - f (m - v)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_
      (fun v hv => mul_pos (by linarith [hv.2]) (by linarith [h v hv])) ht
    exact ((hf.integrable.comp_add_left m).sub (hf.integrable.comp_sub_left m)).intervalIntegrable.continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have e : ∫ v in (0:ℝ)..t, (t - v) * (f (m + v) - f (m - v)) =
      -∫ v in (0:ℝ)..t, (t - v) * (f (m - v) - f (m + v)) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext v; ring
  linarith

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_cont (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c : ℝ) :
    Continuous (nvProfit f p c) := by
  have hL : ∀ x y, |expMin f x - expMin f y| ≤ |x - y| := by
    intro x y
    unfold expMin
    rw [← integral_sub (bnv2d_minf_int f hf _) (bnv2d_minf_int f hf _)]
    have hb : Integrable (fun t => |x - y| * f t) := hf.integrable.const_mul _
    calc |∫ t, (min t x * f t - min t y * f t)|
        ≤ ∫ t, |x - y| * f t := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le hb (Eventually.of_forall (fun t => ?_))
          rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (hf.nonneg t)]
          refine mul_le_mul_of_nonneg_right ?_ (hf.nonneg t)
          have := abs_min_sub_min_le_max t x t y
          simpa using this
      _ = |x - y| := by rw [integral_const_mul, hf.integral_eq_one, mul_one]
  have hc : Continuous (expMin f) := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
    simpa [Real.dist_eq] using hL x y
  unfold nvProfit
  fun_prop

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_logitExp_eq (S : Set ℝ) (hS : MeasurableSet S) (u g : ℝ → ℝ) (β : ℝ) :
    logitExp S u β g =
      (∫ y in S, g y * Real.exp (u y / β)) / ∫ v in S, Real.exp (u v / β) := by
  unfold logitExp logitDensity
  have : (fun y => g y * S.indicator
      (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y) =
      S.indicator (fun y => g y * Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) := by
    funext y
    by_cases hy : y ∈ S <;> simp [hy, mul_div_assoc]
  rw [this, integral_indicator hS, integral_div]

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv2d_mean (u : ℝ → ℝ) (hu : Continuous u) (β a b : ℝ) (hab : a < b) :
    ∃ Z > 0, logitExp (Set.Icc a b) u β id = (a + b) / 2 +
      (∫ v in (0:ℝ)..((b - a) / 2), v * (Real.exp (u ((a + b) / 2 + v) / β)
        - Real.exp (u ((a + b) / 2 - v) / β))) / Z := by
  set w : ℝ → ℝ := fun y => Real.exp (u y / β) with hw
  have hwc : Continuous w := by rw [hw]; fun_prop
  have hIcc : ∀ g : ℝ → ℝ, ∫ y in Set.Icc a b, g y = ∫ y in a..b, g y := by
    intro g; rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab.le]
  refine ⟨∫ v in Set.Icc a b, w v, ?_, ?_⟩
  · rw [hIcc]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hwc.intervalIntegrable _ _)
      (fun x _ => Real.exp_pos _) hab
  have hZ : 0 < ∫ v in Set.Icc a b, w v := by
    rw [hIcc]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hwc.intervalIntegrable _ _)
      (fun x _ => Real.exp_pos _) hab
  rw [bnv2d_logitExp_eq _ measurableSet_Icc]
  change (∫ y in Set.Icc a b, id y * w y) / (∫ v in Set.Icc a b, w v) = _
  set m := (a + b) / 2 with hm
  set h := (b - a) / 2 with hh
  -- the key identity
  have hR : ∫ y in m..b, (y - m) * w y = ∫ v in (0:ℝ)..h, v * w (m + v) := by
    have e := intervalIntegral.integral_comp_add_left (fun y => (y - m) * w y) m (a := 0) (b := h)
    rw [add_zero, show m + h = b by rw [hm, hh]; ring] at e
    rw [← e]; congr 1; funext v; congr 1; ring
  have hLft : ∫ y in a..m, (y - m) * w y = -∫ v in (0:ℝ)..h, v * w (m - v) := by
    have e := intervalIntegral.integral_comp_sub_left (fun y => (y - m) * w y) m (a := 0) (b := h)
    rw [sub_zero, show m - h = a by rw [hm, hh]; ring] at e
    rw [← e, ← intervalIntegral.integral_neg]; congr 1; funext v; ring
  have hci : ∀ g : ℝ → ℝ, Continuous g → ∀ x y : ℝ, IntervalIntegrable g volume x y :=
    fun g hg x y => hg.intervalIntegrable x y
  have hK : ∫ y in a..b, (y - m) * w y =
      ∫ v in (0:ℝ)..h, v * (w (m + v) - w (m - v)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
      (hci _ (by fun_prop) _ _) (hci _ (by fun_prop) _ _), hR, hLft,
      ← sub_eq_neg_add, ← intervalIntegral.integral_sub (hci _ (by fun_prop) _ _)
      (hci _ (by fun_prop) _ _)]
    congr 1; funext v; ring
  have hsub : ∫ y in a..b, (y - m) * w y = (∫ y in a..b, y * w y) - m * ∫ y in a..b, w y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hci _ (by fun_prop) _ _) (hci _ (by fun_prop) _ _)]
    congr 1; funext y; ring
  simp only [id, hIcc] at hZ ⊢
  rw [← hK, hsub]
  field_simp
  ring

open BoundedNV.ExpFam BoundedNV.Uniform in
theorem solution (f : ℝ → ℝ) (p c β a b : ℝ)
    (hf : BoundedNV.ExpFam.IsDemandDensity f) (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ x ∉ Set.Icc a b, f x = 0)
    (hp : 0 < c) (hpc : c < p) (hβ : 0 < β)
    (hm : IsMaxOn (BoundedNV.Uniform.nvProfit f p c) Set.univ ((a + b) / 2)) :
    (StrictAntiOn f (Set.Icc a b) →
      (a + b) / 2 < BoundedNV.Uniform.logitExp (Set.Icc a b) (BoundedNV.Uniform.nvProfit f p c) β id) ∧
    (StrictMonoOn f (Set.Icc a b) →
      BoundedNV.Uniform.logitExp (Set.Icc a b) (BoundedNV.Uniform.nvProfit f p c) β id < (a + b) / 2) := by
  have hpp : 0 < p := by linarith
  obtain ⟨Z, hZ, hE⟩ := bnv2d_mean (nvProfit f p c) (bnv2d_cont f hf p c) β a b hab
  have hwc : Continuous (fun v => v * (Real.exp (nvProfit f p c ((a + b) / 2 + v) / β)
      - Real.exp (nvProfit f p c ((a + b) / 2 - v) / β))) := by
    have := bnv2d_cont f hf p c
    fun_prop
  have hh : (0:ℝ) < (b - a) / 2 := by linarith
  constructor
  · intro hdec
    have hM : ∀ x, f x ≤ f a := by
      intro x
      by_cases hx : x ∈ Set.Icc a b
      · exact hdec.antitoneOn ⟨le_refl a, hab.le⟩ hx hx.1
      · rw [hsupp x hx]; exact hf.nonneg a
    have hκ := bnv2d_kappa f hf p c ((a + b) / 2) (f a) hpp hM hm
    have hI : 0 < ∫ v in (0:ℝ)..((b - a) / 2), v * (Real.exp (nvProfit f p c ((a + b) / 2 + v) / β)
        - Real.exp (nvProfit f p c ((a + b) / 2 - v) / β)) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on (hwc.intervalIntegrable _ _) ?_ hh
      intro v hv
      refine mul_pos hv.1 ?_
      rw [sub_pos, Real.exp_lt_exp, div_lt_div_iff_of_pos_right hβ]
      have hφ := bnv2d_phi f hf p c ((a + b) / 2) v hv.1.le hκ
      have hD := bnv2d_D_pos f hf ((a + b) / 2) v hv.1 (fun w hw =>
        hdec ⟨by linarith [hw.2, hv.2], by linarith [hw.1, hw.2, hv.2]⟩
          ⟨by linarith [hw.1], by linarith [hw.2, hv.2]⟩ (by linarith [hw.1]))
      nlinarith [mul_pos hpp hD]
    rw [hE]
    have := div_pos hI hZ
    linarith
  · intro hinc
    have hM : ∀ x, f x ≤ f b := by
      intro x
      by_cases hx : x ∈ Set.Icc a b
      · exact hinc.monotoneOn hx ⟨hab.le, le_refl b⟩ hx.2
      · rw [hsupp x hx]; exact hf.nonneg b
    have hκ := bnv2d_kappa f hf p c ((a + b) / 2) (f b) hpp hM hm
    have hI : 0 < ∫ v in (0:ℝ)..((b - a) / 2), -(v * (Real.exp (nvProfit f p c ((a + b) / 2 + v) / β)
        - Real.exp (nvProfit f p c ((a + b) / 2 - v) / β))) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on (hwc.neg.intervalIntegrable _ _) ?_ hh
      intro v hv
      rw [neg_pos]
      refine mul_neg_of_pos_of_neg hv.1 ?_
      rw [sub_neg, Real.exp_lt_exp, div_lt_div_iff_of_pos_right hβ]
      have hφ := bnv2d_phi f hf p c ((a + b) / 2) v hv.1.le hκ
      have hD := bnv2d_D_neg f hf ((a + b) / 2) v hv.1 (fun w hw =>
        hinc ⟨by linarith [hw.2, hv.2], by linarith [hw.1, hw.2, hv.2]⟩
          ⟨by linarith [hw.1], by linarith [hw.2, hv.2]⟩ (by linarith [hw.1]))
      nlinarith [mul_neg_of_pos_of_neg hpp hD]
    rw [intervalIntegral.integral_neg, neg_pos] at hI
    rw [hE]
    have := div_neg_of_neg_of_pos hI hZ
    linarith
