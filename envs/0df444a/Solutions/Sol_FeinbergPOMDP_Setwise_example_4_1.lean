-- Prove2me | solution 1 for FeinbergPOMDP.Setwise.example_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T06:03:08.922492+00:00
-- url     : https://prove2.me/submissions/59ac9fbc-01b3-40ca-9cf5-2f2e73e0c3f2

import Mathlib
import Definitions.Def_FeinbergPOMDP_Setwise_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction ENNReal

namespace FKZ41

/-- The 1-periodic indicator of `fract x ∈ (0, 1/2)`. -/
noncomputable def hfun (x : ℝ) : ℝ := if Int.fract x ∈ Ioo (0:ℝ) (1/2) then 1 else 0

lemma measurableSet_fractSet : MeasurableSet {x : ℝ | Int.fract x ∈ Ioo (0:ℝ) (1/2)} :=
  measurableSet_Ioo.preimage measurable_fract

lemma hfun_eq : hfun = {x : ℝ | Int.fract x ∈ Ioo (0:ℝ) (1/2)}.indicator 1 := by
  funext x; simp only [hfun, Set.indicator, mem_setOf_eq, Pi.one_apply]

lemma hfun_periodic : Function.Periodic hfun 1 := by
  intro x; simp only [hfun, Int.fract_add_one]

lemma hfun_meas : Measurable hfun := by
  rw [hfun_eq]; exact measurable_one.indicator measurableSet_fractSet

lemma hfun_nonneg (x : ℝ) : 0 ≤ hfun x := by unfold hfun; split_ifs <;> norm_num

lemma hfun_le_one (x : ℝ) : hfun x ≤ 1 := by unfold hfun; split_ifs <;> norm_num

lemma hfun_norm_le (x : ℝ) : ‖hfun x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hfun_nonneg x)]; exact hfun_le_one x

lemma hfun_intInt (a b : ℝ) : IntervalIntegrable hfun volume a b := by
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hfun_meas.aestronglyMeasurable ?_
  exact Eventually.of_forall (fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hfun_nonneg x)] using hfun_le_one x)

lemma integral_hfun_01 : ∫ x in (0:ℝ)..1, hfun x = 1/2 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hc : EqOn hfun ((Ioo (0:ℝ) (1/2)).indicator 1) (Ioc (0:ℝ) 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h1 | h1
    · subst h1
      simp [hfun, Set.indicator]
      norm_num
    · have hf : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, h1⟩
      simp only [hfun, hf, Set.indicator, Pi.one_apply]
  rw [setIntegral_congr_fun measurableSet_Ioc hc, integral_indicator measurableSet_Ioo]
  simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one, Measure.restrict_restrict
    measurableSet_Ioo, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  have : Ioo (0:ℝ) (1/2) ∩ Ioc 0 1 = Ioo 0 (1/2) := by
    ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioc]; constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, h.1, by linarith [h.2]⟩
  rw [measureReal_def, Measure.restrict_apply_univ, this, Real.volume_Ioo]
  norm_num

lemma integral_hfun_nat (n : ℕ) : ∫ x in (0:ℝ)..n, hfun x = n/2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hk, ← intervalIntegral.integral_add_adjacent_intervals (hfun_intInt 0 k)
      (hfun_intInt k (k+1)), ih, hfun_periodic.intervalIntegral_add_eq (k:ℝ) 0, zero_add,
      integral_hfun_01]
    ring

/-- `H x = ∫_0^x hfun` stays within 2 of `x/2`. -/
lemma integral_hfun_near (x : ℝ) (hx : 0 ≤ x) :
    |(∫ t in (0:ℝ)..x, hfun t) - x/2| ≤ 2 := by
  set n := ⌊x⌋₊
  have hn1 : (n:ℝ) ≤ x := Nat.floor_le hx
  have hn2 : x < n + 1 := Nat.lt_floor_add_one x
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hfun_intInt 0 n)
    (hfun_intInt n x)
  have hb : ‖∫ t in (n:ℝ)..x, hfun t‖ ≤ 1 * |x - n| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hfun_norm_le t)
  rw [← hsplit, integral_hfun_nat]
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - n)] at hb
  have := abs_le.mp hb
  rw [abs_le]; constructor <;> linarith

/-- The real dyadic zero set of level `m`. -/
def Zr (m : ℕ) : Set ℝ := {y : ℝ | Int.fract ((2:ℝ)^m * y) ∈ Ioo (0:ℝ) (1/2)}

lemma measurableSet_Zr (m : ℕ) : MeasurableSet (Zr m) :=
  measurableSet_fractSet.preimage (measurable_const_mul _)

/-- Key estimate on `[0,s]`. -/
lemma volume_Icc_inter_Zr (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    |(volume (Icc 0 s ∩ Zr m)).toReal - s/2| ≤ 2 / 2^m := by
  have hM : (0:ℝ) < 2^m := by positivity
  have h0 : Icc 0 s ∩ Zr m = Ioc 0 s ∩ Zr m := by
    ext y; simp only [mem_inter_iff, mem_Icc, mem_Ioc, Zr, mem_setOf_eq]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      rcases eq_or_lt_of_le h1 with h | h
      · subst h; simp at h3
      · exact h
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.le, h2⟩, h3⟩
  have hI : (volume (Ioc 0 s ∩ Zr m)).toReal = ∫ y in (0:ℝ)..s, hfun ((2:ℝ)^m * y) := by
    rw [intervalIntegral.integral_of_le hs]
    have : (fun y => hfun ((2:ℝ)^m * y)) = (Zr m).indicator 1 := by
      funext y; simp only [hfun, Zr, Set.indicator, mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator (measurableSet_Zr m)]
    simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.restrict_restrict (measurableSet_Zr m)]
    rw [inter_comm]
  rw [h0, hI, intervalIntegral.integral_comp_mul_left (fun t => hfun t) hM.ne', mul_zero]
  have key := integral_hfun_near ((2:ℝ)^m * s) (by positivity)
  rw [smul_eq_mul]
  have e : ((2:ℝ)^m)⁻¹ * (∫ t in (0:ℝ)..(2:ℝ)^m * s, hfun t) - s/2
      = ((2:ℝ)^m)⁻¹ * ((∫ t in (0:ℝ)..(2:ℝ)^m * s, hfun t) - (2:ℝ)^m * s / 2) := by
    rw [mul_sub]; congr 1; field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hM)]
  calc ((2:ℝ)^m)⁻¹ * |(∫ t in (0:ℝ)..(2:ℝ)^m * s, hfun t) - (2:ℝ)^m * s / 2|
      ≤ ((2:ℝ)^m)⁻¹ * 2 := mul_le_mul_of_nonneg_left key (by positivity)
    _ = 2 / 2^m := by ring

lemma tendsto_two_div_pow : Tendsto (fun m : ℕ => (2:ℝ) / 2^m) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).const_mul 2
  rw [mul_zero] at h
  refine h.congr (fun m => ?_)
  rw [one_div, inv_pow]; ring

/-- Convergence on the generators `Iic t`. -/
lemma tendsto_Iic (t : ℝ) :
    Tendsto (fun m => (volume (Iic t ∩ Icc 0 1 ∩ Zr m)).toReal) atTop
      (𝓝 ((volume (Iic t ∩ Icc (0:ℝ) 1)).toReal / 2)) := by
  rcases lt_or_ge t 0 with ht | ht
  · have he : Iic t ∩ Icc (0:ℝ) 1 = ∅ := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, _⟩; linarith
    simp [he]
  · set s := min t 1 with hsdef
    have hs0 : 0 ≤ s := le_min ht zero_le_one
    have he : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 s := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc, hsdef, le_min_iff]; tauto
    rw [he, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), sub_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) tendsto_two_div_pow
    rw [Real.norm_eq_abs]; exact volume_Icc_inter_Zr m s hs0

open Classical FeinbergPOMDP.Setwise in
lemma density_eq (n : PositiveNat) (y : Observation) :
    density n y = if (y:ℝ) ∈ Zr (n.1 - 1) then 0 else 2 := by
  have hn : (2:ℝ)^n.1 = 2 * 2^(n.1-1) := by
    rw [← pow_succ']; congr 1; have := n.2; omega
  set M : ℝ := (2:ℝ)^(n.1-1) with hMdef
  have hM : 0 < M := by positivity
  have hy0 : 0 ≤ (y:ℝ) := y.2.1
  have hy1 : (y:ℝ) ≤ 1 := y.2.2
  unfold density
  congr 1
  apply propext
  rw [hn]
  simp only [Zr, mem_Ioo]
  rw [show {y : ℝ | 0 < Int.fract (2 ^ (n.1 - 1) * y) ∧ Int.fract (2 ^ (n.1 - 1) * y) < 1 / 2}
    = {y : ℝ | 0 < Int.fract (M * y) ∧ Int.fract (M * y) < 1 / 2} from rfl]
  show _ ↔ 0 < Int.fract (M * (y:ℝ)) ∧ Int.fract (M * (y:ℝ)) < 1 / 2
  constructor
  · rintro ⟨k, _, h1, h2⟩
    have a1 : (k:ℝ) < M * y := by
      rw [div_lt_iff₀ (by positivity)] at h1; nlinarith
    have a2 : M * y < k + 1/2 := by
      rw [lt_div_iff₀ (by positivity)] at h2; nlinarith
    have hfl : ⌊M * (y:ℝ)⌋ = (k:ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [← Int.self_sub_floor, hfl]; push_cast
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hfl : ((⌊M * (y:ℝ)⌋₊ : ℕ) : ℝ) = ((⌊M * (y:ℝ)⌋ : ℤ) : ℝ) := by
      rw [← Int.natCast_floor_eq_floor (by positivity)]; push_cast; rfl
    rw [← Int.self_sub_floor, ← hfl] at h1 h2
    set k := ⌊M * (y:ℝ)⌋₊
    have a1 : (k:ℝ) < M * y := by linarith
    have a2 : M * y < k + 1/2 := by linarith
    refine ⟨k, ?_, ?_, ?_⟩
    · have : (k:ℝ) < ((2^(n.1-1) : ℕ) : ℝ) := by
        push_cast; rw [← hMdef]; nlinarith
      exact_mod_cast this
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · rw [lt_div_iff₀ (by positivity)]; nlinarith

/-- Lebesgue measure on `[0,1]`, as a measure on `ℝ`. -/
noncomputable def nu : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

lemma nu_finite : IsFiniteMeasure nu :=
  ⟨by rw [nu, Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩

lemma nu_real_univ : nu.real univ = 1 := by
  rw [measureReal_def, nu, Measure.restrict_apply_univ, Real.volume_Icc]; simp

lemma nu_real_inter (D : Set ℝ) (m : ℕ) :
    nu.real (D ∩ Zr m) = (volume (D ∩ Icc 0 1 ∩ Zr m)).toReal := by
  rw [measureReal_def, nu, Measure.restrict_apply' measurableSet_Icc]
  congr 2; ext y; simp only [mem_inter_iff]; tauto

lemma nu_real_eq (D : Set ℝ) : nu.real D = (volume (D ∩ Icc 0 1)).toReal := by
  rw [measureReal_def, nu, Measure.restrict_apply' measurableSet_Icc]

/-- Setwise convergence of `nu(· ∩ Z_m)` to `nu(·)/2` on every Borel set (Dynkin). -/
lemma tendsto_all (D : Set ℝ) (hD : MeasurableSet D) :
    Tendsto (fun m => nu.real (D ∩ Zr m)) atTop (𝓝 (nu.real D / 2)) := by
  haveI := nu_finite
  have h_eq : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom (range Iic) :=
    BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic (α := ℝ))
  refine MeasurableSpace.induction_on_inter
    (C := fun D _ => Tendsto (fun m => nu.real (D ∩ Zr m)) atTop (𝓝 (nu.real D / 2)))
    h_eq isPiSystem_Iic ?_ ?_ ?_ ?_ D hD
  · simp
  · rintro t ⟨a, rfl⟩
    simp only [nu_real_inter]; rw [nu_real_eq]
    exact tendsto_Iic a
  · intro D hDm hP
    have hU : Tendsto (fun m => nu.real (univ ∩ Zr m)) atTop (𝓝 (nu.real univ / 2)) := by
      have h1 := tendsto_Iic 1
      have e : Iic (1:ℝ) ∩ Icc 0 1 = univ ∩ Icc 0 1 := by
        ext y; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_univ, true_and]; tauto
      rw [e] at h1
      simp only [nu_real_inter]; rw [nu_real_eq]
      exact h1
    simp only [univ_inter, nu_real_univ] at hU
    have e1 : ∀ m, nu.real (Dᶜ ∩ Zr m) = nu.real (Zr m) - nu.real (D ∩ Zr m) := by
      intro m
      rw [← measureReal_diff inter_subset_right (hDm.inter (measurableSet_Zr m))]
      congr 1; ext y; simp only [mem_inter_iff, mem_compl_iff, mem_diff]; tauto
    have e2 : nu.real Dᶜ = 1 - nu.real D := by
      rw [measureReal_compl hDm, nu_real_univ]
    simp only [e1, e2]
    have := hU.sub hP
    convert this using 2; ring
  · intro f hdisj hfm hP
    have hdZ : ∀ m, Pairwise (Function.onFun Disjoint fun i => f i ∩ Zr m) := fun m i j hij =>
      (hdisj hij).mono inter_subset_left inter_subset_left
    have e1 : ∀ m, nu.real ((⋃ i, f i) ∩ Zr m) = ∑' i, nu.real (f i ∩ Zr m) := by
      intro m
      rw [iUnion_inter, measureReal_def,
        measure_iUnion (hdZ m) (fun i => (hfm i).inter (measurableSet_Zr m)),
        ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _)]
      rfl
    have e2 : nu.real (⋃ i, f i) = ∑' i, nu.real (f i) := by
      rw [measureReal_def, measure_iUnion hdisj hfm,
        ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _)]
      rfl
    simp only [e1, e2]
    have hsum : Summable (fun i => nu.real (f i)) := by
      apply ENNReal.summable_toReal
      rw [← measure_iUnion hdisj hfm]; exact measure_ne_top _ _
    have := tendsto_tsum_of_dominated_convergence (f := fun m i => nu.real (f i ∩ Zr m))
      (g := fun i => nu.real (f i) / 2) hsum (fun i => hP i)
      (Eventually.of_forall (fun m i => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_mono inter_subset_left))
    rw [tsum_div_const] at this
    exact this

lemma nu_real_Zr (m : ℕ) : nu.real (Zr m) = 1/2 := by
  have hM : (0:ℝ) < 2^m := by positivity
  rw [measureReal_def, nu, Measure.restrict_apply (measurableSet_Zr m), inter_comm]
  have h0 : Icc 0 1 ∩ Zr m = Ioc 0 1 ∩ Zr m := by
    ext y; simp only [mem_inter_iff, mem_Icc, mem_Ioc, Zr, mem_setOf_eq]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      rcases eq_or_lt_of_le h1 with h | h
      · subst h; simp at h3
      · exact h
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1.le, h2⟩, h3⟩
  have hI : (volume (Ioc 0 1 ∩ Zr m)).toReal = ∫ y in (0:ℝ)..1, hfun ((2:ℝ)^m * y) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have : (fun y => hfun ((2:ℝ)^m * y)) = (Zr m).indicator 1 := by
      funext y; simp only [hfun, Zr, Set.indicator, mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator (measurableSet_Zr m)]
    simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.restrict_restrict (measurableSet_Zr m)]
    rw [inter_comm]
  rw [h0, hI, intervalIntegral.integral_comp_mul_left (fun t => hfun t) hM.ne', mul_zero, mul_one,
    smul_eq_mul]
  have e : ((2:ℝ)^m) = ((2^m : ℕ) : ℝ) := by push_cast; ring
  rw [e, integral_hfun_nat]
  have : (0:ℝ) < ((2^m : ℕ) : ℝ) := by rw [← e]; exact hM
  field_simp

open FeinbergPOMDP.Setwise

lemma vol_preimage (D : Set ℝ) (hD : MeasurableSet D) :
    (volume (Subtype.val ⁻¹' D : Set Observation)) = nu D := by
  rw [unitInterval.volume_apply, Subtype.image_preimage_coe, nu, Measure.restrict_apply hD]
  congr 1; exact inter_comm _ _

lemma dyadicLaw_apply (n : PositiveNat) (D : Set ℝ) (hD : MeasurableSet D) :
    dyadicLaw n (Subtype.val ⁻¹' D) = 2 * nu (D \ Zr (n.1 - 1)) := by
  have hZ : MeasurableSet (Subtype.val ⁻¹' Zr (n.1 - 1) : Set Observation) :=
    (measurableSet_Zr _).preimage measurable_subtype_coe
  have hC : MeasurableSet (Subtype.val ⁻¹' D : Set Observation) :=
    hD.preimage measurable_subtype_coe
  have hden : density n = (Subtype.val ⁻¹' Zr (n.1 - 1) : Set Observation)ᶜ.indicator
      (fun _ => (2:ℝ≥0∞)) := by
    funext y; rw [density_eq]
    simp only [Set.indicator, mem_compl_iff, mem_preimage]
    split_ifs <;> simp_all
  rw [dyadicLaw, withDensity_apply _ hC, hden, lintegral_indicator_const hZ.compl,
    Measure.restrict_apply hZ.compl]
  congr 1
  rw [show (Subtype.val ⁻¹' Zr (n.1 - 1) : Set Observation)ᶜ ∩ Subtype.val ⁻¹' D
      = Subtype.val ⁻¹' (D \ Zr (n.1 - 1)) by
    ext y; simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_diff]; tauto]
  exact vol_preimage _ (hD.diff (measurableSet_Zr _))

lemma dyadicLaw_real (n : PositiveNat) (D : Set ℝ) (hD : MeasurableSet D) :
    dyadicLaw n (Subtype.val ⁻¹' D) =
      ENNReal.ofReal (2 * (nu.real D - nu.real (D ∩ Zr (n.1 - 1)))) := by
  haveI := nu_finite
  rw [dyadicLaw_apply n D hD, ← ofReal_measureReal (measure_ne_top _ _)]
  rw [show D \ Zr (n.1 - 1) = D \ (D ∩ Zr (n.1 - 1)) by
    ext y; simp only [mem_diff, mem_inter_iff]; tauto]
  rw [measureReal_diff inter_subset_left (hD.inter (measurableSet_Zr _)),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]

lemma dyadicLaw_univ (n : PositiveNat) : dyadicLaw n univ = 1 := by
  haveI := nu_finite
  have h := dyadicLaw_real n univ MeasurableSet.univ
  rw [preimage_univ, univ_inter, nu_real_univ, nu_real_Zr] at h
  rw [h]; norm_num

lemma dyadicLaw_prob (n : PositiveNat) : IsProbabilityMeasure (dyadicLaw n) :=
  ⟨dyadicLaw_univ n⟩

attribute [local instance] dyadicLaw_prob

lemma tendsto_G (C : Set Observation) (hC : MeasurableSet C) :
    Tendsto (fun k : ℕ => if h : 1 ≤ k then dyadicLaw ⟨k, h⟩ C else volume C) atTop
      (𝓝 (volume C)) := by
  obtain ⟨D, hD, rfl⟩ := hC
  haveI := nu_finite
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * (nu.real D - nu.real (D ∩ Zr (k-1)))))
      atTop (𝓝 (ENNReal.ofReal (2 * (nu.real D - nu.real D / 2)))) := by
    apply ENNReal.tendsto_ofReal
    exact (((tendsto_all D hD).comp (tendsto_sub_atTop_nat 1)).const_sub _).const_mul 2
  have e : 2 * (nu.real D - nu.real D / 2) = nu.real D := by ring
  rw [e, ofReal_measureReal (measure_ne_top _ _), ← vol_preimage D hD] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [dif_pos hk, dyadicLaw_real _ D hD]

lemma actionIndex_spec (b : Action) (h : b.1 ≠ 0) :
    b.1 = 1 / ((actionIndex b h).1 : ℝ) :=
  (Classical.choose_spec (b.2.resolve_left h)).2

lemma floor_inv_eq (b : Action) (h : b.1 ≠ 0) : ⌊(b.1)⁻¹⌋₊ = (actionIndex b h).1 := by
  have e := actionIndex_spec b h
  set k := actionIndex b h
  rw [e, one_div, inv_inv, Nat.floor_natCast]

lemma obs_state0 (a : Action) : observationKernel (a, 0) = volume := by
  simp [observationKernel]

lemma obs_action0 (x : State) : observationKernel (zeroAction, x) = volume := by
  simp [observationKernel, zeroAction]

lemma obs_ne (b : Action) (h : b.1 ≠ 0) :
    observationKernel (b, 1) = dyadicLaw (actionIndex b h) := by
  simp [observationKernel, h]

lemma obs_markov : IsMarkovKernel observationKernel := by
  refine ⟨fun p => ?_⟩
  rcases p with ⟨a, x⟩
  by_cases hx : x = 0
  · subst hx; rw [obs_state0]; infer_instance
  · have hx1 : x = 1 := by fin_cases x <;> simp_all
    subst hx1
    by_cases ha : a.1 = 0
    · have : a = zeroAction := Subtype.ext ha
      subst this; rw [obs_action0]; infer_instance
    · rw [obs_ne a ha]; infer_instance

lemma inv_eq_index (b : Action) (hb : b.1 ≠ 0) : (b.1)⁻¹ = ((actionIndex b hb).1 : ℝ) := by
  calc (b.1)⁻¹ = (1 / ((actionIndex b hb).1 : ℝ))⁻¹ := by rw [← actionIndex_spec b hb]
    _ = _ := by rw [one_div, inv_inv]

lemma recip_tendsto :
    Tendsto (fun k : ℕ => reciprocalAction ⟨k + 1, by omega⟩) atTop (𝓝 zeroAction) := by
  rw [tendsto_subtype_rng]
  show Tendsto _ _ (𝓝 (0:ℝ))
  refine tendsto_one_div_add_atTop_nhds_zero_nat.congr (fun k => ?_)
  simp [reciprocalAction]

lemma transition_apply (p : State × Action) : transition p = Measure.dirac p.1 := by
  simp [transition, Kernel.deterministic_apply]

lemma tv_cont : TVContinuous (fun p : State × Action => transition p) := by
  intro s ss hss
  have h1 : Tendsto (fun n => (ss n).1) atTop (𝓝 s.1) := (continuous_fst.tendsto s).comp hss
  rw [nhds_discrete] at h1
  have hev : ∀ᶠ n in atTop, (ss n).1 = s.1 := tendsto_pure.mp h1
  refine ⟨fun n => by simp only [transition_apply]; infer_instance,
    by simp only [transition_apply]; infer_instance, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn f _ _ => ?_⟩
  simp only [transition_apply, hN n hn, sub_self, abs_zero]; exact hε.le

lemma setwise_cont : SetwiseContinuous (fun p : Action × State => observationKernel p) := by
  intro s ss hss
  haveI := obs_markov
  refine ⟨fun n => inferInstance, inferInstance, fun C hC => ?_⟩
  have h2 : ∀ᶠ n in atTop, (ss n).2 = s.2 := by
    have := (continuous_snd.tendsto s).comp hss
    rw [nhds_discrete] at this
    exact tendsto_pure.mp this
  have h1 : Tendsto (fun n => (ss n).1) atTop (𝓝 s.1) := (continuous_fst.tendsto s).comp hss
  rcases s with ⟨a, x⟩
  by_cases hx : x = 0
  · subst hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h2] with n hn
    show observationKernel (a, 0) C = observationKernel (ss n) C
    generalize ss n = p at hn ⊢
    obtain ⟨b, y⟩ := p
    simp only at hn; subst hn
    rw [obs_state0, obs_state0]
  have hx1 : x = 1 := by fin_cases x <;> simp_all
  subst hx1
  by_cases ha : a.1 = 0
  · have ha' : a = zeroAction := Subtype.ext ha
    subst ha'
    set G : ℕ → ℝ≥0∞ := fun k => if h : 1 ≤ k then dyadicLaw ⟨k, h⟩ C else volume C with hGdef
    have hG : Tendsto G atTop (𝓝 (volume C)) := tendsto_G C hC
    have hFG : ∀ b : Action, observationKernel (b, 1) C = G ⌊(b.1)⁻¹⌋₊ := by
      intro b
      by_cases hb : b.1 = 0
      · have : b = zeroAction := Subtype.ext hb
        subst this; rw [obs_action0]; simp [G, zeroAction]
      · rw [obs_ne b hb, floor_inv_eq b hb]; simp [G, (actionIndex b hb).2]
    have hreal : Tendsto (fun n => ((ss n).1 : ℝ)) atTop (𝓝 0) :=
      (continuous_subtype_val.tendsto _).comp h1
    have key : Tendsto (fun n => G ⌊((ss n).1 : ℝ)⁻¹⌋₊) atTop (𝓝 (volume C)) := by
      refine fun U hU => Filter.mem_map.mpr ?_
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hG.eventually_mem hU)
      have hU0 : G 0 ∈ U := by simp only [G]; exact mem_of_mem_nhds hU
      have hsmall : ∀ᶠ n in atTop, dist ((ss n).1 : ℝ) 0 < 1 / ((N:ℝ) + 1) :=
        Metric.tendsto_nhds.mp hreal _ (by positivity)
      filter_upwards [hsmall] with n hn
      show G _ ∈ U
      set b := (ss n).1
      by_cases hb : b.1 = 0
      · rw [hb, inv_zero, Nat.floor_zero]; exact hU0
      · rw [floor_inv_eq b hb]
        apply hN
        have e := actionIndex_spec b hb
        have hk : (0:ℝ) < (actionIndex b hb).1 := by
          have := (actionIndex b hb).2; exact_mod_cast (by omega : 0 < (actionIndex b hb).1)
        rw [Real.dist_eq, sub_zero, e, abs_of_pos (by positivity)] at hn
        rw [one_div_lt_one_div hk (by positivity)] at hn
        have : (N:ℝ) < (actionIndex b hb).1 := by linarith
        exact_mod_cast this.le
    show Tendsto (fun n => observationKernel (ss n) C) atTop
      (𝓝 (observationKernel (zeroAction, 1) C))
    rw [obs_action0]
    refine key.congr' ?_
    filter_upwards [h2] with n hn
    show G ⌊((ss n).1 : ℝ)⁻¹⌋₊ = observationKernel (ss n) C
    generalize ss n = p at hn ⊢
    obtain ⟨b, y⟩ := p
    simp only at hn; subst hn
    exact (hFG b).symm
  · have hinv : Tendsto (fun n => (((ss n).1 : ℝ))⁻¹) atTop (𝓝 ((a:ℝ)⁻¹)) :=
      ((continuous_subtype_val.tendsto _).comp h1).inv₀ ha
    rw [inv_eq_index a ha] at hinv
    have hm1 : 1 ≤ (actionIndex a ha).1 := (actionIndex a ha).2
    have hev : ∀ᶠ n in atTop, (ss n).1 = a := by
      filter_upwards [Metric.tendsto_nhds.mp hinv (1/2) (by norm_num)] with n hn
      rw [Real.dist_eq] at hn
      set b := (ss n).1
      by_cases hb : b.1 = 0
      · rw [hb, inv_zero, zero_sub, abs_neg] at hn
        have : (1:ℝ) ≤ (actionIndex a ha).1 := by exact_mod_cast hm1
        rw [abs_of_pos (by linarith)] at hn; linarith
      · rw [inv_eq_index b hb] at hn
        have hh := abs_sub_lt_iff.mp hn
        have c1 : ((actionIndex b hb).1 : ℝ) < (actionIndex a ha).1 + 1 := by linarith
        have c2 : ((actionIndex a ha).1 : ℝ) < (actionIndex b hb).1 + 1 := by linarith
        have d1 : (actionIndex b hb).1 < (actionIndex a ha).1 + 1 := by exact_mod_cast c1
        have d2 : (actionIndex a ha).1 < (actionIndex b hb).1 + 1 := by exact_mod_cast c2
        have hkm : (actionIndex b hb).1 = (actionIndex a ha).1 := by omega
        apply Subtype.ext
        rw [actionIndex_spec b hb, actionIndex_spec a ha, hkm]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h2, hev] with n hn hn'
    show observationKernel (a, 1) C = observationKernel (ss n) C
    generalize ss n = p at hn hn' ⊢
    obtain ⟨b, y⟩ := p
    simp only at hn hn'; subst hn hn'
    rfl

/-! ### The explicit filter -/

noncomputable def q1 (a : Action) (y : Observation) : ℝ≥0∞ :=
  if h : a.1 = 0 then 1 else density (actionIndex a h) y

noncomputable def qx (a : Action) (x : State) (y : Observation) : ℝ≥0∞ :=
  if x = 0 then 1 else q1 a y

lemma density_ind (n : PositiveNat) : density n =
    (Subtype.val ⁻¹' Zr (n.1 - 1) : Set Observation)ᶜ.indicator (fun _ => (2:ℝ≥0∞)) := by
  funext y; rw [density_eq]
  simp only [Set.indicator, mem_compl_iff, mem_preimage]
  split_ifs <;> simp_all

lemma q1_le (a : Action) (y : Observation) : q1 a y ≤ 2 := by
  unfold q1; split_ifs
  · exact one_le_two
  · rw [density_eq]; split_ifs <;> simp

lemma q1_ne_top (a : Action) (y : Observation) : q1 a y ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (q1_le a y)

lemma q1_meas (a : Action) : Measurable (q1 a) := by
  unfold q1; split_ifs with h
  · exact measurable_const
  · rw [density_ind]
    exact measurable_const.indicator
      ((measurableSet_Zr _).preimage measurable_subtype_coe).compl

lemma qx_meas (a : Action) (x : State) : Measurable (qx a x) := by
  unfold qx; split_ifs
  · exact measurable_const
  · exact q1_meas a

lemma obs_withDensity (a : Action) (x : State) :
    observationKernel (a, x) = volume.withDensity (qx a x) := by
  by_cases hx : x = 0
  · subst hx
    have : qx a 0 = 1 := by funext y; simp [qx]
    rw [obs_state0, this, withDensity_one]
  · have hx1 : x = 1 := by fin_cases x <;> simp_all
    subst hx1
    by_cases ha : a.1 = 0
    · have : a = zeroAction := Subtype.ext ha
      subst this
      have : qx zeroAction 1 = 1 := by funext y; simp [qx, q1, zeroAction]
      rw [obs_action0, this, withDensity_one]
    · rw [obs_ne a ha, dyadicLaw]; congr 1; funext y; simp [qx, q1, ha]

noncomputable def wt (z : ProbabilityMeasure State) (c : ℝ≥0∞) (x : State) : ℝ≥0∞ :=
  (z : Measure State) {x} * (if x = 0 then 1 else c)

noncomputable def tot (z : ProbabilityMeasure State) (c : ℝ≥0∞) : ℝ≥0∞ := ∑ x, wt z c x

lemma tot_ne_top (z : ProbabilityMeasure State) (c : ℝ≥0∞) (hc : c ≠ ∞) : tot z c ≠ ∞ := by
  unfold tot
  refine ENNReal.sum_ne_top.2 (fun x _ => ENNReal.mul_ne_top (measure_ne_top _ _) ?_)
  split_ifs
  · simp
  · exact hc

noncomputable def postM (z : ProbabilityMeasure State) (c : ℝ≥0∞) : Measure State :=
  if tot z c = 0 ∨ tot z c = ∞ then (z : Measure State)
  else ∑ x, (wt z c x / tot z c) • Measure.dirac x

lemma postM_apply_of (z : ProbabilityMeasure State) (c : ℝ≥0∞) (h0 : tot z c ≠ 0)
    (htop : tot z c ≠ ∞) (B : Set State) :
    postM z c B = ∑ x, wt z c x / tot z c * B.indicator 1 x := by
  rw [postM, if_neg (by tauto)]
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete)]

lemma postM_prob (z : ProbabilityMeasure State) (c : ℝ≥0∞) : IsProbabilityMeasure (postM z c) := by
  by_cases h : tot z c = 0 ∨ tot z c = ∞
  · rw [postM, if_pos h]; infer_instance
  · push_neg at h
    constructor
    rw [postM_apply_of z c h.1 h.2]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact ENNReal.mul_inv_cancel h.1 h.2

noncomputable def post (z : ProbabilityMeasure State) (c : ℝ≥0∞) : ProbabilityMeasure State :=
  ⟨postM z c, postM_prob z c⟩

lemma tot_mul_post (z : ProbabilityMeasure State) (c : ℝ≥0∞) (hc : c ≠ ∞) (B : Set State) :
    tot z c * postM z c B = ∑ x, wt z c x * B.indicator 1 x := by
  have htop := tot_ne_top z c hc
  by_cases h0 : tot z c = 0
  · rw [h0, zero_mul]; symm
    apply Finset.sum_eq_zero; intro x _
    have : wt z c x = 0 := (Finset.sum_eq_zero_iff.mp h0) x (Finset.mem_univ x)
    rw [this, zero_mul]
  · rw [postM_apply_of z c h0 htop, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← mul_assoc, ENNReal.mul_div_cancel h0 htop]

noncomputable def Hf (z : ProbabilityMeasure State) (a : Action) (y : Observation) :
    ProbabilityMeasure State := post z (q1 a y)

lemma R_apply (z : ProbabilityMeasure State) (a : Action) (B : Set State) (C : Set Observation)
    (hC : MeasurableSet C) :
    R transition observationKernel z a (B ×ˢ C) =
      ∑ x, (z : Measure State) {x} * B.indicator 1 x * observationKernel (a, x) C := by
  haveI := obs_markov
  have hb : (z : Measure State).bind (fun x => transition (x, a)) = z := by
    have : (fun x => transition (x, a)) = Measure.dirac := by
      funext x; rw [transition_apply]
    rw [this, Measure.bind_dirac]
  rw [R, hb, Measure.compProd_apply_prod MeasurableSet.of_discrete hC, lintegral_fintype]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Kernel.comap_apply, Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ B
  · rw [singleton_inter_of_mem hx, indicator_of_mem hx]; simp only [Pi.one_apply]; ring
  · rw [singleton_inter_eq_empty.mpr hx, indicator_of_notMem hx]; simp

lemma tot_q1_eq (z : ProbabilityMeasure State) (a : Action) :
    (fun y => tot z (q1 a y)) = fun y => ∑ x, (z : Measure State) {x} * qx a x y := rfl

lemma tot_q1_meas (z : ProbabilityMeasure State) (a : Action) :
    Measurable (fun y => tot z (q1 a y)) := by
  rw [tot_q1_eq]
  exact Finset.measurable_sum _ (fun x _ => (qx_meas a x).const_mul _)

lemma Rprime_eq (z : ProbabilityMeasure State) (a : Action) :
    Rprime transition observationKernel z a = volume.withDensity (fun y => tot z (q1 a y)) := by
  ext C hC
  rw [Rprime, Measure.map_apply measurable_snd hC,
    show Prod.snd ⁻¹' C = (univ : Set State) ×ˢ C by ext; simp, R_apply z a univ C hC,
    withDensity_apply _ hC, tot_q1_eq,
    lintegral_finset_sum _ (fun x _ => (qx_meas a x).const_mul _)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [lintegral_const_mul _ (qx_meas a x), obs_withDensity, withDensity_apply _ hC]
  simp

lemma Hf_eq (z : ProbabilityMeasure State) (a : Action) (B : Set State) (C : Set Observation)
    (hC : MeasurableSet C) :
    R transition observationKernel z a (B ×ˢ C) =
      ∫⁻ y in C, (Hf z a y : Measure State) B ∂(Rprime transition observationKernel z a) := by
  rw [Rprime_eq, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _
    (tot_q1_meas z a) _ hC (Eventually.of_forall (fun y => (tot_ne_top z _ (q1_ne_top a y)).lt_top))]
  have : ∀ y, ((fun y => tot z (q1 a y)) * fun y => (Hf z a y : Measure State) B) y
      = ∑ x, (z : Measure State) {x} * B.indicator 1 x * qx a x y := by
    intro y
    simp only [Pi.mul_apply]
    rw [show (Hf z a y : Measure State) = postM z (q1 a y) from rfl,
      tot_mul_post z _ (q1_ne_top a y)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [wt, qx]; ring
  simp_rw [this]
  rw [lintegral_finset_sum _ (fun x _ => (qx_meas a x).const_mul _), R_apply z a B C hC]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [lintegral_const_mul _ (qx_meas a x), obs_withDensity, withDensity_apply _ hC]

open Classical in
lemma Hf_cases (z : ProbabilityMeasure State) (a : Action) :
    (∃ p, Hf z a = fun _ => p) ∨
    (∃ (S : Set Observation) (p q : ProbabilityMeasure State), MeasurableSet S ∧
      Hf z a = fun y => if y ∈ S then p else q) := by
  by_cases ha : a.1 = 0
  · exact Or.inl ⟨post z 1, funext (fun y => by simp [Hf, q1, ha])⟩
  · refine Or.inr ⟨Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1), post z 0, post z 2,
      (measurableSet_Zr _).preimage measurable_subtype_coe, funext (fun y => ?_)⟩
    simp only [Hf, q1, dif_neg ha]
    rw [density_eq]
    by_cases h : (y:ℝ) ∈ Zr ((actionIndex a ha).1 - 1) <;> simp [h]

open Classical in
lemma Hf_meas (z : ProbabilityMeasure State) (a : Action)
    (m : MeasurableSpace (ProbabilityMeasure State)) : @Measurable _ _ _ m (Hf z a) := by
  letI : MeasurableSpace (ProbabilityMeasure State) := m
  rcases Hf_cases z a with ⟨p, hp⟩ | ⟨S, p, q, hS, hpq⟩
  · rw [hp]; exact measurable_const
  · rw [hpq]; exact Measurable.ite hS measurable_const measurable_const

lemma isFilter_Hf : IsFilter transition observationKernel Hf :=
  ⟨fun z a => Hf_meas z a _, fun z a => Hf_meas z a _,
    fun z a B C _ hC => Hf_eq z a B C hC⟩


/-! ### Every filter agrees with `Hf` almost everywhere -/

lemma Rprime_univ (z : ProbabilityMeasure State) (a : Action) :
    Rprime transition observationKernel z a univ = 1 := by
  haveI := obs_markov
  rw [Rprime, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, R_apply z a univ univ MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one, measure_univ]
  rw [MeasureTheory.sum_measure_singleton, Finset.coe_univ, measure_univ]

lemma Rprime_fin (z : ProbabilityMeasure State) (a : Action) :
    IsFiniteMeasure (Rprime transition observationKernel z a) :=
  ⟨by rw [Rprime_univ]; exact ENNReal.one_lt_top⟩

attribute [local instance] Rprime_fin

lemma ae_eq_Hf (H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State)
    (hH : IsFilter transition observationKernel H) (z : ProbabilityMeasure State) (a : Action) :
    ∀ᵐ y ∂(Rprime transition observationKernel z a), H z a y = Hf z a y := by
  have key : ∀ x : State, ∀ᵐ y ∂(Rprime transition observationKernel z a),
      (H z a y : Measure State) {x} = (Hf z a y : Measure State) {x} := by
    intro x
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    · exact (Measure.measurable_coe (measurableSet_singleton x)).comp
        (measurable_subtype_coe.comp (hH.1 z a))
    · exact (Measure.measurable_coe (measurableSet_singleton x)).comp
        (measurable_subtype_coe.comp (isFilter_Hf.1 z a))
    · intro s hs _
      rw [← hH.2.2 z a {x} s (measurableSet_singleton x) hs,
        ← isFilter_Hf.2.2 z a {x} s (measurableSet_singleton x) hs]
  filter_upwards [ae_all_iff.2 key] with y hy
  exact Subtype.ext (Measure.ext_iff_singleton.2 hy)

/-! ### The test function -/

noncomputable def f0 : State →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => if x = 0 then 1 else 0, continuous_of_discreteTopology⟩

noncomputable def F (μ : ProbabilityMeasure State) : ℝ := ∫ x, f0 x ∂(μ : Measure State)

lemma F_cont : Continuous F := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f0

lemma F_eq (μ : ProbabilityMeasure State) : F μ = (μ : Measure State).real {0} := by
  rw [F, integral_fintype]
  · simp [f0]
  · exact f0.integrable _

lemma F_mem (μ : ProbabilityMeasure State) : 0 ≤ F μ ∧ F μ ≤ 1 := by
  rw [F_eq]; exact ⟨measureReal_nonneg, measureReal_le_one⟩

noncomputable def gt : ProbabilityMeasure State →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun μ => (F μ - 1/2)^2, (F_cont.sub continuous_const).pow 2⟩ 1
    (fun μ ν => by
      have h1 := F_mem μ; have h2 := F_mem ν
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]; constructor <;> nlinarith)

lemma gt_apply (μ : ProbabilityMeasure State) : gt μ = ((μ : Measure State).real {0} - 1/2)^2 := by
  rw [← F_eq]; rfl

lemma gt_nonneg (μ : ProbabilityMeasure State) : 0 ≤ gt μ := by rw [gt_apply]; positivity

lemma int_eq (H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State)
    (hH : IsFilter transition observationKernel H) (z : ProbabilityMeasure State) (a : Action)
    (g : ProbabilityMeasure State →ᵇ ℝ) :
    ∫ b, g b ∂(beliefTransition transition observationKernel H z a) =
      ∫ y, g (Hf z a y) ∂(Rprime transition observationKernel z a) := by
  letI : MeasurableSpace (ProbabilityMeasure State) := borel _
  haveI : BorelSpace (ProbabilityMeasure State) := ⟨rfl⟩
  rw [beliefTransition, integral_map (hH.2.1 z a).aemeasurable g.continuous.aestronglyMeasurable]
  exact integral_congr_ae ((ae_eq_Hf H hH z a).mono (fun y hy => congrArg g hy))

/-! ### Evaluation at the prior -/

lemma ofReal_half : ENNReal.ofReal 2⁻¹ = 2⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

lemma prior0 : (prior : Measure State) {0} = 2⁻¹ := by
  show bernoulliMeasure (0 : State) 1 ⟨1 / 2, by norm_num⟩ {0} = 2⁻¹
  rw [bernoulliMeasure_apply _ (measurableSet_singleton 0)]
  simp
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  exact ofReal_half

lemma prior1 : (prior : Measure State) {1} = 2⁻¹ := by
  show bernoulliMeasure (0 : State) 1 ⟨1 / 2, by norm_num⟩ {1} = 2⁻¹
  rw [bernoulliMeasure_apply _ (measurableSet_singleton 1)]
  simp
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  norm_num
  simpa [one_div] using ofReal_half

lemma post1_real : (post prior 1 : Measure State).real {0} = 1/2 := by
  have ht : tot prior 1 = 1 := by
    simp [tot, wt, Fin.sum_univ_two, prior0, prior1]
    done
  rw [measureReal_def, show (post prior 1 : Measure State) = postM prior 1 from rfl,
    postM_apply_of prior 1 (by rw [ht]; simp) (by rw [ht]; simp)]
  simp [ht, wt, Fin.sum_univ_two, prior0]

lemma post0_real : (post prior 0 : Measure State).real {0} = 1 := by
  have ht : tot prior 0 = 2⁻¹ := by
    simp [tot, wt, Fin.sum_univ_two, prior0, prior1]
  rw [measureReal_def, show (post prior 0 : Measure State) = postM prior 0 from rfl,
    postM_apply_of prior 0 (by rw [ht]; simp) (by rw [ht]; simp)]
  simp [ht, wt, Fin.sum_univ_two, prior0]

lemma val_zero : ∫ y, gt (Hf prior zeroAction y)
    ∂(Rprime transition observationKernel prior zeroAction) = 0 := by
  have : ∀ y, Hf prior zeroAction y = post prior 1 := fun y => by simp [Hf, q1, zeroAction]
  simp_rw [this, gt_apply, post1_real]
  simp

lemma Rprime_S (a : Action) (ha : a.1 ≠ 0) :
    (Rprime transition observationKernel prior a).real
      (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1)) = 1/4 := by
  haveI := nu_finite
  have hZ := measurableSet_Zr ((actionIndex a ha).1 - 1)
  have hS : MeasurableSet (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1) : Set Observation) :=
    hZ.preimage measurable_subtype_coe
  have hnu : nu (Zr ((actionIndex a ha).1 - 1)) = 2⁻¹ := by
    have h := nu_real_Zr ((actionIndex a ha).1 - 1)
    rw [measureReal_def] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top nu _), h, one_div]
    exact ofReal_half
  rw [measureReal_def, Rprime, Measure.map_apply measurable_snd hS,
    show Prod.snd ⁻¹' (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1) : Set Observation)
      = (univ : Set State) ×ˢ (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1)) by ext; simp,
    R_apply prior a univ _ hS, Fin.sum_univ_two, obs_state0, obs_ne a ha,
    vol_preimage _ hZ, dyadicLaw_apply _ _ hZ, sdiff_self, measure_empty, hnu, prior0, prior1]
  simp
  norm_num

lemma Hf_on_S (a : Action) (ha : a.1 ≠ 0) (y : Observation)
    (hy : y ∈ (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1) : Set Observation)) :
    Hf prior a y = post prior 0 := by
  simp only [Hf, q1, dif_neg ha]
  rw [density_eq, if_pos (show (y:ℝ) ∈ Zr ((actionIndex a ha).1 - 1) from hy)]

lemma val_ge (a : Action) (ha : a.1 ≠ 0) :
    1/16 ≤ ∫ y, gt (Hf prior a y) ∂(Rprime transition observationKernel prior a) := by
  have hS : MeasurableSet (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1) : Set Observation) :=
    (measurableSet_Zr _).preimage measurable_subtype_coe
  have hmeas : Measurable (fun y => gt (Hf prior a y)) := by
    letI : MeasurableSpace (ProbabilityMeasure State) := borel _
    haveI : BorelSpace (ProbabilityMeasure State) := ⟨rfl⟩
    exact gt.continuous.measurable.comp (Hf_meas prior a _)
  have hint : Integrable (fun y => gt (Hf prior a y)) (Rprime transition observationKernel prior a) :=
    Integrable.of_bound hmeas.aestronglyMeasurable ‖gt‖
      (Eventually.of_forall fun y => gt.norm_coe_le_norm _)
  calc (1:ℝ)/16 = ∫ y in (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1) : Set Observation),
          (1/4:ℝ) ∂(Rprime transition observationKernel prior a) := by
        rw [setIntegral_const, smul_eq_mul, Rprime_S a ha]; norm_num
    _ = ∫ y in (Subtype.val ⁻¹' Zr ((actionIndex a ha).1 - 1) : Set Observation),
          gt (Hf prior a y) ∂(Rprime transition observationKernel prior a) := by
        refine setIntegral_congr_fun hS (fun y hy => ?_)
        rw [Hf_on_S a ha y hy, gt_apply, post0_real]; norm_num
    _ ≤ _ := setIntegral_le_integral hint (Eventually.of_forall fun y => gt_nonneg _)

lemma recip_ne (k : ℕ) : (reciprocalAction ⟨k + 1, by omega⟩).1 ≠ 0 :=
  (show (0:ℝ) < 1 / ((k + 1 : ℕ) : ℝ) by positivity).ne'

lemma last_conj : ∀ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H →
      ∃ g : ProbabilityMeasure State →ᵇ ℝ,
        ¬ Tendsto
          (fun k : ℕ => ∫ b, g b ∂(beliefTransition transition observationKernel H prior
            (reciprocalAction ⟨k + 1, by omega⟩))) atTop
          (𝓝 (∫ b, g b ∂(beliefTransition transition observationKernel H prior zeroAction))) := by
  intro H hH
  refine ⟨gt, fun hT => ?_⟩
  rw [int_eq H hH prior zeroAction gt, val_zero] at hT
  have hge : ∀ k : ℕ, (1:ℝ)/16 ≤ ∫ b, gt b ∂(beliefTransition transition observationKernel H prior
      (reciprocalAction ⟨k + 1, by omega⟩)) := by
    intro k; rw [int_eq H hH]; exact val_ge _ (recip_ne k)
  have := ge_of_tendsto' hT hge
  norm_num at this

end FKZ41

open FeinbergPOMDP.Setwise MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction in
theorem solution :
    IsMarkovKernel observationKernel ∧
    TVContinuous (fun p : State × Action => transition p) ∧
    SetwiseContinuous (fun p : Action × State => observationKernel p) ∧
    Tendsto (fun k : ℕ => reciprocalAction ⟨k + 1, by omega⟩)
      atTop (𝓝 zeroAction) ∧
    (∃ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H) ∧
    ∀ H : ProbabilityMeasure State → Action → Observation → ProbabilityMeasure State,
      IsFilter transition observationKernel H →
      ∃ g : ProbabilityMeasure State →ᵇ ℝ,
        ¬ Tendsto
          (fun k : ℕ => ∫ b, g b ∂(beliefTransition transition observationKernel H prior
            (reciprocalAction ⟨k + 1, by omega⟩))) atTop
          (𝓝 (∫ b, g b ∂(beliefTransition transition observationKernel H prior zeroAction))) := by
  exact ⟨FKZ41.obs_markov, FKZ41.tv_cont, FKZ41.setwise_cont, FKZ41.recip_tendsto,
    ⟨FKZ41.Hf, FKZ41.isFilter_Hf⟩, FKZ41.last_conj⟩
