-- Prove2me | solution 1 for BoundedNV.Pooling.scale_comparison
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:51:04.480902+00:00
-- url     : https://prove2.me/submissions/c2208633-5d53-4873-a6b5-adf0773d6c92

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical
set_option autoImplicit false
open MeasureTheory ProbabilityTheory BoundedNV.Pooling

theorem BNP_demand_map (μ σ : ℝ) (hσ : 0 < σ) :
    InventoryControl.newsboyDemand μ σ = (gaussianReal 0 1).map (fun t => μ + σ * t) := by
  have h1 : (gaussianReal 0 1).map (fun t => μ + σ * t) =
      ((gaussianReal 0 1).map (σ * ·)).map (μ + ·) := by
    rw [Measure.map_map (measurable_const_add μ) (measurable_const_mul σ)]
    rfl
  rw [h1, gaussianReal_map_const_mul, gaussianReal_map_const_add]
  unfold InventoryControl.newsboyDemand
  congr 1
  · simp
  · apply NNReal.eq
    simp [Real.coe_toNNReal _ (sq_nonneg σ)]

theorem BNP_integrable_min (z : ℝ) : Integrable (fun t : ℝ => min t z) (gaussianReal 0 1) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  exact hid.inf (integrable_const z)

theorem BNP_int_id : ∫ t : ℝ, t ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

theorem BNP_m_le_zero (z : ℝ) : ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ 0 := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  calc ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ ∫ t : ℝ, t ∂(gaussianReal 0 1) :=
        integral_mono (BNP_integrable_min z) hid (fun t => min_le_left t z)
    _ = 0 := BNP_int_id

theorem BNP_m_le_z (z : ℝ) : ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ z := by
  calc ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ ∫ t : ℝ, z ∂(gaussianReal 0 1) :=
        integral_mono (BNP_integrable_min z) (integrable_const z) (fun t => min_le_right t z)
    _ = z := by simp

theorem BNP_m_ge (z : ℝ) :
    -(∫ t : ℝ, |t| ∂(gaussianReal 0 1) + |z|) ≤ ∫ t : ℝ, min t z ∂(gaussianReal 0 1) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  have hn : Integrable (fun t : ℝ => -|t|) (gaussianReal 0 1) := hid.abs.neg
  have h1 : Integrable (fun t : ℝ => -|t| - |z|) (gaussianReal 0 1) :=
    hn.sub (integrable_const _)
  have := integral_mono h1 (BNP_integrable_min z) (fun t => by
    exact le_min (by linarith [neg_abs_le t, abs_nonneg z]) (by linarith [neg_abs_le z, abs_nonneg t]))
  have e : ∫ t : ℝ, (-|t| - |z|) ∂(gaussianReal 0 1) =
      -(∫ t : ℝ, |t| ∂(gaussianReal 0 1)) - |z| := by
    rw [integral_sub hn (integrable_const _), integral_neg]; simp
  rw [e] at this
  linarith

theorem BNP_m_mono : Monotone (fun z : ℝ => ∫ t : ℝ, min t z ∂(gaussianReal 0 1)) := by
  intro z z' h
  exact integral_mono (BNP_integrable_min z) (BNP_integrable_min z') (fun t => min_le_min_left t h)

theorem BNP_Pi_meas (p c : ℝ) : Measurable (canonProfit p c) := by
  unfold canonProfit
  exact (measurable_const.mul BNP_m_mono.measurable).sub (measurable_const.mul measurable_id)

theorem BNP_Pi_le (p c : ℝ) (hc : 0 < c) (hcp : c < p) (z : ℝ) :
    canonProfit p c z ≤ -(min c (p - c)) * |z| := by
  unfold canonProfit
  have hm0 := BNP_m_le_zero z
  have hmz := BNP_m_le_z z
  have h1 : min c (p - c) ≤ c := min_le_left _ _
  have h2 : min c (p - c) ≤ p - c := min_le_right _ _
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) hz]
  · rw [abs_of_nonpos hz]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hz)]

theorem BNP_Pi_ge (p c : ℝ) (hc : 0 < c) (hcp : c < p) (z : ℝ) :
    -(canonProfit p c z) ≤ p * (∫ t : ℝ, |t| ∂(gaussianReal 0 1) + |z|) + c * |z| := by
  unfold canonProfit
  have := BNP_m_ge z
  nlinarith [neg_abs_le z, le_abs_self z]

theorem BNP_int_exp (k : ℝ) (hk : 0 < k) : Integrable (fun z : ℝ => Real.exp (-k * |z|)) := by
  have h1 : IntegrableOn (fun z : ℝ => Real.exp (-k * |z|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hk 0).congr_fun (fun z hz => ?_) measurableSet_Iic
    simp only [Set.mem_Iic] at hz
    simp only [abs_of_nonpos hz]; ring_nf
  have h2 : IntegrableOn (fun z : ℝ => Real.exp (-k * |z|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (by linarith : -k < 0) 0).congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only [Set.mem_Ioi] at hz
    simp only [abs_of_pos hz]
  have := h1.union h2
  rw [Set.Iic_union_Ioi] at this
  exact integrableOn_univ.1 this

theorem BNP_int_abs_exp (k : ℝ) (hk : 0 < k) : Integrable (fun z : ℝ => |z| * Real.exp (-k * |z|)) := by
  have hi := (BNP_int_exp (k / 2) (by linarith)).const_mul (2 / k)
  refine Integrable.mono' hi (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : k * |z| / 2 ≤ Real.exp (k * |z| / 2) := by
    have := Real.add_one_le_exp (k * |z| / 2); linarith
  have h2 : Real.exp (-k * |z|) = Real.exp (k * |z| / 2) ^ (-1 : ℤ) * Real.exp (-(k/2) * |z|) := by
    rw [zpow_neg_one, ← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have h3 : |z| ≤ (2 / k) * Real.exp (k * |z| / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk]; nlinarith
  calc |z| * Real.exp (-k * |z|) ≤ (2 / k) * Real.exp (k * |z| / 2) * Real.exp (-k * |z|) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / k) * Real.exp (-(k / 2) * |z|) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem BNP_integ (p c β s : ℝ) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β) (hs : 0 < s) :
    Integrable (fun z : ℝ => Real.exp (s * canonProfit p c z / β)) ∧
    Integrable (fun z : ℝ => canonProfit p c z * Real.exp (s * canonProfit p c z / β)) := by
  set κ := min c (p - c) with hκ
  have hκpos : 0 < κ := lt_min hc (by linarith)
  set k := s * κ / β with hk
  have hkpos : 0 < k := by positivity
  have hmeas : Measurable (fun z : ℝ => Real.exp (s * canonProfit p c z / β)) := by
    have := BNP_Pi_meas p c
    fun_prop
  have hbd : ∀ z : ℝ, Real.exp (s * canonProfit p c z / β) ≤ Real.exp (-k * |z|) := by
    intro z
    apply Real.exp_le_exp.2
    have := BNP_Pi_le p c hc hcp z
    rw [← hκ] at this
    have h3 : s * canonProfit p c z ≤ -(s * κ * |z|) := by
      nlinarith [mul_le_mul_of_nonneg_left this hs.le]
    calc s * canonProfit p c z / β ≤ -(s * κ * |z|) / β := div_le_div_of_nonneg_right h3 hβ.le
      _ = -k * |z| := by rw [hk]; field_simp
  have i1 : Integrable (fun z : ℝ => Real.exp (s * canonProfit p c z / β)) :=
    Integrable.mono' (BNP_int_exp k hkpos) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; exact hbd z)
  refine ⟨i1, ?_⟩
  set C := ∫ t : ℝ, |t| ∂(gaussianReal 0 1) with hC
  have hC0 : 0 ≤ C := integral_nonneg (fun t => abs_nonneg t)
  have hdom : Integrable (fun z : ℝ => (p * C) * Real.exp (-k * |z|) + (p + c) * (|z| * Real.exp (-k * |z|))) :=
    ((BNP_int_exp k hkpos).const_mul _).add ((BNP_int_abs_exp k hkpos).const_mul _)
  refine Integrable.mono' hdom ((BNP_Pi_meas p c).mul hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hPneg : canonProfit p c z ≤ 0 := by
    have := BNP_Pi_le p c hc hcp z
    nlinarith [abs_nonneg z]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonpos hPneg]
  have := BNP_Pi_ge p c hc hcp z
  have he := hbd z
  have hep := Real.exp_pos (s * canonProfit p c z / β)
  calc -canonProfit p c z * Real.exp (s * canonProfit p c z / β)
      ≤ (p * (C + |z|) + c * |z|) * Real.exp (-k * |z|) :=
        mul_le_mul this he hep.le (by nlinarith [abs_nonneg z])
    _ = _ := by ring

open MeasureTheory

/-- weighted Chebyshev-type core: integral over the product of the symmetrized integrand. -/
theorem BNS_cheb_core (μ : Measure ℝ) [SFinite μ] (g w1 w2 : ℝ → ℝ)
    (hw1 : Integrable w1 μ) (hw2 : Integrable w2 μ)
    (hg1 : Integrable (fun x => g x * w1 x) μ) (hg2 : Integrable (fun x => g x * w2 x) μ) :
    ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1) ∂(μ.prod μ) =
      2 * ((∫ x, g x * w1 x ∂μ) * (∫ x, w2 x ∂μ) - (∫ x, g x * w2 x ∂μ) * (∫ x, w1 x ∂μ)) ∧
    Integrable (fun z : ℝ × ℝ => (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1)) (μ.prod μ) := by
  have e : (fun z : ℝ × ℝ => (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1)) =
      fun z => ((g z.1 * w1 z.1) * w2 z.2 - (g z.1 * w2 z.1) * w1 z.2) +
        (-(w1 z.1 * (g z.2 * w2 z.2)) + w2 z.1 * (g z.2 * w1 z.2)) := by
    funext z; ring
  have i1 : Integrable (fun z : ℝ × ℝ => (g z.1 * w1 z.1) * w2 z.2) (μ.prod μ) := hg1.mul_prod hw2
  have i2 : Integrable (fun z : ℝ × ℝ => (g z.1 * w2 z.1) * w1 z.2) (μ.prod μ) := hg2.mul_prod hw1
  have i3 : Integrable (fun z : ℝ × ℝ => w1 z.1 * (g z.2 * w2 z.2)) (μ.prod μ) := hw1.mul_prod hg2
  have i4 : Integrable (fun z : ℝ × ℝ => w2 z.1 * (g z.2 * w1 z.2)) (μ.prod μ) := hw2.mul_prod hg1
  have i12 : Integrable (fun z : ℝ × ℝ => (g z.1 * w1 z.1) * w2 z.2 - (g z.1 * w2 z.1) * w1 z.2)
      (μ.prod μ) := i1.sub i2
  have i34 : Integrable (fun z : ℝ × ℝ => -(w1 z.1 * (g z.2 * w2 z.2)) + w2 z.1 * (g z.2 * w1 z.2))
      (μ.prod μ) := i3.neg.add i4
  have i3n : Integrable (fun z : ℝ × ℝ => -(w1 z.1 * (g z.2 * w2 z.2))) (μ.prod μ) := i3.neg
  rw [e]
  refine ⟨?_, i12.add i34⟩
  have p1 : ∫ z : ℝ × ℝ, (g z.1 * w1 z.1) * w2 z.2 ∂(μ.prod μ) =
      (∫ x, g x * w1 x ∂μ) * ∫ x, w2 x ∂μ := integral_prod_mul (fun x => g x * w1 x) w2
  have p2 : ∫ z : ℝ × ℝ, (g z.1 * w2 z.1) * w1 z.2 ∂(μ.prod μ) =
      (∫ x, g x * w2 x ∂μ) * ∫ x, w1 x ∂μ := integral_prod_mul (fun x => g x * w2 x) w1
  have p3 : ∫ z : ℝ × ℝ, w1 z.1 * (g z.2 * w2 z.2) ∂(μ.prod μ) =
      (∫ x, w1 x ∂μ) * ∫ x, g x * w2 x ∂μ := integral_prod_mul w1 (fun x => g x * w2 x)
  have p4 : ∫ z : ℝ × ℝ, w2 z.1 * (g z.2 * w1 z.2) ∂(μ.prod μ) =
      (∫ x, w2 x ∂μ) * ∫ x, g x * w1 x ∂μ := integral_prod_mul w2 (fun x => g x * w1 x)
  rw [integral_add i12 i34, integral_sub i1 i2, integral_add i3n i4,
    integral_neg, p1, p2, p3, p4]
  ring

theorem BNS_pt (π g : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hg : ∀ x y, π x ≤ π y → g x ≤ g y) (x y : ℝ) :
    0 ≤ (g x - g y) * (Real.exp (t1 * π x) * Real.exp (t2 * π y) -
      Real.exp (t1 * π y) * Real.exp (t2 * π x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rcases le_total (π x) (π y) with h | h
  · have h1 := hg x y h
    have h2 : Real.exp (t1 * π x + t2 * π y) ≤ Real.exp (t1 * π y + t2 * π x) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 := hg y x h
    have h2 : Real.exp (t1 * π y + t2 * π x) ≤ Real.exp (t1 * π x + t2 * π y) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_nonneg (by linarith) (by linarith)

theorem BNS_pt_strict (π : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1) (x y : ℝ) (hxy : π x ≠ π y) :
    0 < (π x - π y) * (Real.exp (t1 * π x) * Real.exp (t2 * π y) -
      Real.exp (t1 * π y) * Real.exp (t2 * π x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rcases lt_or_gt_of_ne hxy with h | h
  · have h2 : Real.exp (t1 * π x + t2 * π y) < Real.exp (t1 * π y + t2 * π x) :=
      Real.exp_lt_exp.2 (by nlinarith)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h2 : Real.exp (t1 * π y + t2 * π x) < Real.exp (t1 * π x + t2 * π y) :=
      Real.exp_lt_exp.2 (by nlinarith)
    exact mul_pos (by linarith) (by linarith)

theorem BNS_cheb (μ : Measure ℝ) [SFinite μ] (π g : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hπ : Measurable π) (hgm : Measurable g)
    (hg : ∀ x y, π x ≤ π y → g x ≤ g y)
    (hw1 : Integrable (fun x => Real.exp (t1 * π x)) μ) (hw2 : Integrable (fun x => Real.exp (t2 * π x)) μ)
    (hg1 : Integrable (fun x => g x * Real.exp (t1 * π x)) μ)
    (hg2 : Integrable (fun x => g x * Real.exp (t2 * π x)) μ) :
    (∫ x, g x * Real.exp (t2 * π x) ∂μ) * (∫ x, Real.exp (t1 * π x) ∂μ) ≤
      (∫ x, g x * Real.exp (t1 * π x) ∂μ) * (∫ x, Real.exp (t2 * π x) ∂μ) := by
  obtain ⟨h1, h2⟩ := BNS_cheb_core μ g _ _ hw1 hw2 hg1 hg2
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) := by
    refine integral_nonneg fun z => ?_
    exact BNS_pt π g t1 t2 ht hg z.1 z.2
  linarith


theorem BNS_e1 (lam β : ℝ) (π : ℝ → ℝ) (x : ℝ) :
    Real.exp (lam * π x / β) = Real.exp ((lam / β) * π x) := by
  congr 1; ring

theorem BNS_strict (μ : Measure ℝ) [SFinite μ] (π : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hw1 : Integrable (fun x => Real.exp (t1 * π x)) μ)
    (hw2 : Integrable (fun x => Real.exp (t2 * π x)) μ)
    (hg1 : Integrable (fun x => π x * Real.exp (t1 * π x)) μ)
    (hg2 : Integrable (fun x => π x * Real.exp (t2 * π x)) μ)
    (hnc : ¬ ∃ k : ℝ, ∀ᵐ x ∂μ, π x = k) :
    (∫ x, π x * Real.exp (t2 * π x) ∂μ) * (∫ x, Real.exp (t1 * π x) ∂μ) <
      (∫ x, π x * Real.exp (t1 * π x) ∂μ) * (∫ x, Real.exp (t2 * π x) ∂μ) := by
  obtain ⟨h1, h2⟩ := BNS_cheb_core μ π _ _ hw1 hw2 hg1 hg2
  have hF : ∀ z : ℝ × ℝ, 0 ≤ (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) := fun z =>
    BNS_pt π π t1 t2 ht (fun x y h => h) z.1 z.2
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) := integral_nonneg hF
  by_contra hcon
  push_neg at hcon
  have hI : ∫ z : ℝ × ℝ, (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (μ := μ.prod μ) hF h2).1 hI
  have hae2 : ∀ᵐ z ∂(μ.prod μ), π z.1 = π z.2 := by
    filter_upwards [hae] with z hz
    by_contra hne
    have := BNS_pt_strict π t1 t2 ht z.1 z.2 hne
    simp only [Pi.zero_apply] at hz
    linarith
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  have : μ ≠ 0 := by
    rintro rfl
    exact hnc ⟨0, by simp⟩
  haveI : NeZero μ := ⟨this⟩
  obtain ⟨x0, hx0⟩ := hae3.exists
  exact hnc ⟨π x0, by filter_upwards [hx0] with y hy using hy.symm⟩


theorem BNP_mean_eq (S : Set ℝ) (hS : MeasurableSet S) (u : ℝ → ℝ) (β : ℝ) (g : ℝ → ℝ) :
    logitExp S u β g =
      (∫ v in S, g v * Real.exp (u v / β)) / ∫ v in S, Real.exp (u v / β) := by
  unfold logitExp logitDensity
  have e : ∀ y, g y * S.indicator (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y =
      S.indicator (fun y => g y * Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y := by
    intro y
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy]; ring
    · simp [Set.indicator_of_notMem hy]
  simp_rw [e]
  rw [integral_indicator hS, integral_div]

theorem BNP_scale_strict (p c β s s' : ℝ) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β)
    (hs : 0 < s) (hss' : s < s') :
    centeredExpectedProfit p c β s < centeredExpectedProfit p c β s' := by
  unfold centeredExpectedProfit
  rw [BNP_mean_eq _ MeasurableSet.univ, BNP_mean_eq _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  obtain ⟨i1, m1⟩ := BNP_integ p c β s' hc hcp hβ (by linarith)
  obtain ⟨i2, m2⟩ := BNP_integ p c β s hc hcp hβ hs
  have e1 : ∀ (t : ℝ) (z : ℝ), Real.exp (t * canonProfit p c z / β) = Real.exp ((t / β) * canonProfit p c z) :=
    fun t z => by congr 1; ring
  simp only [e1] at i1 i2 m1 m2 ⊢
  have hZ1 := integral_exp_pos i1
  have hZ2 := integral_exp_pos i2
  have ht : s / β < s' / β := div_lt_div_of_pos_right hss' hβ
  have hnc : ¬ ∃ k : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), canonProfit p c x = k := by
    rintro ⟨k, hk⟩
    have hκ : 0 < min c (p - c) := lt_min hc (by linarith)
    set r : ℝ := |k| / min c (p - c) with hr
    have hsub : ∀ᵐ x ∂(volume : Measure ℝ), ¬ (r < x) := by
      filter_upwards [hk] with x hx hrx
      have h1 := BNP_Pi_le p c hc hcp x
      have h2 : |k| < min c (p - c) * |x| := by
        have : r * min c (p - c) < x * min c (p - c) := mul_lt_mul_of_pos_right hrx hκ
        have h3 : r * min c (p - c) = |k| := by rw [hr]; field_simp
        have h4 : x ≤ |x| := le_abs_self x
        nlinarith
      have h5 := neg_abs_le k
      rw [hx] at h1
      nlinarith [abs_nonneg k, le_abs_self k]
    have h0 : volume (Set.Ioi r) = 0 := by
      have := ae_iff.1 hsub
      simpa [Set.Ioi] using this
    simp at h0
  have key := BNS_strict (volume : Measure ℝ) (canonProfit p c) (s' / β) (s / β) ht i1 i2 m1 m2 hnc
  rw [div_lt_div_iff₀ hZ2 hZ1]
  exact key

theorem solution (p c β s s' : ℝ)
    (hc : 0 < c) (hcp : c < p) (hβ : 0 < β)
    (hs : 0 < s) (hss' : s ≤ s') :
    centeredExpectedProfit p c β s ≤ centeredExpectedProfit p c β s' ∧
      (centeredExpectedProfit p c β s = centeredExpectedProfit p c β s' ↔ s = s') := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hss' with h | h
    · rw [h]
    · exact (BNP_scale_strict p c β s s' hc hcp hβ hs h).le
  · constructor
    · intro h
      by_contra hne
      have := BNP_scale_strict p c β s s' hc hcp hβ hs (lt_of_le_of_ne hss' hne)
      linarith
    · intro h; rw [h]

