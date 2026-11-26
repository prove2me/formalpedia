-- Prove2me | solution 1 for BranchActualQ.nonnegative_from_verified_height
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-18T09:44:59.01865+00:00
-- url     : https://prove2.me/submissions/5e600c4a-8b5d-4050-bd59-f64551621284

import Theorems.Thm_XiQuantitativePublished_concrete_upper_zero_anchor
import Theorems.Thm_BranchActualCount_strict_and_window_occurrence_count_exact
import Theorems.Thm_BranchActualCount_unit_window_bound
import Mathlib
import Theorems.Thm_XiPairingPublished_concrete_G_zero_product
import Theorems.Thm_XiQuantitativePublished_concrete_upper_zero_lower
import Theorems.Thm_BranchActualCount_original_occurrence_sublinear_bound
import Theorems.Thm_BranchActualCount_original_occurrence_uniform_small_scale_positive
set_option maxHeartbeats 1600000
open Set Filter Topology
namespace EtaQBridge

-- This definition includes the removable values at s = 0 and s = 1.
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

theorem xi_differentiable : Differentiable ℂ xi := by
  have hz := differentiable_completedZeta₀
  unfold xi
  fun_prop

theorem xi_functional_equation (s : ℂ) : xi (1-s) = xi s := by
  simp only [xi, completedRiemannZeta₀_one_sub]
  ring

theorem xi_centered_even (u : ℂ) : xi (1/2-u) = xi (1/2+u) := by
  convert xi_functional_equation (1/2+u) using 1 <;> congr 1 <;> ring

theorem xi_eq_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s-1) * completedRiemannZeta s / 2 := by
  rw [completedRiemannZeta_eq]
  unfold xi
  have h : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  <;> ring

theorem xi_eq_zeta (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s-1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hr
  field_simp


end EtaQBridge

namespace XiZeroGeometry
open EtaQBridge Set

theorem xi_zero_value : xi 0 = 1/2 := by simp [xi]
theorem xi_one_value : xi 1 = 1/2 := by simp [xi]

theorem xi_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, xi_one_value]; norm_num
  have hr : 0 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  rw [xi_eq_zeta s hr h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0
    (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hr))
    (riemannZeta_ne_zero_of_one_le_re hs)) (by norm_num)

theorem xi_ne_zero_left (s : ℂ) (hs : s.re ≤ 0) : xi s ≠ 0 := by
  rw [← xi_functional_equation s]
  apply xi_ne_zero_right
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem xi_zero_iff (s : ℂ) :
    xi s = 0 ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 := by
  constructor
  · intro hx
    have hr : 0 < s.re := lt_of_not_ge (fun h => xi_ne_zero_left s h hx)
    have hl : s.re < 1 := lt_of_not_ge (fun h => xi_ne_zero_right s h hx)
    have h0 : s ≠ 0 := by intro h; simp [h] at hr
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1] at hx
    have hz : riemannZeta s = 0 := by
      rcases (div_eq_zero_iff).mp hx with hh | hh
      · exact (mul_eq_zero.mp hh).resolve_left
          (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
            (Complex.Gammaℝ_ne_zero_of_re_pos hr))
      · norm_num at hh
    exact ⟨hz, hr, hl⟩
  · rintro ⟨hz, hr, hl⟩
    have h1 : s ≠ 1 := by intro h; simp [h] at hl
    rw [xi_eq_zeta s hr h1, hz]
    ring

theorem xi_zero_reflection (s : ℂ) : xi (1-s) = 0 ↔ xi s = 0 := by
  rw [xi_functional_equation]

theorem xi_zeros_compact_finite (S : Set ℂ) (hS : IsCompact S) :
    (S ∩ {s | xi s = 0}).Finite := by
  apply hS.inter_riemannZetaZeros_finite.subset
  intro s hs
  exact ⟨hs.1, (xi_zero_iff s).mp hs.2 |>.1⟩

theorem centered_zero_strip (s : ℂ) (hs : xi s = 0) : |s.re - 1/2| < 1/2 := by
  have h := (xi_zero_iff s).mp hs
  rw [abs_lt]
  constructor <;> linarith [h.2.1, h.2.2]

end XiZeroGeometry

namespace XiMultiplicity
open EtaQBridge Set Filter Topology

theorem xi_analytic (s : ℂ) : AnalyticAt ℂ xi s := xi_differentiable.analyticAt s

theorem xi_order_finite (s : ℂ) : analyticOrderAt xi s ≠ ⊤ := by
  intro h
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s xi_analytic).mp h
  have hh := congrFun hz 0
  rw [XiZeroGeometry.xi_zero_value] at hh
  norm_num at hh

theorem xi_multiplicity_pos (s : ℂ) (hs : xi s = 0) :
    0 < analyticOrderNatAt xi s := by
  exact ENat.toNat_pos ((xi_analytic s).analyticOrderAt_ne_zero.mpr hs) (xi_order_finite s)

theorem xi_zeta_order_eq (s : ℂ) (hr : 0 < s.re) (h1 : s ≠ 1) :
    analyticOrderAt xi s = analyticOrderAt riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hg0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have hg : AnalyticAt ℂ Complex.Gammaℝ s := by
    have hh := (Complex.differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hg0)
    simpa only [Pi.inv_def, inv_inv] using hh
  let a : ℂ → ℂ := fun z => z*(z-1)*Complex.Gammaℝ z/2
  have ha : AnalyticAt ℂ a s := by
    dsimp [a]
    exact ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hg).div_const
  have ha0 : a s ≠ 0 := div_ne_zero
    (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hg0) (by norm_num)
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s h1
  have he : xi =ᶠ[𝓝 s] a*riemannZeta := by
    have hR : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hr
    filter_upwards [hR, eventually_ne_nhds h1] with z hz hz1
    rw [xi_eq_zeta z hz hz1]
    simp only [Pi.mul_apply, a]
    ring
  rw [analyticOrderAt_congr he, analyticOrderAt_mul ha hz,
    ha.analyticOrderAt_eq_zero.mpr ha0, zero_add]

theorem xi_zeta_multiplicity_eq (s : ℂ) (hs : xi s = 0) :
    analyticOrderNatAt xi s = analyticOrderNatAt riemannZeta s := by
  have h := (XiZeroGeometry.xi_zero_iff s).mp hs
  have h1 : s ≠ 1 := by intro he; simp [he] at h
  unfold analyticOrderNatAt
  rw [xi_zeta_order_eq s h.2.1 h1]

theorem xi_zero_set_countable : {s : ℂ | xi s = 0}.Countable := by
  have hc : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ) ∩ {s | xi s = 0}).Countable :=
    Set.countable_iUnion (fun n =>
      (XiZeroGeometry.xi_zeros_compact_finite _ (isCompact_closedBall _ _)).countable)
  apply hc.mono
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_gt ‖s‖
  exact mem_iUnion.mpr ⟨n, ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hn.le, hs⟩⟩

def UpperZero := {s : ℂ // xi s = 0 ∧ 0 < s.im}

instance upperZero_countable : Countable UpperZero :=
  (xi_zero_set_countable.mono (fun s hs => hs.1)).to_subtype

def Occurrence := (s : UpperZero) × Fin (analyticOrderNatAt xi s.val)

instance occurrence_countable : Countable Occurrence := by
  unfold Occurrence
  infer_instance

def location (z : Occurrence) : ℂ := z.1.val

theorem occurrence_location (z : Occurrence) :
    riemannZeta (location z) = 0 ∧ 0 < (location z).re ∧
      (location z).re < 1 ∧ 0 < (location z).im := by
  have h := (XiZeroGeometry.xi_zero_iff z.1.val).mp z.1.property.1
  exact ⟨h.1, h.2.1, h.2.2, z.1.property.2⟩

theorem every_upper_zero_occurs (s : ℂ) (hz : riemannZeta s = 0)
    (hr : 0 < s.re) (hl : s.re < 1) (hi : 0 < s.im) :
    ∃ z : Occurrence, location z = s := by
  have hx := (XiZeroGeometry.xi_zero_iff s).mpr ⟨hz,hr,hl⟩
  exact ⟨⟨⟨s,hx,hi⟩,⟨0,xi_multiplicity_pos s hx⟩⟩,rfl⟩

def fiberEquiv (s : UpperZero) : {z : Occurrence // z.1 = s} ≃
    Fin (analyticOrderNatAt xi s.val) where
  toFun z := z.property ▸ z.val.2
  invFun k := ⟨⟨s,k⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨v,k⟩,h⟩
    dsimp at h
    subst v
    rfl
  right_inv := by intro k; rfl

theorem fiber_card (s : UpperZero) :
    Nat.card {z : Occurrence // z.1 = s} = analyticOrderNatAt riemannZeta s.val := by
  rw [Nat.card_congr (fiberEquiv s), Nat.card_fin,
    xi_zeta_multiplicity_eq s.val s.property.1]

theorem occurrences_compact_finite (K : Set ℂ) (hK : IsCompact K) :
    {z : Occurrence | location z ∈ K}.Finite := by
  have hf : {s : UpperZero | s.val ∈ K}.Finite := by
    have hh := Set.Finite.preimage (f := fun s : UpperZero => s.val)
      (fun _ _ _ _ h => Subtype.ext h) (XiZeroGeometry.xi_zeros_compact_finite K hK)
    exact hh.subset (fun s hs => ⟨hs,s.property.1⟩)
  have hfi (s : UpperZero) : {z : Occurrence | z.1 = s}.Finite := by
    exact Set.finite_coe_iff.mp (Finite.of_equiv
      (Fin (analyticOrderNatAt xi s.val)) (fiberEquiv s).symm)
  apply (hf.biUnion (fun s _ => hfi s)).subset
  intro z hz
  exact mem_iUnion.mpr ⟨z.1,mem_iUnion.mpr ⟨hz,rfl⟩⟩

theorem occurrences_bounded_height_finite (T : ℝ) :
    {z : Occurrence | (location z).im ≤ T}.Finite := by
  apply (occurrences_compact_finite (Metric.closedBall 0 (|T|+1))
    (isCompact_closedBall _ _)).subset
  intro z hz
  have h := occurrence_location z
  rw [mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  calc
    ‖location z‖ ≤ |(location z).re|+|(location z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |T|+1 := by rw [abs_of_pos h.2.1, abs_of_pos h.2.2.2]; linarith [h.2.2.1, (show (location z).im ≤ T from hz), le_abs_self T]

theorem occurrence_indexing : ∃ code : Occurrence → ℕ, Function.Injective code :=
  Countable.exists_injective_nat Occurrence

def locationFiberEquiv (s : UpperZero) :
    {z : Occurrence // location z = s.val} ≃ {z : Occurrence // z.1 = s} where
  toFun z := ⟨z.val, Subtype.ext z.property⟩
  invFun z := ⟨z.val, congrArg Subtype.val z.property⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl

theorem complete_countable_zero_index :
    ∃ I : Type, Countable I ∧ ∃ rho : I → ℂ,
      (∀ s : ℂ, (∃ i, rho i = s) ↔
        riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im) ∧
      (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 < s.im →
        Nat.card {i : I // rho i = s} = analyticOrderNatAt riemannZeta s) ∧
      (∀ T : ℝ, {i : I | (rho i).im ≤ T}.Finite) := by
  refine ⟨Occurrence, inferInstance, location, ?_, ?_, occurrences_bounded_height_finite⟩
  · intro s
    constructor
    · rintro ⟨i,rfl⟩
      exact occurrence_location i
    · rintro ⟨hz,hr,hl,hi⟩
      exact every_upper_zero_occurs s hz hr hl hi
  · intro s hz hr hl hi
    let v : UpperZero := ⟨s,(XiZeroGeometry.xi_zero_iff s).mpr ⟨hz,hr,hl⟩,hi⟩
    exact (Nat.card_congr (locationFiberEquiv v)).trans (fiber_card v)

theorem xi_meromorphic_order (s : ℂ) :
    meromorphicOrderAt xi s = ((analyticOrderNatAt xi s : ℕ) : WithTop ℤ) := by
  rw [(xi_analytic s).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (xi_order_finite s)]
  simp

end XiMultiplicity

section QBridgeGeneric
universe u
variable {ι : Type u} [Countable ι]
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace ReciprocalCounting

theorem indicator_integrable (a : ℝ) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ))) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).indicator measurableSet_Ioi

theorem indicator_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ y : ℝ in Ioi 1, (Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ)) y) = a⁻¹ := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  have hh := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (show 0 < a by linarith)
  simpa only [show (-2 : ℝ)+1 = -1 by norm_num, Real.rpow_neg_one,
    div_neg, div_one, neg_neg] using hh

theorem summable_inverse_from_sublinear_count (a : ι → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by
  classical
  have hi : IntegrableOn (fun y : ℝ => C*y^(r-2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : r-2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C
  have hb (F : Finset ι) : (∑ j ∈ F, (a j)⁻¹) ≤ C/(1-r) := by
    calc
      _ = ∑ j ∈ F, ∫ y : ℝ in Ioi 1,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (indicator_integral (a j) (ha j)).symm
      _ = ∫ y : ℝ in Ioi 1, ∑ j ∈ F,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y :=
        (integral_finsetSum F (fun j _ => indicator_integrable (a j))).symm
      _ ≤ ∫ y : ℝ in Ioi 1, C*y^(r-2) := by
        apply integral_mono_ae (integrable_finset_sum F (fun j _ => indicator_integrable (a j))) hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy1 : 1 ≤ y := (mem_Ioi.mp hy).le
        have hy0 : 0 ≤ y := by linarith
        have he : (∑ j ∈ F, (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y) =
            ((F.filter (fun j => a j < y)).card : ℝ)*y^(-2 : ℝ) := by
          simp only [Set.indicator, mem_Ioi]
          rw [← Finset.sum_filter]
          simp
        rw [he]
        have hc := hcount y hy1 (F.filter (fun j => a j < y))
          (fun j hj => (Finset.mem_filter.mp hj).2.le)
        calc
          _ ≤ (C*y^r)*y^(-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hy0 _)
          _ = C*y^(r-2) := by rw [mul_assoc, ← Real.rpow_add (show 0 < y by linarith)]; congr 2 <;> ring
      _ = C/(1-r) := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : r-2 < -1) (by norm_num)]
        rw [show r-2+1 = -(1-r) by ring]
        simp only [Real.one_rpow, div_neg, neg_neg, one_div]
        ring
  have hs := summable_of_sum_le (fun j => inv_nonneg.mpr (by linarith [ha j])) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end ReciprocalCounting



open scoped BigOperators
open Set Filter Topology
namespace HadamardSeries

def domain : Set ℂ := {z | -(1/2 : ℝ) < z.re}

theorem domain_open : IsOpen domain :=
  isOpen_lt continuous_const Complex.continuous_re

theorem domain_convex : Convex ℝ domain := by
  intro x hx y hy a b ha hb hab
  change -(1/2 : ℝ) < (a • x + b • y).re
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  change -(1/2 : ℝ) < x.re at hx
  change -(1/2 : ℝ) < y.re at hy
  by_cases h : a = 0
  · subst a
    have hbb : b = 1 := by linarith
    simpa [hbb] using hy
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    nlinarith [mul_pos hap (show 0 < x.re+1/2 by linarith),
      mul_nonneg hb (show 0 ≤ y.re+1/2 by linarith)]

theorem zero_mem : (0 : ℂ) ∈ domain := by norm_num [domain]

theorem realpart_pos (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    0 < (z+B).re := by
  change -(1/2 : ℝ) < z.re at hz
  simp only [Complex.add_re]
  linarith

theorem denominator_nonzero (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    z+B ≠ 0 := by
  have hp := realpart_pos B z hB hz
  intro h
  simp [h] at hp

theorem inverse_bound (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    ‖(z+B)⁻¹‖ ≤ 2 * B.re⁻¹ := by
  have hb : 0 < B.re := by linarith
  have hd : B.re/2 ≤ ‖z+B‖ := by
    have hr := Complex.re_le_norm (z+B)
    change -(1/2 : ℝ) < z.re at hz
    simp only [Complex.add_re] at hr
    linarith
  rw [norm_inv]
  calc
    ‖z+B‖⁻¹ ≤ (B.re/2)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0 < B.re/2) hd) (by positivity)).2 hd
    _ = 2 * B.re⁻¹ := by field_simp

theorem inverse_power_bound (B z : ℂ) (r : ℕ)
    (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    ‖((z+B)⁻¹)^(r+1)‖ ≤ 2^(r+1) * B.re⁻¹ := by
  have hb : 0 ≤ B.re⁻¹ := inv_nonneg.mpr (by linarith)
  have hle : B.re⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hB
  have hp : (B.re⁻¹)^r ≤ 1 := pow_le_one₀ hb hle
  rw [norm_pow]
  calc
    ‖(z+B)⁻¹‖^(r+1) ≤ (2*B.re⁻¹)^(r+1) :=
      pow_le_pow_left₀ (norm_nonneg _) (inverse_bound B z hB hz) _
    _ = 2^(r+1) * ((B.re⁻¹)^r * B.re⁻¹) := by rw [mul_pow, pow_succ (B.re⁻¹)]
    _ ≤ 2^(r+1) * B.re⁻¹ := mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul_of_nonneg_right hp hb) (by positivity)

theorem pole_power_summable (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    Summable (fun i => ((z+B i)⁻¹)^(r+1)) := by
  exact (hs.mul_left (2^(r+1))).of_norm_bounded
    (fun i => inverse_power_bound (B i) z r (hB i) hz)

theorem log_atom_derivative (B z : ℂ) (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    HasDerivAt (fun w => Complex.log (w+B) - Complex.log B) ((z+B)⁻¹) z := by
  have hd := (Complex.hasDerivAt_log (by
    exact Or.inl (realpart_pos B z hB hz))).comp z ((hasDerivAt_id z).add_const B)
  simpa using hd.sub_const (Complex.log B)

theorem log_series_derivative (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∑' i, (Complex.log (w+B i) - Complex.log (B i)))
      (∑' i, (z+B i)⁻¹) z := by
  apply hasDerivAt_tsum_of_isPreconnected (hs.mul_left 2)
    domain_open domain_convex.isPreconnected
    (fun i w hw => log_atom_derivative (B i) w (hB i) hw)
    (fun i w hw => inverse_bound (B i) w (hB i) hw) zero_mem
  · simp
  · exact hz

theorem log_series_summable (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    Summable (fun i => Complex.log (z+B i) - Complex.log (B i)) := by
  apply summable_of_summable_hasDerivAt_of_isPreconnected (hs.mul_left 2)
    domain_open domain_convex.isPreconnected
    (fun i w hw => log_atom_derivative (B i) w (hB i) hw)
    (fun i w hw => inverse_bound (B i) w (hB i) hw) zero_mem
  · simp
  · exact hz

theorem canonical_product_hasProd (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasProd (fun i => 1+z/B i)
      (Complex.exp (∑' i, (Complex.log (z+B i) - Complex.log (B i)))) := by
  have hsum := (log_series_summable B hB hs z hz).hasSum
  have ht := (Complex.continuous_exp.tendsto _).comp hsum
  have hterm : ∀ i, Complex.exp (Complex.log (z+B i) - Complex.log (B i)) = 1+z/B i := by
    intro i
    have hb : B i ≠ 0 := by
      have := hB i
      intro he
      norm_num [he] at this
    rw [Complex.exp_sub, Complex.exp_log (denominator_nonzero _ _ (hB i) hz),
      Complex.exp_log hb]
    field_simp
    ring
  simpa only [HasProd, Function.comp_def, Complex.exp_sum, hterm] using ht

theorem canonical_product_eq_exp (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    (∏' i, (1+z/B i)) =
      Complex.exp (∑' i, (Complex.log (z+B i) - Complex.log (B i))) :=
  (canonical_product_hasProd B hB hs z hz).tprod_eq

theorem canonical_product_derivative (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∏' i, (1+w/B i))
      ((∏' i, (1+z/B i)) * ∑' i, (z+B i)⁻¹) z := by
  have hd := (Complex.hasDerivAt_exp _).comp z (log_series_derivative B hB hs z hz)
  rw [← canonical_product_eq_exp B hB hs z hz] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [domain_open.mem_nhds hz] with w hw
  exact canonical_product_eq_exp B hB hs w hw

theorem pole_atom_derivative (B z : ℂ) (r : ℕ)
    (hB : 1 ≤ B.re) (hz : z ∈ domain) :
    HasDerivAt (fun w => ((w+B)⁻¹)^(r+1))
      (-((r+1 : ℕ) : ℂ) * ((z+B)⁻¹)^(r+2)) z := by
  have hd := (((hasDerivAt_id z).add_const B).inv
    (denominator_nonzero B z hB hz)).pow (r+1)
  convert! hd using 1 <;>
    simp [Nat.add_sub_cancel, one_div, div_eq_mul_inv, inv_pow, pow_succ] <;> ring

theorem pole_series_derivative (B : ι → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : z ∈ domain) :
    HasDerivAt (fun w => ∑' i, ((w+B i)⁻¹)^(r+1))
      (-((r+1 : ℕ) : ℂ) * ∑' i, ((z+B i)⁻¹)^(r+2)) z := by
  have hbound : ∀ i w, w ∈ domain →
      ‖-((r+1 : ℕ) : ℂ) * ((w+B i)⁻¹)^(r+2)‖ ≤
        ((r+1 : ℕ) : ℝ) * 2^(r+2) * (B i).re⁻¹ := by
    intro i w hw
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (inverse_power_bound (B i) w (r+1) (hB i) hw) (Nat.cast_nonneg _)
  have hd := hasDerivAt_tsum_of_isPreconnected
    (hs.mul_left (((r+1 : ℕ) : ℝ)*2^(r+2))) domain_open domain_convex.isPreconnected
    (fun i w hw => pole_atom_derivative (B i) w r (hB i) hw) hbound
    zero_mem (pole_power_summable B r hB hs 0 zero_mem) hz
  simpa only [tsum_mul_left] using hd

theorem log_series_iteratedDeriv (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (z : ℂ) (hz : z ∈ domain) :
    iteratedDeriv (r+1) (fun w => ∑' i,
      (Complex.log (w+B i) - Complex.log (B i))) z =
      (-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, ((z+B i)⁻¹)^(r+1) := by
  induction r generalizing z with
  | zero =>
    simpa using (log_series_derivative B hB hs z hz).deriv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (r+1) (fun w => ∑' i,
        (Complex.log (w+B i) - Complex.log (B i))) =ᶠ[𝓝 z]
        (fun w => (-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, ((w+B i)⁻¹)^(r+1)) := by
      filter_upwards [domain_open.mem_nhds hz] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    rw [((pole_series_derivative B r hB hs z hz).const_mul
      ((-1 : ℂ)^r * (r.factorial : ℂ))).deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

end HadamardSeries


open MeasureTheory Set Filter Topology
namespace CanonicalQBridge
theorem real_log_iteratedDeriv (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (r : ℕ) (x : ℝ) (hx : -(1/2 : ℝ) < x) :
    iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
      (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) x =
      ((-1 : ℂ)^r * (r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re := by
  have hz : (x : ℂ) ∈ HadamardSeries.domain := hx
  induction r generalizing x with
  | zero =>
    have hd := (HadamardSeries.log_series_derivative B hB hs (x : ℂ) hz).comp_ofReal
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    simpa [Function.comp_def] using hr.deriv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (r+1) (fun v : ℝ => (∑' i,
        (Complex.log ((v : ℂ)+B i) - Complex.log (B i))).re) =ᶠ[𝓝 x]
        (fun v : ℝ => ((-1 : ℂ)^r*(r.factorial : ℂ)*
          ∑' i, (((v : ℂ)+B i)⁻¹)^(r+1)).re) := by
      filter_upwards [Ioi_mem_nhds hx] with v hv
      exact ih v hv hv
    rw [he.deriv_eq]
    have hd := ((HadamardSeries.pole_series_derivative B r hB hs (x : ℂ) hz).const_mul
      ((-1 : ℂ)^r*(r.factorial : ℂ))).comp_ofReal
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
    have hh := hr.deriv
    change deriv (fun v : ℝ => ((-1 : ℂ)^r*(r.factorial : ℂ)*
      ∑' i, (((v : ℂ)+B i)⁻¹)^(r+1)).re) x = _ at hh
    rw [hh]
    change (_ : ℂ).re = (_ : ℂ).re
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem positive_function_log_identity (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c x : ℝ) (hc : 0 < c) (hx : 0 < x) (hg : 0 < g x)
    (hp : (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i)) :
    Real.log (g x) - Real.log c =
      (∑' i, (Complex.log ((x : ℂ)+B i) - Complex.log (B i))).re := by
  have hz : (x : ℂ) ∈ HadamardSeries.domain := by
    change -(1/2 : ℝ) < x
    linarith
  rw [HadamardSeries.canonical_product_eq_exp B hB hs (x : ℂ) hz] at hp
  have hn := congrArg (fun z : ℂ => Real.log ‖z‖) hp
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hg hc), abs_of_pos hg, abs_of_pos hc,
    Complex.norm_exp, Real.log_exp, Real.log_div (ne_of_gt hg) (ne_of_gt hc)] using hn


end CanonicalQBridge
end
end QBridgeGeneric
open Set Filter Topology
open scoped BigOperators
namespace CanonicalQBridge
variable {ι : Type*} [Countable ι]

theorem original_Q_spectral_identity (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x)-Real.log c) (u^2) =
    (2 : ℝ)^(r+1)*(r.factorial : ℝ)/u *
      (∑' i, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i))^(r+1)).re := by
  have he : (fun x => Real.log (g x)-Real.log c) =ᶠ[𝓝 (u^2)]
      (fun x : ℝ => (∑' i, (Complex.log ((x : ℂ)+B i)-Complex.log (B i))).re) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos hu)] with x hx
    exact positive_function_log_identity B hB hs g c x hc hx (hg x hx) (hp x hx)
  rw [he.iteratedDeriv_eq (r+1), real_log_iteratedDeriv B hB hs r (u^2) (by nlinarith)]
  have hsum : (∑' i, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i))^(r+1)) =
      ((u^(2*(r+1)) : ℝ) : ℂ) * ∑' i, (((u^2 : ℂ)+B i)⁻¹)^(r+1) := by
    simp_rw [div_eq_mul_inv,mul_pow]
    rw [tsum_mul_left]
    congr 1
    push_cast
    rw [← pow_mul]
  rw [hsum, Complex.re_ofReal_mul]
  have hcast : (-1 : ℂ)^r*(r.factorial : ℂ) =
      (((-1 : ℝ)^r*(r.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.re_ofReal_mul]
  have hsign : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by rw [← mul_pow]; norm_num
  have hpw : u^(2*(r+1)) = u^(2*(r+1)-1)*u := by
    rw [← pow_succ]
    congr 1 <;> omega
  rw [hpw]
  field_simp
  simp only [pow_two, hsign, one_mul, Complex.ofReal_pow,Complex.ofReal_mul]

end CanonicalQBridge
noncomputable section
namespace CountedQBridge
variable {ι : Type*} [Countable ι]
def pole (gamma eps : ℝ) : ℂ :=
  ((gamma^2-eps^2 : ℝ) : ℂ) - ((2*eps*gamma : ℝ) : ℂ)*Complex.I

theorem pole_re (gamma eps : ℝ) : (pole gamma eps).re = gamma^2-eps^2 := by
  simp only [pole, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]

theorem pole_im (gamma eps : ℝ) : (pole gamma eps).im = -(2*eps*gamma) := by
  simp only [pole, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_sub]

theorem pole_real_lower (gamma eps : ℝ) (hg : 2 ≤ gamma) (he : |eps| ≤ 1/2) :
    1 ≤ (pole gamma eps).re ∧ gamma^2/2 ≤ (pole gamma eps).re := by
  rw [pole_re]
  obtain ⟨h1,h2⟩ := abs_le.mp he
  have he2 : eps^2 ≤ 1/4 := by nlinarith
  constructor <;> nlinarith

theorem pole_inverse_summable (gamma eps : ι → ℝ)
    (hg : ∀ j, 2 ≤ gamma j) (he : ∀ j, |eps j| ≤ 1/2)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p) :
    Summable (fun j => (pole (gamma j) (eps j)).re⁻¹) := by
  have hs := (ReciprocalCounting.summable_inverse_from_sublinear_count
    (fun j => (gamma j)^2) (fun j => by nlinarith [hg j]) C p hp hcount).1
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro j
    exact inv_nonneg.mpr (le_trans (by norm_num) (pole_real_lower _ _ (hg j) (he j)).1)
  · intro j
    have hb := pole_real_lower _ _ (hg j) (he j)
    have hp1 : 0 < (pole (gamma j) (eps j)).re := by linarith
    have hg1 : 0 < (gamma j)^2/2 := by nlinarith [hg j]
    calc
      _ ≤ ((gamma j)^2/2)⁻¹ := (inv_le_inv₀ hp1 hg1).2 hb.2
      _ = 2*((gamma j)^2)⁻¹ := by rw [inv_div]; ring

end CountedQBridge
end
noncomputable section
variable {ι : Type*} [Countable ι]
namespace ActualXiBranches
open EtaQBridge XiMultiplicity Set
noncomputable def G (x : ℝ) : ℝ := (xi (1/2 + (Real.sqrt x : ℂ))).re

theorem G_continuous : Continuous G := by
  exact Complex.continuous_re.comp (xi_differentiable.continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.comp Real.continuous_sqrt)))

theorem G_quarter : G (1/4) = 1/2 := by
  have h : Real.sqrt (1/4) = (1/2 : ℝ) := by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  simp only [G, h]
  norm_num [show (1/2 : ℂ) + ((1/2 : ℝ) : ℂ) = 1 by norm_num,
    XiZeroGeometry.xi_one_value]

theorem continuous_nonzero_positive (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ x ≥ 0, f x ≠ 0) (a : ℝ) (ha : 0 ≤ a) (hfa : 0 < f a) :
    ∀ x ≥ 0, 0 < f x := by
  intro x hx
  by_contra h
  have hfx : f x ≤ 0 := le_of_not_gt h
  rcases le_total x a with hxa | hax
  · obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hxa hf.continuousOn
      (show (0 : ℝ) ∈ Icc (f x) (f a) from ⟨hfx, hfa.le⟩)
    exact hn y (le_trans hx hy.1) hfy
  · obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' hax hf.continuousOn
      (show (0 : ℝ) ∈ Icc (f x) (f a) from ⟨hfx, hfa.le⟩)
    exact hn y (le_trans ha hy.1) hfy

theorem G_positive_from_product (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (hp : ∀ x > 0, ((G x / G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i)) :
    ∀ x ≥ 0, 0 < G x := by
  have hprod (x : ℝ) (hx : 0 < x) : (∏' i, (1+(x : ℂ)/B i)) ≠ 0 := by
    rw [HadamardSeries.canonical_product_eq_exp B hB hs _ (by
      change -(1/2 : ℝ) < (x : ℂ).re
      simpa using (show -(1/2 : ℝ) < x by linarith))]
    exact Complex.exp_ne_zero _
  have h0 : G 0 ≠ 0 := by
    intro he
    have hh := hp 1 (by norm_num)
    simp only [he, div_zero, Complex.ofReal_zero] at hh
    exact hprod 1 (by norm_num) hh.symm
  apply continuous_nonzero_positive G G_continuous ?_ (1/4) (by norm_num)
    (by rw [G_quarter]; norm_num)
  intro x hx
  rcases eq_or_lt_of_le hx with he | he
  · simpa [← he] using h0
  · intro hh
    have hh' := hp x he
    simp only [hh, zero_div, Complex.ofReal_zero] at hh'
    exact hprod x he hh'.symm
end ActualXiBranches

namespace ActualXiBranches
open EtaQBridge XiMultiplicity Set
noncomputable def gamma (i : Occurrence) : ℝ := (location i).im
noncomputable def eps (i : Occurrence) : ℝ := (location i).re - 1/2
noncomputable def B (i : Occurrence) : ℂ := CountedQBridge.pole (gamma i) (eps i)
noncomputable def Q (n : ℕ) (u : ℝ) : ℝ :=
  (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
    iteratedDeriv n (fun x => Real.log (G x) - Real.log (G 0)) (u^2)

theorem eps_bound (i : Occurrence) : |eps i| ≤ 1/2 :=
  (XiZeroGeometry.centered_zero_strip (location i) i.1.property.1).le

theorem B_squared_zero (i : Occurrence) : B i = -(location i-1/2)^2 := by
  apply Complex.ext <;>
    simp [B, CountedQBridge.pole, gamma, eps, Complex.mul_re, Complex.mul_im,
      pow_two] <;> ring


end ActualXiBranches
end
namespace ActualXiBranches
open XiMultiplicity Set Filter Topology

theorem original_Q_identity_from_inputs
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i)) :
    ∀ n ≥ 1, ∀ u > 0,
      Q n u = (2 : ℝ)^n*((n-1).factorial : ℝ)/u *
        (∑' i, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i))^n).re := by
  have hb : ∀ i, 1 ≤ (B i).re := fun i =>
    (CountedQBridge.pole_real_lower _ _ (lower i) (eps_bound i)).1
  have hs : Summable (fun i => (B i).re⁻¹) :=
    CountedQBridge.pole_inverse_summable gamma eps lower eps_bound C (3/4)
      (by norm_num) count
  have hg := G_positive_from_product B hb hs product
  intro n hn u hu
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Q,Nat.succ_eq_add_one,Nat.add_sub_cancel] using
    CanonicalQBridge.original_Q_spectral_identity B hb hs G (G 0) (hg 0 le_rfl)
      (fun x hx => hg x hx.le) product r u hu

theorem scale_identity (n : ℕ) (hn : 2 ≤ n) (u : ℝ) (hu : 0 < u) :
    (n : ℝ)/(Real.sqrt (n : ℝ)/u)^2 = u^2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [div_pow,Real.sq_sqrt hn0.le]
  field_simp [ne_of_gt hn0,ne_of_gt hu]

theorem small_scale_Q_from_identity
    (identity : ∀ n ≥ 1, ∀ u > 0,
      Q n u = (2 : ℝ)^n*((n-1).factorial : ℝ)/u *
        (∑' i, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i))^n).re)
    (spectral : ∃ δ > (0 : ℝ), ∀ h, 0 < h → h < δ → ∀ (k : ℕ), 2 ≤ k →
      Summable (fun i : Occurrence =>
        (((((k : ℝ)/h^2 : ℝ) : ℂ) / ((((k : ℝ)/h^2+(gamma i)^2-(eps i)^2 : ℝ) : ℂ) -
          (2*eps i*gamma i : ℝ)*Complex.I)) ^ k)) ∧
      0 < (∑' i : Occurrence,
        (((((k : ℝ)/h^2 : ℝ) : ℂ) / ((((k : ℝ)/h^2+(gamma i)^2-(eps i)^2 : ℝ) : ℂ) -
          (2*eps i*gamma i : ℝ)*Complex.I)) ^ k)).re) :
    ∃ δ > (0 : ℝ), ∀ (n : ℕ), 2 ≤ n → ∀ u > 0,
      Real.sqrt (n : ℝ)/u < δ → 0 < Q n u := by
  obtain ⟨δ,hδ,hsp⟩ := spectral
  refine ⟨δ,hδ,?_⟩
  intro n hn u hu hscale
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp := (hsp (Real.sqrt (n : ℝ)/u) (div_pos (Real.sqrt_pos.mpr hn0) hu) hscale n hn).2
  rw [identity n (by omega) u hu]
  have heq : (∑' i : Occurrence,
        (((((n : ℝ)/(Real.sqrt (n : ℝ)/u)^2 : ℝ) : ℂ) /
          ((((n : ℝ)/(Real.sqrt (n : ℝ)/u)^2+(gamma i)^2-(eps i)^2 : ℝ) : ℂ) -
            (2*eps i*gamma i : ℝ)*Complex.I)) ^ n)) =
      ∑' i : Occurrence, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i))^n := by
    apply tsum_congr
    intro i
    rw [scale_identity n hn u hu]
    simp only [B, CountedQBridge.pole,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_pow]
    congr 2
    ring
  rw [heq] at hp
  exact mul_pos (by positivity) hp

theorem Q_one_nonneg_from_identity
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (identity : ∀ n ≥ 1, ∀ u > 0,
      Q n u = (2 : ℝ)^n*((n-1).factorial : ℝ)/u *
        (∑' i, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i))^n).re) :
    ∀ u > 0, 0 ≤ Q 1 u := by
  intro u hu
  rw [identity 1 (by norm_num) u hu]
  apply mul_nonneg (by positivity)
  simp only [pow_one]
  let f : Occurrence → ℂ := fun i => ((u^2 : ℝ) : ℂ)/((u^2 : ℂ)+B i)
  have hf (i : Occurrence) : 0 ≤ (f i).re := by
    dsimp [f]
    rw [div_eq_mul_inv,Complex.re_ofReal_mul,Complex.inv_re]
    apply mul_nonneg (sq_nonneg u)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    have hb := (CountedQBridge.pole_real_lower _ _ (lower i) (eps_bound i)).1
    change 1 ≤ (B i).re at hb
    simp only [Complex.add_re,← Complex.ofReal_pow,Complex.ofReal_re]
    nlinarith
  change 0 ≤ (∑' i, f i).re
  by_cases hs : Summable f
  · have he := Complex.reCLM.map_tsum hs
    change (∑' i, f i).re = ∑' i, (f i).re at he
    rw [he]
    exact tsum_nonneg hf
  · rw [tsum_eq_zero_of_not_summable hs]
    simp

end ActualXiBranches
theorem qbridge_concrete_result :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // f s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt f s.val)
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    (∀ n ≥ 1, ∀ u > 0,
      Q n u = (2 : ℝ)^n*((n-1).factorial : ℝ)/u *
        (∑' i : I, (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)-(i.1.val-1/2)^2))^n).re) ∧
    (∃ δ > (0 : ℝ), ∀ (n : ℕ), 2 ≤ n → ∀ u > 0,
      Real.sqrt (n : ℝ)/u < δ → 0 < Q n u) ∧
    (∀ u > 0, 0 ≤ Q 1 u) := by
  dsimp only
  let N : ℝ → ℝ := fun T =>
    ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
  have hlower : ∀ i : XiMultiplicity.Occurrence, 2 ≤ ActualXiBranches.gamma i := by
    intro i
    exact (XiQuantitativePublished.concrete_upper_zero_lower i).2
  have hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset XiMultiplicity.Occurrence,
      (∀ i ∈ F, (ActualXiBranches.gamma i)^2 ≤ y) →
        (F.card : ℝ) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) :=
    BranchActualCount.original_occurrence_sublinear_bound
  have hp : ∀ x > 0, ((ActualXiBranches.G x/ActualXiBranches.G 0 : ℝ) : ℂ) =
      ∏' i, (1+(x : ℂ)/ActualXiBranches.B i) := by
    intro x hx
    have hh := (XiPairingPublished.concrete_G_zero_product x hx.le).2
    change ((ActualXiBranches.G x/ActualXiBranches.G 0 : ℝ) : ℂ) =
      ∏' i : XiMultiplicity.Occurrence,
        (1+(x : ℂ)/(-(XiMultiplicity.location i-1/2)^2)) at hh
    simpa only [ActualXiBranches.B_squared_zero] using hh
  have hi := ActualXiBranches.original_Q_identity_from_inputs hlower (4*(N 600+600)) hcount hp
  have hs := ActualXiBranches.small_scale_Q_from_identity hi
    BranchActualCount.original_occurrence_uniform_small_scale_positive
  constructor
  · intro n hn u hu
    change ActualXiBranches.Q n u = (2 : ℝ)^n*((n-1).factorial : ℝ)/u *
      (∑' i : XiMultiplicity.Occurrence,
        (((u^2 : ℝ) : ℂ)/((u^2 : ℂ)-(XiMultiplicity.location i-1/2)^2))^n).re
    rw [hi n hn u hu]
    congr 2
    apply tsum_congr
    intro i
    rw [ActualXiBranches.B_squared_zero]
    simp only [sub_eq_add_neg]
  · exact ⟨hs, ActualXiBranches.Q_one_nonneg_from_identity hlower hi⟩


open Set Filter Topology
namespace CanonicalQBridge
variable {ι : Type*} [Countable ι]
/-- Continuity at the left endpoint follows from the unnormalized pole series,
not from the singular-looking normalized factor 1/u. -/
theorem original_Q_continuous_on_nonnegative
    (B : ι → ℂ) (hB : ∀ i, 1 ≤ (B i).re)
    (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) :
    ContinuousOn (fun u : ℝ => (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x)-Real.log c) (u^2)) (Ici 0) := by
  let H : ℂ → ℂ := fun z => ∑' i, ((z+B i)⁻¹)^(r+1)
  let R : ℝ → ℝ := fun u => (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*
    (r.factorial : ℝ)*(H ((u^2 : ℝ) : ℂ)).re
  have hR : Continuous R := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hz : ((u^2 : ℝ) : ℂ) ∈ HadamardSeries.domain := by
      change -(1/2 : ℝ) < u^2
      nlinarith [sq_nonneg u]
    have hH : ContinuousAt H ((u^2 : ℝ) : ℂ) :=
      (HadamardSeries.pole_series_derivative B r hB hs _ hz).continuousAt
    have hcomp : ContinuousAt (fun u : ℝ => H ((u^2 : ℝ) : ℂ)) u :=
      hH.comp_of_eq (show ContinuousAt (fun t : ℝ => ((t^2 : ℝ) : ℂ)) u from
        (Complex.continuous_ofReal.comp (continuous_id.pow 2)).continuousAt) rfl
    exact (((continuousAt_const.mul (continuousAt_id.pow _)).mul
      continuousAt_const).mul (Complex.continuous_re.continuousAt.comp hcomp))
  apply hR.continuousOn.congr
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    have hm : 2*(r+1)-1 ≠ 0 := by omega
    simp [R,hm]
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have he : (fun x => Real.log (g x)-Real.log c) =ᶠ[𝓝 (u^2)]
      (fun x : ℝ => (∑' i, (Complex.log ((x : ℂ)+B i)-Complex.log (B i))).re) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos hup)] with x hx
    exact positive_function_log_identity B hB hs g c x hc hx (hg x hx) (hp x hx)
  dsimp only
  rw [he.iteratedDeriv_eq (r+1), real_log_iteratedDeriv B hB hs r (u^2) (by nlinarith)]
  have hcast : (-1 : ℂ)^r*(r.factorial : ℂ) =
      (((-1 : ℝ)^r*(r.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.re_ofReal_mul]
  have hsign : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by rw [← mul_pow]; norm_num
  dsimp [R,H]
  calc
    _ = (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*
        ((-1 : ℝ)^r * (-1 : ℝ)^r)*(r.factorial : ℝ)*
        (∑' i, ((((u^2 : ℝ) : ℂ)+B i)⁻¹)^(r+1)).re := by push_cast; ring
    _ = _ := by rw [hsign]; ring
end CanonicalQBridge
open Set Filter Topology
namespace CanonicalQBridge
variable {ι : Type*} [Countable ι]
theorem original_Q_differentiable_positive
    (B : ι → ℂ) (hB : ∀ i, 1 ≤ (B i).re)
    (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    DifferentiableAt ℝ (fun u : ℝ => (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x)-Real.log c) (u^2)) u := by
  let H : ℂ → ℂ := fun z => ∑' i, ((z+B i)⁻¹)^(r+1)
  let R : ℝ → ℝ := fun u => (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*
    (r.factorial : ℝ)*(H ((u^2 : ℝ) : ℂ)).re
  have hz : ((u^2 : ℝ) : ℂ) ∈ HadamardSeries.domain := by
    change -(1/2 : ℝ) < u^2
    nlinarith [sq_nonneg u]
  have hd := (HadamardSeries.pole_series_derivative B r hB hs _ hz).comp_ofReal
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (u^2) hd
  have hcomp := hr.comp_of_eq u ((hasDerivAt_id u).pow 2) rfl
  have hR : DifferentiableAt ℝ R u :=
    ((((differentiableAt_const ((2 : ℝ)^(r+1))).mul (differentiableAt_id.pow _)).mul
      (differentiableAt_const (r.factorial : ℝ))).mul hcomp.differentiableAt)
  apply hR.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  have he : (fun x => Real.log (g x)-Real.log c) =ᶠ[𝓝 (v^2)]
      (fun x : ℝ => (∑' i, (Complex.log ((x : ℂ)+B i)-Complex.log (B i))).re) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos hv)] with x hx
    exact positive_function_log_identity B hB hs g c x hc hx (hg x hx) (hp x hx)
  rw [he.iteratedDeriv_eq (r+1), real_log_iteratedDeriv B hB hs r (v^2) (by nlinarith)]
  have hcast : (-1 : ℂ)^r*(r.factorial : ℂ) =
      (((-1 : ℝ)^r*(r.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.re_ofReal_mul]
  have hsign : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by rw [← mul_pow]; norm_num
  dsimp [R,H]
  calc
    _ = (2 : ℝ)^(r+1)*v^(2*(r+1)-1)*
        ((-1 : ℝ)^r * (-1 : ℝ)^r)*(r.factorial : ℝ)*
        (∑' i, ((((v^2 : ℝ) : ℂ)+B i)⁻¹)^(r+1)).re := by push_cast; ring
    _ = _ := by rw [hsign]; ring
end CanonicalQBridge
open Set Filter Topology
namespace NegativeSeedMinimum
/-- Compactness supplies an interior global minimum once both ends of the positive axis
have values above a negative seed. This theorem does not assert these inputs for Q. -/
theorem interior_global_minimum (f : ℝ → ℝ)
    (hc : ContinuousOn f (Ici 0)) (hzero : f 0 = 0)
    (hinfty : ∀ᶠ u : ℝ in atTop, 0 ≤ f u)
    (u₀ : ℝ) (hu₀ : 0 < u₀) (hseed : f u₀ < 0) :
    ∃ v > 0, f v ≤ f u₀ ∧ (∀ u > 0, f v ≤ f u) ∧
      IsLocalMin f v ∧ deriv f v = 0 := by
  obtain ⟨b,hb⟩ := eventually_atTop.1 hinfty
  let R := max b (u₀+1)
  have hR : u₀ < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hR0 : 0 < R := hu₀.trans hR
  have hRb : b ≤ R := le_max_left _ _
  have hcR : ContinuousOn f (Icc 0 R) := hc.mono (fun _ h => h.1)
  obtain ⟨v,hv,hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hR0.le) hcR
  have hval : f v ≤ f u₀ := hmin ⟨hu₀.le,hR.le⟩
  have hvneg : f v < 0 := hval.trans_lt hseed
  have hv0 : 0 < v := lt_of_le_of_ne hv.1 (by
    intro h; rw [← h,hzero] at hvneg; exact lt_irrefl _ hvneg)
  have hvR : v < R := lt_of_le_of_ne hv.2 (by
    intro h; subst v; exact (not_lt_of_ge (hb R hRb)) hvneg)
  have hlocal : IsLocalMin f v := by
    filter_upwards [Ioo_mem_nhds hv0 hvR] with u hu
    exact hmin ⟨hu.1.le,hu.2.le⟩
  refine ⟨v,hv0,hval,?_,hlocal,hlocal.deriv_eq_zero⟩
  intro u hu
  by_cases hur : u ≤ R
  · exact hmin ⟨hu.le,hur⟩
  · exact hvneg.le.trans (hb u (hRb.trans (le_of_not_ge hur)))
end NegativeSeedMinimum
namespace ActualXiBranches
open Set Filter Topology XiMultiplicity

theorem Q_zero (n : ℕ) (hn : 1 ≤ n) : Q n 0 = 0 := by
  have hm : 2*n-1 ≠ 0 := by omega
  simp [Q,hm]

theorem Q_continuous_from_inputs
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i))
    (n : ℕ) (hn : 1 ≤ n) : ContinuousOn (Q n) (Ici 0) := by
  have hb : ∀ i, 1 ≤ (B i).re := fun i =>
    (CountedQBridge.pole_real_lower _ _ (lower i) (eps_bound i)).1
  have hs : Summable (fun i => (B i).re⁻¹) :=
    CountedQBridge.pole_inverse_summable gamma eps lower eps_bound C (3/4)
      (by norm_num) count
  have hg := G_positive_from_product B hb hs product
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  unfold Q
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using
    CanonicalQBridge.original_Q_continuous_on_nonnegative B hb hs G (G 0)
      (hg 0 le_rfl) (fun x hx => hg x hx.le) product r

theorem Q_differentiable_from_inputs
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i))
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 < u) : DifferentiableAt ℝ (Q n) u := by
  have hb : ∀ i, 1 ≤ (B i).re := fun i =>
    (CountedQBridge.pole_real_lower _ _ (lower i) (eps_bound i)).1
  have hs : Summable (fun i => (B i).re⁻¹) :=
    CountedQBridge.pole_inverse_summable gamma eps lower eps_bound C (3/4)
      (by norm_num) count
  have hg := G_positive_from_product B hb hs product
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  unfold Q
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using
    CanonicalQBridge.original_Q_differentiable_positive B hb hs G (G 0)
      (hg 0 le_rfl) (fun x hx => hg x hx.le) product r u hu

theorem eventually_Q_nonnegative
    (scale : ∃ δ > (0 : ℝ), ∀ (n : ℕ), 2 ≤ n → ∀ u > 0,
      Real.sqrt (n : ℝ)/u < δ → 0 < Q n u)
    (one : ∀ u > 0, 0 ≤ Q 1 u) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ u : ℝ in atTop, 0 ≤ Q n u := by
  by_cases hn1 : n = 1
  · subst n
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact one u hu
  obtain ⟨δ,hδ,hscale⟩ := scale
  refine eventually_atTop.mpr ⟨max 1 (Real.sqrt (n : ℝ)/δ+1),?_⟩
  intro u hu
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hu0 : 0 < u := by linarith
  have hlt : Real.sqrt (n : ℝ)/δ < u :=
    lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hu)
  have hlt' : Real.sqrt (n : ℝ)/u < δ :=
    (div_lt_iff₀ hu0).mpr (by
      have hh := (div_lt_iff₀ hδ).mp hlt
      nlinarith)
  exact (hscale n (by omega) u hu0 hlt').le
end ActualXiBranches

theorem minimum_concrete_result :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n : ℕ), 1 ≤ n → ∀ u₀ > 0, Q n u₀ < 0 →
      ∃ v > 0, Q n v ≤ Q n u₀ ∧ (∀ u > 0, Q n v ≤ Q n u) ∧
        IsLocalMin (Q n) v ∧ HasDerivAt (Q n) 0 v := by
  dsimp only
  let N : ℝ → ℝ := fun T =>
    ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
  have hlower : ∀ i : XiMultiplicity.Occurrence, 2 ≤ ActualXiBranches.gamma i := by
    intro i
    exact (XiQuantitativePublished.concrete_upper_zero_lower i).2
  have hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset XiMultiplicity.Occurrence,
      (∀ i ∈ F, (ActualXiBranches.gamma i)^2 ≤ y) →
        (F.card : ℝ) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) :=
    BranchActualCount.original_occurrence_sublinear_bound
  have hp : ∀ x > 0, ((ActualXiBranches.G x/ActualXiBranches.G 0 : ℝ) : ℂ) =
      ∏' i, (1+(x : ℂ)/ActualXiBranches.B i) := by
    intro x hx
    have hh := (XiPairingPublished.concrete_G_zero_product x hx.le).2
    change ((ActualXiBranches.G x/ActualXiBranches.G 0 : ℝ) : ℂ) =
      ∏' i : XiMultiplicity.Occurrence,
        (1+(x : ℂ)/(-(XiMultiplicity.location i-1/2)^2)) at hh
    simpa only [ActualXiBranches.B_squared_zero] using hh
  have hscale : ∃ δ > (0 : ℝ), ∀ (n : ℕ), 2 ≤ n → ∀ u > 0,
      Real.sqrt (n : ℝ)/u < δ → 0 < ActualXiBranches.Q n u :=
    qbridge_concrete_result.2.1
  have hone : ∀ u > 0, 0 ≤ ActualXiBranches.Q 1 u := qbridge_concrete_result.2.2
  intro n hn u₀ hu₀ hseed
  obtain ⟨v,hv,hval,hglobal,hlocal,hder⟩ := NegativeSeedMinimum.interior_global_minimum (ActualXiBranches.Q n)
    (ActualXiBranches.Q_continuous_from_inputs hlower (4*(N 600+600)) hcount hp n hn)
    (ActualXiBranches.Q_zero n hn)
    (ActualXiBranches.eventually_Q_nonnegative hscale hone n hn) u₀ hu₀ hseed
  refine ⟨v,hv,hval,hglobal,hlocal,?_⟩
  have hd := (ActualXiBranches.Q_differentiable_from_inputs hlower
    (4*(N 600+600)) hcount hp n hn v hv).hasDerivAt
  rw [hder] at hd
  exact hd


open Set Filter Topology
namespace NegativeSeedCascade
noncomputable def tower (h : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*iteratedDeriv n h (u^2)
theorem recurrence (h : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hd : DifferentiableAt ℝ (iteratedDeriv n h) (u^2)) :
    tower h (n+1) u = (2*(n : ℝ)-1)*tower h n u-u*deriv (tower h n) u := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hd' := hd.hasDerivAt.comp_of_eq u ((hasDerivAt_id u).pow 2) rfl
  have hd'' := ((((hasDerivAt_id u).pow (2*r+1)).const_mul ((2 : ℝ)^(r+1))).mul_const
    ((-1 : ℝ)^r)).mul hd'
  have hf : tower h (r+1) = fun v => (2 : ℝ)^(r+1)*v^(2*r+1)*(-1 : ℝ)^r*
      iteratedDeriv (r+1) h (v^2) := by
    funext v
    simp only [tower, Nat.add_sub_cancel]
    congr 3 <;> omega
  simp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, id_eq] at hd''
  change HasDerivAt (fun v : ℝ => (2 : ℝ)^(r+1)*v^(2*r+1)*(-1 : ℝ)^r*
    iteratedDeriv (r+1) h (v^2)) _ u at hd''
  rw [hf, hd''.deriv]
  simp only [tower, Nat.add_sub_cancel, iteratedDeriv_succ]
  have he : 2*(r+1+1)-1 = 2*r+3 := by omega
  rw [he]
  simp only [pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    Nat.add_sub_cancel, one_mul, mul_one]
  simp only [Nat.cast_succ, pow_zero, one_mul]
  ring
end NegativeSeedCascade
open Set Filter Topology
namespace CanonicalQBridge
variable {ι : Type*} [Countable ι]
theorem original_log_iterated_differentiable
    (B : ι → ℂ) (hB : ∀ i, 1 ≤ (B i).re)
    (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (iteratedDeriv n (fun x => Real.log (g x)-Real.log c)) x := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hz : (x : ℂ) ∈ HadamardSeries.domain := by
    change -(1/2 : ℝ) < x
    linarith
  have hd := ((HadamardSeries.pole_series_derivative B r hB hs (x : ℂ) hz).const_mul
      ((-1 : ℂ)^r*(r.factorial : ℂ))).comp_ofReal
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  apply hr.differentiableAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  change 0 < y at hy
  have he : (fun t => Real.log (g t)-Real.log c) =ᶠ[𝓝 y]
      (fun t : ℝ => (∑' i, (Complex.log ((t : ℂ)+B i)-Complex.log (B i))).re) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact positive_function_log_identity B hB hs g c t hc ht (hg t ht) (hp t ht)
  rw [he.iteratedDeriv_eq (r+1), real_log_iteratedDeriv B hB hs r y (by linarith)]
  rfl
end CanonicalQBridge
open Set Filter Topology
namespace NegativeSeedCascade
/-- Global negative stationary minima at every later order, all for the same tower. -/
theorem sequence_from_minimum_and_recurrence (Q : ℕ → ℝ → ℝ)
    (hmin : ∀ n ≥ 1, ∀ u > 0, Q n u < 0 →
      ∃ v > 0, Q n v ≤ Q n u ∧ (∀ w > 0, Q n v ≤ Q n w) ∧
        IsLocalMin (Q n) v ∧ HasDerivAt (Q n) 0 v)
    (hrec : ∀ n ≥ 1, ∀ u > 0,
      Q (n+1) u = (2*(n : ℝ)-1)*Q n u-u*deriv (Q n) u)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (u₀ : ℝ) (hu₀ : 0 < u₀) (hseed : Q n₀ u₀ < 0) :
    ∃ v : ℕ → ℝ,
      Q n₀ (v 0) ≤ Q n₀ u₀ ∧
      ∀ j : ℕ, 0 < v j ∧ Q (n₀+j) (v j) < 0 ∧
        (∀ u > 0, Q (n₀+j) (v j) ≤ Q (n₀+j) u) ∧
        IsLocalMin (Q (n₀+j)) (v j) ∧ HasDerivAt (Q (n₀+j)) 0 (v j) ∧
        Q (n₀+(j+1)) (v (j+1)) ≤ (2*((n₀+j : ℕ) : ℝ)-1)*Q (n₀+j) (v j) := by
  have hex : ∀ j : ℕ, ∃ v > 0, Q (n₀+j) v < 0 ∧
      (∀ u > 0, Q (n₀+j) v ≤ Q (n₀+j) u) ∧
      IsLocalMin (Q (n₀+j)) v ∧ HasDerivAt (Q (n₀+j)) 0 v := by
    intro j
    induction j with
    | zero =>
      obtain ⟨v,hv,hval,hglobal,hlocal,hstat⟩ := hmin n₀ hn₀ u₀ hu₀ hseed
      exact ⟨v,hv,by simpa using hval.trans_lt hseed,by simpa using hglobal,
        by simpa using hlocal,by simpa using hstat⟩
    | succ j ih =>
      obtain ⟨v,hv,hneg,hglobal,hlocal,hstat⟩ := ih
      have hn : 1 ≤ n₀+j := by omega
      have hc : 0 < 2*((n₀+j : ℕ) : ℝ)-1 := by
        have hh : (1 : ℝ) ≤ (n₀+j : ℕ) := by exact_mod_cast hn
        linarith
      have hnext : Q (n₀+j+1) v < 0 := by
        rw [hrec (n₀+j) hn v hv,hstat.deriv]
        simpa using mul_neg_of_pos_of_neg hc hneg
      obtain ⟨w,hw,hval,hwglobal,hwlocal,hwstat⟩ := hmin (n₀+j+1) (by omega) v hv hnext
      refine ⟨w,hw,?_,?_,?_,?_⟩
      · simpa [Nat.add_assoc] using hval.trans_lt hnext
      · simpa [Nat.add_assoc] using hwglobal
      · simpa [Nat.add_assoc] using hwlocal
      · simpa [Nat.add_assoc] using hwstat
  choose v hv hneg hglobal hlocal hstat using hex
  refine ⟨v,?_,?_⟩
  · simpa using hglobal 0 u₀ hu₀
  · intro j
    refine ⟨hv j,hneg j,hglobal j,hlocal j,hstat j,?_⟩
    have hh := hglobal (j+1) (v j) (hv j)
    have he := hrec (n₀+j) (by omega) (v j) (hv j)
    rw [(hstat j).deriv, mul_zero, sub_zero] at he
    rw [← Nat.add_assoc, he] at hh
    simpa only [Nat.add_assoc] using hh
end NegativeSeedCascade
namespace ActualXiBranches
open Set Filter Topology XiMultiplicity

theorem Q_recurrence_from_inputs
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i))
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 < u) :
    Q (n+1) u = (2*(n : ℝ)-1)*Q n u-u*deriv (Q n) u := by
  have hb : ∀ i, 1 ≤ (B i).re := fun i =>
    (CountedQBridge.pole_real_lower _ _ (lower i) (eps_bound i)).1
  have hs : Summable (fun i => (B i).re⁻¹) :=
    CountedQBridge.pole_inverse_summable gamma eps lower eps_bound C (3/4)
      (by norm_num) count
  have hg := G_positive_from_product B hb hs product
  have hd := CanonicalQBridge.original_log_iterated_differentiable B hb hs G (G 0)
    (hg 0 le_rfl) (fun x hx => hg x hx.le) product n hn (u^2) (sq_pos_of_pos hu)
  exact NegativeSeedCascade.recurrence (fun x => Real.log (G x)-Real.log (G 0)) n hn u hd

theorem Q_recurrence_concrete (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 < u) :
    Q (n+1) u = (2*(n : ℝ)-1)*Q n u-u*deriv (Q n) u := by
  let N : ℝ → ℝ := fun T =>
    ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
  have hlower : ∀ i : XiMultiplicity.Occurrence, 2 ≤ gamma i := by
    intro i
    exact (XiQuantitativePublished.concrete_upper_zero_lower i).2
  have hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset XiMultiplicity.Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) →
        (F.card : ℝ) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) :=
    BranchActualCount.original_occurrence_sublinear_bound
  have hp : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i) := by
    intro x hx
    have hh := (XiPairingPublished.concrete_G_zero_product x hx.le).2
    change ((G x/G 0 : ℝ) : ℂ) =
      ∏' i : XiMultiplicity.Occurrence,
        (1+(x : ℂ)/(-(XiMultiplicity.location i-1/2)^2)) at hh
    simpa only [B_squared_zero] using hh
  exact Q_recurrence_from_inputs hlower (4*(N 600+600)) hcount hp n hn u hu
end ActualXiBranches

theorem cascade_concrete_result :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n₀ : ℕ), 1 ≤ n₀ → ∀ u₀ > 0, Q n₀ u₀ < 0 →
    ∃ v : ℕ → ℝ,
      Q n₀ (v 0) ≤ Q n₀ u₀ ∧
      ∀ j : ℕ, 0 < v j ∧ Q (n₀+j) (v j) < 0 ∧
        (∀ u > 0, Q (n₀+j) (v j) ≤ Q (n₀+j) u) ∧
        IsLocalMin (Q (n₀+j)) (v j) ∧ HasDerivAt (Q (n₀+j)) 0 (v j) ∧
        Q (n₀+(j+1)) (v (j+1)) ≤ (2*((n₀+j : ℕ) : ℝ)-1)*Q (n₀+j) (v j) := by
  dsimp only
  intro n₀ hn₀ u₀ hu₀ hseed
  exact NegativeSeedCascade.sequence_from_minimum_and_recurrence ActualXiBranches.Q
    minimum_concrete_result ActualXiBranches.Q_recurrence_concrete n₀ hn₀ u₀ hu₀ hseed


namespace BranchLargeScaleSubsequence

lemma quadratic_binomial (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 + (n : ℝ)*t + ((n : ℝ)*((n : ℝ)-1)/2)*t^2 ≤ (1+t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnn : 0 ≤ (n : ℝ)*((n : ℝ)-1) := by
      cases n with
      | zero => norm_num
      | succ k => simp only [Nat.cast_add, Nat.cast_one]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hc : 0 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*t^3 := mul_nonneg (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+t)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ (1+t) n]
    nlinarith

theorem uniform_ratio_majorant (n : ℕ) (hn : 2 ≤ n) (x d : ℝ)
    (hx : 0 < x) (hxn : x ≤ n) (hd : 0 < d) :
    (x / (x+d))^n ≤ 4 / d^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ d/x := le_of_lt (div_pos hd hx)
  have hbin := quadratic_binomial n (d/x) ht
  have hxx : 0 < x^2 := sq_pos_of_pos hx
  have hnx : x^2 ≤ (n : ℝ)^2 := sq_le_sq₀ (le_of_lt hx) (by positivity) |>.2 hxn
  have hcoef : (n : ℝ)^2 ≤ 2*((n : ℝ)*((n : ℝ)-1)) := by nlinarith
  have hmain : d^2/4 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*(d/x)^2 := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hxx).2
    nlinarith [sq_nonneg d]
  have hpow : d^2/4 ≤ (1+d/x)^n := by
    have : 0 ≤ (n : ℝ)*(d/x) := mul_nonneg (by positivity) ht
    linarith
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hid : x/(x+d) = (1+d/x)⁻¹ := by field_simp
  rw [hid, inv_pow]
  calc
    ((1+d/x)^n)⁻¹ ≤ (d^2/4)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = 4/d^2 := by field_simp


open Filter Topology

lemma ratio_le_linear_inverse (n : ℕ) (x d : ℝ) (hx : 0 < x) (hd : 0 < d) :
    (x / (x+d))^n ≤ (1 + d*((n : ℝ)/x))⁻¹ := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ d/x by linarith [div_pos hd hx]) n
  have hi : (x / (x+d))^n = ((1+d/x)^n)⁻¹ := by
    rw [← inv_pow]
    congr 1
    field_simp
  rw [hi]
  have he : 1+(n : ℝ)*(d/x) = 1+d*((n : ℝ)/x) := by ring
  rw [he] at hb
  exact inv_anti₀ (by positivity) hb

lemma ratio_tendsto_zero (k : ℕ → ℕ) (x : ℕ → ℝ) (hx : ∀ n, 0 < x n) (d : ℝ) (hd : 0 < d)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => (x n/(x n+d))^(k n)) atTop (𝓝 0) := by
  have ht := (Tendsto.const_mul_atTop hd hscale).atTop_add
    (tendsto_const_nhds (x := (1 : ℝ)))
  have hi : Tendsto (fun (n : ℕ) => (1+d*((k n : ℝ)/x n))⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, add_comm] using tendsto_inv_atTop_zero.comp ht
  exact squeeze_zero (fun (n : ℕ) => by have := hx n; positivity)
    (fun (n : ℕ) => ratio_le_linear_inverse (k n) (x n) d (hx n) hd) hi

/- Normalized positive-kernel sum tends to zero in the large-scale regime.
No assertion of a uniform exponential rate is used. -/
theorem large_scale_normalized_sum_zero {ι : Type*} (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hs : Summable (fun i => 1/(d i)^2))
    (k : ℕ → ℕ) (hk : ∀ᶠ n : ℕ in atTop, 2 ≤ k n)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i, (x n/(x n+d i))^(k n)) atTop (𝓝 0) := by
  have hsum : Summable (fun i => 4/(d i)^2) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hs.mul_left 4
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ i, ‖(x n/(x n+d i))^(k n)‖ ≤ 4/(d i)^2 := by
    filter_upwards [hk, hscale.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hscale_n i
    have hxn : x n ≤ (k n : ℝ) := by
      have hh := (le_div_iff₀ (hx n)).1 hscale_n
      simpa using hh
    rw [Real.norm_of_nonneg (by have := hx n; have := hd i; positivity)]
    exact uniform_ratio_majorant (k n) hn (x n) (d i) (hx n) hxn (hd i)
  have ht := tendsto_tsum_of_dominated_convergence (g := fun _ : ι => (0 : ℝ))
    hsum (fun i => ratio_tendsto_zero k x hx (d i) (hd i) hscale) hbound
  simpa using ht


lemma normalized_complex_sum_zero {ι : Type*} (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (hs : Summable (fun i => 1/(d i)^2))
    (k : ℕ → ℕ) (hk : ∀ᶠ n : ℕ in atTop, 2 ≤ k n)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop)
    (f : ℕ → ι → ℂ) (hf : ∀ n i, ‖f n i‖ ≤ (x n/(x n+d i))^(k n)) :
    Tendsto (fun n => ∑' i, f n i) atTop (𝓝 0) := by
  have hsum : Summable (fun i => 4/(d i)^2) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hs.mul_left 4
  have hp : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 0) := by
    intro i
    exact squeeze_zero_norm (fun n => hf n i) (ratio_tendsto_zero k x hx (d i) (hd i) hscale)
  have hb : ∀ᶠ n : ℕ in atTop, ∀ i, ‖f n i‖ ≤ 4/(d i)^2 := by
    filter_upwards [hk, hscale.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hscale_n i
    have hxn : x n ≤ (k n : ℝ) := by
      have hh := (le_div_iff₀ (hx n)).1 hscale_n
      simpa using hh
    exact (hf n i).trans (uniform_ratio_majorant (k n) hn (x n) (d i) (hx n) hxn (hd i))
  simpa using tendsto_tsum_of_dominated_convergence (g := fun _ : ι => (0 : ℂ)) hsum hp hb

/- Large-scale escape estimate for a complex pole family strictly to the right
of an anchor, normalized by the anchor kernel. -/
theorem normalized_pole_sum_tendsto_zero {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).re) (hs : Summable (fun i => 1/((z i).re)^2))
    (k : ℕ → ℕ) (hk : ∀ᶠ n : ℕ in atTop, 2 ≤ k n)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i, ((x n : ℂ)/((x n : ℂ)+z i))^(k n)) atTop (𝓝 0) := by
  apply normalized_complex_sum_zero (fun i => (z i).re) hz hs k hk x hx hscale
  intro n i
  have hpos : 0 < x n+(z i).re := add_pos (hx n) (hz i)
  have hnorm : x n+(z i).re ≤ ‖(x n : ℂ)+z i‖ := by
    simpa only [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm ((x n : ℂ)+z i)
  have hratio : ‖(x n : ℂ)/((x n : ℂ)+z i)‖ ≤ x n/(x n+(z i).re) := by
    rw [norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hx n)]
    exact div_le_div_of_nonneg_left (le_of_lt (hx n)) hpos hnorm
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hratio (k n)
end BranchLargeScaleSubsequence

open Filter Topology
theorem BranchLargeScaleRepair.normalized_pole_subsequence_sum_tendsto_zero {ι : Type*} (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).re) (hs : Summable (fun i => 1/((z i).re)^2))
    (k : ℕ → ℕ) (hk : ∀ᶠ n : ℕ in atTop, 2 ≤ k n)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i, ((x n : ℂ)/((x n : ℂ)+z i))^(k n)) atTop (𝓝 0) :=
  BranchLargeScaleSubsequence.normalized_pole_sum_tendsto_zero z hz hs k hk x hx hscale

open Filter Topology

namespace BranchAnchorRepair

theorem shifted_inverse_square_summable {ι : Type*}
    (a : ι → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ i, 2*b+1 ≤ a i)
    (hs : Summable (fun i => 1/a i)) :
    Summable (fun i => 1/(a i-b)^2) := by
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro i
    positivity
  · intro i
    have hd1 : 1 ≤ a i-b := by linarith [ha i]
    have hd : 0 < a i-b := by linarith
    have hap : 0 < a i := by linarith [ha i]
    calc
      1/(a i-b)^2 ≤ 1/(a i-b) :=
        one_div_le_one_div_of_le hd (by nlinarith)
      _ ≤ 2/a i := (div_le_div_iff₀ hd hap).2 (by linarith [ha i])
      _ = 2*(1/a i) := by ring

theorem anchor_shift_preserves_scale (k : ℕ → ℕ) (x : ℕ → ℝ)
    (hk : Tendsto k atTop atTop) (hx : ∀ n, 0 < x n)
    (b : ℝ) (hb : 0 ≤ b)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => (k n : ℝ)/(x n+b)) atTop atTop := by
  have hkr : Tendsto (fun (n : ℕ) => (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [hscale.eventually (eventually_ge_atTop (2*M)),
    hkr.eventually (eventually_ge_atTop (2*M*b))] with n hn hn'
  apply (le_div_iff₀ (show 0 < x n+b by linarith [hx n])).2
  have hnx : 2*M*x n ≤ (k n : ℝ) := (le_div_iff₀ (hx n)).1 hn
  nlinarith

theorem offline_anchor_gap {ι : Type*} (gamma eps : ι → ℝ)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100) :
    ∀ i : {i // eps i ≠ 0},
      2*(gamma anchor)^2+1 ≤ (gamma i)^2-(eps i)^2 := by
  intro i
  have hg : 1000 < gamma i := lt_of_not_ge (fun h => i.property (verified i h))
  have ha : 0 ≤ gamma anchor := by linarith [lower anchor]
  obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
  have he : (eps i)^2 ≤ 1/4 := by nlinarith
  have ha2 : (gamma anchor)^2 ≤ 10000 := by nlinarith
  nlinarith

end BranchAnchorRepair

open Filter Topology

namespace BranchAnchorRepair

theorem normalized_offline_sum_after_anchor_tendsto_zero {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (hs : Summable (fun i => 1/(B i).re))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i : {i // eps i ≠ 0},
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n))
      atTop (𝓝 0) := by
  let b : ℝ := (gamma anchor)^2
  have hb : 0 ≤ b := sq_nonneg _
  have hgap : ∀ i : {i // eps i ≠ 0}, 2*b+1 ≤ (B i).re := by
    intro i
    rw [hB]
    exact offline_anchor_gap gamma eps lower strip verified anchor anchor_low i
  have hss : Summable (fun i : {i // eps i ≠ 0} => 1/(B i).re) :=
    hs.subtype (fun i => eps i ≠ 0)
  have hshift := shifted_inverse_square_summable
    (fun i : {i // eps i ≠ 0} => (B i).re) b hb hgap hss
  have hz : ∀ i : {i // eps i ≠ 0}, 0 < (B i-(b : ℂ)).re := by
    intro i
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [hgap i]
  have hzs : Summable (fun i : {i // eps i ≠ 0} => 1/((B i-(b : ℂ)).re)^2) := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using hshift
  have hlarge := anchor_shift_preserves_scale k x hk hx b hb hscale
  have hlim := BranchLargeScaleRepair.normalized_pole_subsequence_sum_tendsto_zero
    (fun i : {i // eps i ≠ 0} => B i-(b : ℂ)) hz hzs k
    (hk.eventually (eventually_ge_atTop 2)) (fun n => x n+b)
    (fun n => by linarith [hx n]) hlarge
  have he : ∀ n, (∑' i : {i // eps i ≠ 0},
      (((x n+b : ℝ) : ℂ)/(((x n+b : ℝ) : ℂ)+(B i-(b : ℂ))))^(k n)) =
      ∑' i : {i // eps i ≠ 0},
      (((x n+b : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n) := by
    intro n
    apply tsum_congr
    intro i
    congr 2
    push_cast
    ring
  simp_rw [he] at hlim
  exact hlim

end BranchAnchorRepair

open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace BranchAnchorCounting

theorem indicator_integrable (a : ℝ) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ))) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).indicator measurableSet_Ioi

theorem indicator_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ y : ℝ in Ioi 1, (Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ)) y) = a⁻¹ := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  have hh := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (show 0 < a by linarith)
  simpa only [show (-2 : ℝ)+1 = -1 by norm_num, Real.rpow_neg_one,
    div_neg, div_one, neg_neg] using hh

theorem summable_inverse_from_sublinear_count {ι : Type*} (a : ι → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by
  classical
  have hi : IntegrableOn (fun y : ℝ => C*y^(r-2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : r-2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C
  have hb (F : Finset ι) : (∑ j ∈ F, (a j)⁻¹) ≤ C/(1-r) := by
    calc
      _ = ∑ j ∈ F, ∫ y : ℝ in Ioi 1,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (indicator_integral (a j) (ha j)).symm
      _ = ∫ y : ℝ in Ioi 1, ∑ j ∈ F,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y :=
        (integral_finsetSum F (fun j _ => indicator_integrable (a j))).symm
      _ ≤ ∫ y : ℝ in Ioi 1, C*y^(r-2) := by
        apply integral_mono_ae (integrable_finset_sum F (fun j _ => indicator_integrable (a j))) hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy1 : 1 ≤ y := (mem_Ioi.mp hy).le
        have hy0 : 0 ≤ y := by linarith
        have he : (∑ j ∈ F, (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y) =
            ((F.filter (fun j => a j < y)).card : ℝ)*y^(-2 : ℝ) := by
          simp only [Set.indicator, mem_Ioi]
          rw [← Finset.sum_filter]
          simp
        rw [he]
        have hc := hcount y hy1 (F.filter (fun j => a j < y))
          (fun j hj => (Finset.mem_filter.mp hj).2.le)
        calc
          _ ≤ (C*y^r)*y^(-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hy0 _)
          _ = C*y^(r-2) := by rw [mul_assoc, ← Real.rpow_add (show 0 < y by linarith)]; congr 2 <;> ring
      _ = C/(1-r) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : r-2 < -1) (by norm_num)]
        rw [show r-2+1 = -(1-r) by ring]
        simp only [Real.one_rpow, div_neg, neg_neg, one_div]
        ring
  have hs := summable_of_sum_le (fun j => inv_nonneg.mpr (by linarith [ha j])) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end BranchAnchorCounting
end

namespace BranchAnchorRepair

theorem pole_reciprocal_summable_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p) :
    Summable (fun i => 1/(B i).re) := by
  have hs := (BranchAnchorCounting.summable_inverse_from_sublinear_count
    (fun i => (gamma i)^2) (fun i => by nlinarith [lower i]) C p hp hcount).1
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro i
    rw [hB]
    obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
    have hpos : 0 < (gamma i)^2-(eps i)^2 := by nlinarith [lower i]
    positivity
  · intro i
    have hb : (gamma i)^2/2 ≤ (B i).re := by
      rw [hB]
      obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
      nlinarith [lower i]
    have hg : 0 < (gamma i)^2/2 := by nlinarith [lower i]
    calc
      1/(B i).re ≤ 1/((gamma i)^2/2) := one_div_le_one_div_of_le hg hb
      _ = 2*((gamma i)^2)⁻¹ := by rw [one_div, inv_div]; ring

/- The large-scale off-line estimate with shifted summability derived from
sublinear occurrence counting. The low-height verification remains explicit. -/
theorem normalized_offline_sum_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i : {i // eps i ≠ 0},
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n))
      atTop (𝓝 0) := by
  exact normalized_offline_sum_after_anchor_tendsto_zero gamma eps B hB lower strip
    verified anchor anchor_low
    (pole_reciprocal_summable_from_counting gamma eps B hB lower strip C p hp hcount)
    k hk x hx hscale

end BranchAnchorRepair

namespace BranchAnchorRepair

theorem normalized_power_summable {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => 1/(B i).re))
    (x X : ℝ) (hx : 0 < x) (hX : 0 < X) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun i => ((X : ℂ)/((x : ℂ)+B i))^k) := by
  apply (hs.mul_left (X^k)).of_norm_bounded
  intro i
  have hp : 0 < (B i).re := by linarith [hB i]
  have hnorm : (B i).re ≤ ‖(x : ℂ)+B i‖ := by
    have hh := Complex.re_le_norm ((x : ℂ)+B i)
    simp only [Complex.add_re, Complex.ofReal_re] at hh
    linarith
  have hi : ‖((x : ℂ)+B i)⁻¹‖ ≤ 1/(B i).re := by
    rw [norm_inv, one_div]
    exact inv_anti₀ hp hnorm
  have hi1 : ‖((x : ℂ)+B i)⁻¹‖ ≤ 1 := by
    exact hi.trans (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (hB i))
  have hpow : ‖((x : ℂ)+B i)⁻¹‖^k ≤ 1/(B i).re := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    calc
      _ = ‖((x : ℂ)+B i)⁻¹‖^m * ‖((x : ℂ)+B i)⁻¹‖ := pow_succ _ _
      _ ≤ 1 * ‖((x : ℂ)+B i)⁻¹‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hi1) (norm_nonneg _)
      _ ≤ 1/(B i).re := by simpa using hi
  rw [div_eq_mul_inv, mul_pow, norm_mul, norm_pow, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem critical_normalized_sum_ge_one {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (anchor : ι) (hanchor : eps anchor = 0)
    (x : ℝ) (hx : 0 < x) (k : ℕ)
    (hs : Summable (fun i => (((x+(gamma anchor)^2 : ℝ) : ℂ)/((x : ℂ)+B i))^k)) :
    1 ≤ (∑' i : {i // eps i = 0},
      (((x+(gamma anchor)^2 : ℝ) : ℂ)/((x : ℂ)+B i))^k).re := by
  let f : ι → ℂ := fun i => (((x+(gamma anchor)^2 : ℝ) : ℂ)/((x : ℂ)+B i))^k
  have hc := hs.subtype (fun i => eps i = 0)
  have hcr := Complex.hasSum_re hc.hasSum
  have hnonneg : ∀ i : {i // eps i = 0}, 0 ≤ (f i).re := by
    intro i
    dsimp [f]
    rw [hcritical i i.property]
    rw [← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_pow,
      Complex.ofReal_re]
    positivity
  have ha : (f anchor).re = 1 := by
    dsimp [f]
    rw [hcritical anchor hanchor, ← Complex.ofReal_add, div_self]
    · simp
    · exact_mod_cast (show x+(gamma anchor)^2 ≠ 0 by positivity)
  have hle := hcr.summable.le_tsum (⟨anchor,hanchor⟩ : {i // eps i = 0})
    (fun i _ => hnonneg i)
  rw [hcr.tsum_eq] at hle
  change (f anchor).re ≤ _ at hle
  rw [ha] at hle
  exact hle

end BranchAnchorRepair

namespace BranchAnchorRepair

theorem normalized_spectral_sum_eventually_positive {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < (∑' i,
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n)).re := by
  let f : ℕ → ι → ℂ := fun n i =>
    (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n)
  have hs := pole_reciprocal_summable_from_counting gamma eps B hB lower strip C p hp hcount
  have hlower : ∀ i, 1 ≤ (B i).re := by
    intro i
    rw [hB]
    obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
    nlinarith [lower i]
  have hanchor : eps anchor = 0 := verified anchor (by linarith)
  have hoff := normalized_offline_sum_from_counting gamma eps B hB lower strip
    verified anchor anchor_low C p hp hcount k hk x hx hscale
  have hoffr : Tendsto (fun n => (∑' i : {i // eps i ≠ 0}, f n i).re)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      (Complex.continuous_re.tendsto 0).comp hoff
  filter_upwards [hk.eventually (eventually_ge_atTop 1),
    hoffr.eventually (eventually_gt_nhds (show (-1:ℝ)<0 by norm_num))] with n hn hoffn
  have hsum : Summable (f n) := normalized_power_summable B hlower hs
    (x n) (x n+(gamma anchor)^2) (hx n) (by have := hx n; positivity) (k n) hn
  have hcrit := critical_normalized_sum_ge_one gamma eps B hcritical anchor hanchor
    (x n) (hx n) (k n) hsum
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl {i | eps i = 0}
  have hsplitre := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hsplitre
  change (∑' i : {i // eps i = 0}, f n i).re +
    (∑' i : {i // eps i ≠ 0}, f n i).re = (∑' i, f n i).re at hsplitre
  change 0 < (∑' i, f n i).re
  change 1 ≤ (∑' i : {i // eps i = 0}, f n i).re at hcrit
  linarith

end BranchAnchorRepair

namespace BranchAnchorRepair

/- Large-scale escape forces eventual strict positivity of the original,
unnormalized real spectral power sum. -/
theorem spectral_sum_eventually_positive_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      0 < ∑' i, ((((x n : ℂ)+B i)⁻¹)^(k n)).re := by
  have hnpos := normalized_spectral_sum_eventually_positive gamma eps B hB hcritical
    lower strip verified anchor anchor_low C p hp hcount k hk x hx hscale
  have hs := pole_reciprocal_summable_from_counting gamma eps B hB lower strip C p hp hcount
  have hlower : ∀ i, 1 ≤ (B i).re := by
    intro i
    rw [hB]
    obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
    nlinarith [lower i]
  filter_upwards [hnpos, hk.eventually (eventually_ge_atTop 1)] with n hn hn1
  have hsum : Summable (fun i => (((x n : ℂ)+B i)⁻¹)^(k n)) := by
    simpa only [Complex.ofReal_one, one_div] using
      normalized_power_summable B hlower hs (x n) 1 (hx n) (by norm_num) (k n) hn1
  have he : (∑' i, (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n)) =
      ((x n+(gamma anchor)^2 : ℝ) : ℂ)^(k n) *
        ∑' i, (((x n : ℂ)+B i)⁻¹)^(k n) := by
    simp only [div_eq_mul_inv, mul_pow, tsum_mul_left]
  rw [he, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hn
  have hreal : 0 < (∑' i, (((x n : ℂ)+B i)⁻¹)^(k n)).re :=
    pos_of_mul_pos_right hn (by have := hx n; positivity)
  rw [← (Complex.hasSum_re hsum.hasSum).tsum_eq] at hreal
  exact hreal

end BranchAnchorRepair

set_option maxHeartbeats 1600000
open Set Filter Topology
namespace EtaQBridge

-- This definition includes the removable values at s = 0 and s = 1.
/- Duplicate EtaQBridge.xi uses earlier full declaration. -/
/- Duplicate EtaQBridge.xi_differentiable uses earlier full declaration. -/
/- Duplicate EtaQBridge.xi_functional_equation uses earlier full declaration. -/
/- Duplicate EtaQBridge.xi_centered_even uses earlier full declaration. -/
/- Duplicate EtaQBridge.xi_eq_completed uses earlier full declaration. -/
/- Duplicate EtaQBridge.xi_eq_zeta uses earlier full declaration. -/
end EtaQBridge

namespace XiZeroGeometry
open EtaQBridge Set

/- Duplicate XiZeroGeometry.xi_zero_value uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.xi_one_value uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.xi_ne_zero_right uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.xi_ne_zero_left uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.xi_zero_iff uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.xi_zero_reflection uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.xi_zeros_compact_finite uses earlier full declaration. -/
/- Duplicate XiZeroGeometry.centered_zero_strip uses earlier full declaration. -/
end XiZeroGeometry

namespace XiMultiplicity
open EtaQBridge Set Filter Topology

/- Duplicate XiMultiplicity.xi_analytic uses earlier full declaration. -/
/- Duplicate XiMultiplicity.xi_order_finite uses earlier full declaration. -/
/- Duplicate XiMultiplicity.xi_multiplicity_pos uses earlier full declaration. -/
/- Duplicate XiMultiplicity.xi_zeta_order_eq uses earlier full declaration. -/
/- Duplicate XiMultiplicity.xi_zeta_multiplicity_eq uses earlier full declaration. -/
/- Duplicate XiMultiplicity.xi_zero_set_countable uses earlier full declaration. -/
/- Duplicate XiMultiplicity.UpperZero uses earlier full declaration. -/
/- Duplicate XiMultiplicity.upperZero_countable uses earlier full declaration. -/
/- Duplicate XiMultiplicity.Occurrence uses earlier full declaration. -/
/- Duplicate XiMultiplicity.occurrence_countable uses earlier full declaration. -/
/- Duplicate XiMultiplicity.location uses earlier full declaration. -/
/- Duplicate XiMultiplicity.occurrence_location uses earlier full declaration. -/
/- Duplicate XiMultiplicity.every_upper_zero_occurs uses earlier full declaration. -/
/- Duplicate XiMultiplicity.fiberEquiv uses earlier full declaration. -/
/- Duplicate XiMultiplicity.fiber_card uses earlier full declaration. -/
/- Duplicate XiMultiplicity.occurrences_compact_finite uses earlier full declaration. -/
/- Duplicate XiMultiplicity.occurrences_bounded_height_finite uses earlier full declaration. -/
/- Duplicate XiMultiplicity.occurrence_indexing uses earlier full declaration. -/
/- Duplicate XiMultiplicity.locationFiberEquiv uses earlier full declaration. -/
/- Duplicate XiMultiplicity.complete_countable_zero_index uses earlier full declaration. -/
/- Duplicate XiMultiplicity.xi_meromorphic_order uses earlier full declaration. -/
end XiMultiplicity

section QBridgeGeneric
universe u
variable {ι : Type u} [Countable ι]
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace ReciprocalCounting

/- Duplicate ReciprocalCounting.indicator_integrable uses earlier full declaration. -/
/- Duplicate ReciprocalCounting.indicator_integral uses earlier full declaration. -/
/- Duplicate ReciprocalCounting.summable_inverse_from_sublinear_count uses earlier full declaration. -/
end ReciprocalCounting



open scoped BigOperators
open Set Filter Topology
namespace HadamardSeries

/- Duplicate HadamardSeries.domain uses earlier full declaration. -/
/- Duplicate HadamardSeries.domain_open uses earlier full declaration. -/
/- Duplicate HadamardSeries.domain_convex uses earlier full declaration. -/
/- Duplicate HadamardSeries.zero_mem uses earlier full declaration. -/
/- Duplicate HadamardSeries.realpart_pos uses earlier full declaration. -/
/- Duplicate HadamardSeries.denominator_nonzero uses earlier full declaration. -/
/- Duplicate HadamardSeries.inverse_bound uses earlier full declaration. -/
/- Duplicate HadamardSeries.inverse_power_bound uses earlier full declaration. -/
/- Duplicate HadamardSeries.pole_power_summable uses earlier full declaration. -/
/- Duplicate HadamardSeries.log_atom_derivative uses earlier full declaration. -/
/- Duplicate HadamardSeries.log_series_derivative uses earlier full declaration. -/
/- Duplicate HadamardSeries.log_series_summable uses earlier full declaration. -/
/- Duplicate HadamardSeries.canonical_product_hasProd uses earlier full declaration. -/
/- Duplicate HadamardSeries.canonical_product_eq_exp uses earlier full declaration. -/
/- Duplicate HadamardSeries.canonical_product_derivative uses earlier full declaration. -/
/- Duplicate HadamardSeries.pole_atom_derivative uses earlier full declaration. -/
/- Duplicate HadamardSeries.pole_series_derivative uses earlier full declaration. -/
/- Duplicate HadamardSeries.log_series_iteratedDeriv uses earlier full declaration. -/
end HadamardSeries


open MeasureTheory Set Filter Topology
namespace CanonicalQBridge
/- Duplicate CanonicalQBridge.real_log_iteratedDeriv uses earlier full declaration. -/
/- Duplicate CanonicalQBridge.positive_function_log_identity uses earlier full declaration. -/
end CanonicalQBridge
end
end QBridgeGeneric
open Set Filter Topology
open scoped BigOperators
namespace CanonicalQBridge
variable {ι : Type*} [Countable ι]

/- Duplicate CanonicalQBridge.original_Q_spectral_identity uses earlier full declaration. -/
end CanonicalQBridge
noncomputable section
namespace CountedQBridge
variable {ι : Type*} [Countable ι]
/- Duplicate CountedQBridge.pole uses earlier full declaration. -/
/- Duplicate CountedQBridge.pole_re uses earlier full declaration. -/
/- Duplicate CountedQBridge.pole_im uses earlier full declaration. -/
/- Duplicate CountedQBridge.pole_real_lower uses earlier full declaration. -/
/- Duplicate CountedQBridge.pole_inverse_summable uses earlier full declaration. -/
end CountedQBridge
end
noncomputable section
variable {ι : Type*} [Countable ι]
namespace ActualXiBranches
open EtaQBridge XiMultiplicity Set
/- Duplicate ActualXiBranches.G uses earlier full declaration. -/
/- Duplicate ActualXiBranches.G_continuous uses earlier full declaration. -/
/- Duplicate ActualXiBranches.G_quarter uses earlier full declaration. -/
/- Duplicate ActualXiBranches.continuous_nonzero_positive uses earlier full declaration. -/
/- Duplicate ActualXiBranches.G_positive_from_product uses earlier full declaration. -/
end ActualXiBranches

namespace ActualXiBranches
open EtaQBridge XiMultiplicity Set
/- Duplicate ActualXiBranches.gamma uses earlier full declaration. -/
/- Duplicate ActualXiBranches.eps uses earlier full declaration. -/
/- Duplicate ActualXiBranches.B uses earlier full declaration. -/
/- Duplicate ActualXiBranches.Q uses earlier full declaration. -/
/- Duplicate ActualXiBranches.eps_bound uses earlier full declaration. -/
/- Duplicate ActualXiBranches.B_squared_zero uses earlier full declaration. -/
end ActualXiBranches
end
namespace ActualXiBranches
open XiMultiplicity Set Filter Topology

/- Duplicate ActualXiBranches.original_Q_identity_from_inputs uses earlier full declaration. -/
/- Duplicate ActualXiBranches.scale_identity uses earlier full declaration. -/
/- Duplicate ActualXiBranches.small_scale_Q_from_identity uses earlier full declaration. -/
/- Duplicate ActualXiBranches.Q_one_nonneg_from_identity uses earlier full declaration. -/
end ActualXiBranches
namespace ActualXiBranches
open XiMultiplicity Filter Topology

theorem large_scale_Q_from_inputs
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (verified : ∀ i : Occurrence, gamma i ≤ 1000 → eps i = 0)
    (anchor : ∃ i : Occurrence, gamma i ≤ 100)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (u : ℕ → ℝ) (hu : ∀ j, 0 < u j)
    (hscale : Tendsto (fun (j : ℕ) => (k j : ℝ)/(u j)^2) atTop atTop) :
    ∀ᶠ j : ℕ in atTop, 0 < Q (k j) (u j) := by
  obtain ⟨a,ha⟩ := anchor
  have hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2 :=
    fun i => CountedQBridge.pole_re _ _
  have hc : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ) := by
    intro i hi
    simp only [B, CountedQBridge.pole, hi, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, mul_zero, zero_mul, Complex.ofReal_zero]
  have hpos := BranchAnchorRepair.spectral_sum_eventually_positive_from_counting
    gamma eps B hB hc lower eps_bound verified a ha C (3/4) (by norm_num)
    count k hk (fun j => (u j)^2) (fun j => sq_pos_of_pos (hu j)) hscale
  have hid := original_Q_identity_from_inputs lower C count product
  have hb : ∀ i, 1 ≤ (B i).re := fun i =>
    (CountedQBridge.pole_real_lower _ _ (lower i) (eps_bound i)).1
  have hs : Summable (fun i => 1/(B i).re) := by
    simpa only [one_div, B] using
      CountedQBridge.pole_inverse_summable gamma eps lower eps_bound C (3/4)
        (by norm_num) count
  filter_upwards [hpos, hk.eventually (eventually_ge_atTop 1)] with j hj hj1
  have hsum : Summable (fun i => (((((u j)^2 : ℝ) : ℂ)+B i)⁻¹)^(k j)) := by
    simpa only [Complex.ofReal_one, one_div] using
      BranchAnchorRepair.normalized_power_summable B hb hs ((u j)^2) 1
        (sq_pos_of_pos (hu j)) (by norm_num) (k j) hj1
  have hre : 0 < (∑' i, (((((u j)^2 : ℝ) : ℂ)+B i)⁻¹)^(k j)).re := by
    rw [← (Complex.hasSum_re hsum.hasSum).tsum_eq]
    exact hj
  rw [hid (k j) hj1 (u j) (hu j)]
  apply mul_pos (by have := hu j; positivity)
  have he : (∑' i, ((((u j)^2 : ℝ) : ℂ)/(((u j)^2 : ℂ)+B i))^(k j)) =
      ((((u j)^2 : ℝ) : ℂ)^(k j)) *
        ∑' i, (((((u j)^2 : ℝ) : ℂ)+B i)⁻¹)^(k j) := by
    simp only [Complex.ofReal_pow, div_eq_mul_inv, mul_pow, tsum_mul_left]
  rw [he, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  exact mul_pos (pow_pos (sq_pos_of_pos (hu j)) _) hre

theorem negative_Q_sequence_cannot_have_large_scale
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (verified : ∀ i : Occurrence, gamma i ≤ 1000 → eps i = 0)
    (anchor : ∃ i : Occurrence, gamma i ≤ 100)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (u : ℕ → ℝ) (hu : ∀ j, 0 < u j)
    (hnegative : ∀ j, Q (k j) (u j) < 0) :
    ¬ Tendsto (fun (j : ℕ) => (k j : ℝ)/(u j)^2) atTop atTop := by
  intro hscale
  obtain ⟨j,hj⟩ := (large_scale_Q_from_inputs lower verified anchor C count product
    k hk u hu hscale).exists
  exact (not_lt_of_ge hj.le) (hnegative j)

end ActualXiBranches


open Set Filter Topology
namespace CompactPoleLimit

theorem moving_pole_limit (B : ℂ) (hB : 0 < B.re)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    Tendsto (fun j => ((1+(lam j : ℂ)*B/(k j : ℂ))⁻¹)^(k j)) atTop
      (𝓝 (Complex.exp (-(L : ℂ)*B))) := by
  let g : ℕ → ℂ := fun j => (lam j : ℂ)*B/(k j : ℂ)
  have hkR : Tendsto (fun j => (k j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hh := ((Complex.continuous_ofReal.tendsto 0).comp (hlam.div_atTop hkR)).mul_const B
    simpa [g, Complex.ofReal_div, Complex.ofReal_natCast, div_mul_eq_mul_div] using hh
  have hkpos : ∀ᶠ j : ℕ in atTop, 0 < k j := hk.eventually (eventually_gt_atTop 0)
  have hlpos : ∀ᶠ j : ℕ in atTop, 0 < lam j := hlam.eventually (Ioi_mem_nhds hL)
  have hBn : B ≠ 0 := by intro hh; simpa [hh] using hB
  have hgn : ∀ᶠ j : ℕ in atTop, g j ≠ 0 := by
    filter_upwards [hkpos, hlpos] with j hj hl
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast ne_of_gt hl) hBn)
      (by exact_mod_cast Nat.ne_of_gt hj)
  have hgp : Tendsto g atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨hg0,hgn⟩
  have hratio : Tendsto (fun j => Complex.log (1+g j)/g j) atTop (𝓝 1) := by
    have hd := (Complex.hasDerivAt_log (z := 1) (by simp)).tendsto_slope_zero.comp hgp
    simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  have hw : Tendsto (fun j => (lam j : ℂ)*B) atTop (𝓝 ((L : ℂ)*B)) :=
    ((Complex.continuous_ofReal.tendsto L).comp hlam).mul_const B
  have hlog : Tendsto (fun j => (k j : ℂ)*Complex.log (1+g j)) atTop (𝓝 ((L : ℂ)*B)) := by
    have hh := hratio.mul hw
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hkpos,hlpos] with j hj hl
    have hn : (k j : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
    have hl' : (lam j : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hl
    dsimp [g]
    field_simp
  have hplus : ∀ᶠ j : ℕ in atTop, 1+g j ≠ 0 := by
    exact (tendsto_const_nhds.add hg0).eventually_ne (by norm_num : (1 : ℂ)+0 ≠ 0)
  have hpow : Tendsto (fun j => (1+g j)^(k j)) atTop (𝓝 (Complex.exp ((L : ℂ)*B))) := by
    apply ((Complex.continuous_exp.tendsto _).comp hlog).congr'
    filter_upwards [hplus] with j hj
    change Complex.exp ((k j : ℂ)*Complex.log (1+g j)) = (1+g j)^(k j)
    rw [Complex.exp_nat_mul, Complex.exp_log hj]
  have hi := hpow.inv₀ (Complex.exp_ne_zero _)
  simpa [g, inv_pow, Complex.exp_neg, neg_mul] using hi
end CompactPoleLimit
namespace CompactPoleLimit

theorem pole_majorant (B : ℂ) (hB : 0 < B.re) (k : ℕ) (hk : 1 ≤ k)
    (lam c : ℝ) (hc : 0 < c) (hcl : c ≤ lam) :
    ‖((1+(lam : ℂ)*B/(k : ℂ))⁻¹)^k‖ ≤ c⁻¹*B.re⁻¹ := by
  have hl : 0 < lam := hc.trans_le hcl
  have hn : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ha : 0 < lam*B.re := mul_pos hl hB
  have ht : 0 < 1+lam*B.re/(k : ℝ) := by positivity
  have he : (1+(lam : ℂ)*B/(k : ℂ)).re = 1+lam*B.re/(k : ℝ) := by
    have he' : (lam : ℂ)*B/(k : ℂ) = ((lam/(k : ℝ) : ℝ) : ℂ)*B := by
      push_cast
      ring
    rw [he']
    simp [Complex.mul_re,div_mul_eq_mul_div]
  have hr : 1+lam*B.re/(k : ℝ) ≤ ‖1+(lam : ℂ)*B/(k : ℂ)‖ := by
    rw [← he]
    exact Complex.re_le_norm _
  have hb := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ lam*B.re/(k : ℝ) by linarith [div_nonneg ha.le hn.le]) k
  have hcan : (k : ℝ)*(lam*B.re/(k : ℝ)) = lam*B.re := by field_simp
  rw [hcan] at hb
  rw [norm_pow,norm_inv]
  calc
    _ ≤ ((1+lam*B.re/(k : ℝ))⁻¹)^k :=
      pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ ht hr) k
    _ = ((1+lam*B.re/(k : ℝ))^k)⁻¹ := inv_pow _ _
    _ ≤ (1+lam*B.re)⁻¹ := inv_anti₀ (by positivity) hb
    _ ≤ (lam*B.re)⁻¹ := inv_anti₀ ha (by linarith)
    _ ≤ (c*B.re)⁻¹ := inv_anti₀ (mul_pos hc hB) (mul_le_mul_of_nonneg_right hcl hB.le)
    _ = c⁻¹*B.re⁻¹ := by rw [mul_inv_rev]; ring

theorem moving_pole_sum_limit {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 0 < (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    Tendsto (fun j => ∑' i, ((1+(lam j : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)) atTop
      (𝓝 (∑' i, Complex.exp (-(L : ℂ)*B i))) := by
  have hc : 0 < L/2 := by linarith
  have hb : ∀ᶠ j : ℕ in atTop, ∀ i,
      ‖((1+(lam j : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)‖ ≤ (L/2)⁻¹*(B i).re⁻¹ := by
    filter_upwards [hk.eventually (eventually_ge_atTop 1),
      hlam.eventually (Ioi_mem_nhds (show L/2 < L by linarith))] with j hj hl i
    exact pole_majorant (B i) (hB i) (k j) hj (lam j) (L/2) hc (le_of_lt hl)
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left ((L/2)⁻¹))
    (fun i => moving_pole_limit (B i) (hB i) k hk lam L hL hlam) hb
end CompactPoleLimit

open Set Filter Topology
namespace CompactHeatPositivity
/- A negative oscillatory contribution is dominated by the anchor divided by a squared pole. -/
theorem negative_atom_bound (a b a₀ lam : ℝ)
    (ha : 900000 ≤ a) (ha₀ : a₀ ≤ 10000) (hb : b^2 ≤ 2*a) (hl : 0 < lam) :
    -(Real.exp (-a₀*lam)/a^2) ≤ Real.exp (-a*lam)*Real.cos (b*lam) := by
  have ha0 : 0 < a := by linarith
  by_cases hcos : 0 ≤ Real.cos (b*lam)
  · exact le_trans (neg_nonpos.mpr (by positivity))
      (mul_nonneg (Real.exp_pos _).le hcos)
  have hc : Real.cos (b*lam) < 0 := lt_of_not_ge hcos
  have hphase : 2 < b^2*lam^2 := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := b*lam)
    rw [mul_pow] at hh
    linarith
  have hlam2 : 1 < a*lam^2 := by
    have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg lam)
    nlinarith
  let t := (a-a₀)*lam
  have hgap : a/2 ≤ a-a₀ := by linarith
  have ht : 0 ≤ t := mul_nonneg (by linarith : 0 ≤ a-a₀) hl.le
  have htlow : a*lam/2 ≤ t := by
    have hh := mul_le_mul_of_nonneg_right hgap hl.le
    dsimp [t]
    linarith
  have ht2 : a/4 ≤ t^2 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ a*lam/2) ht |>.2 htlow
    have hh' := mul_le_mul_of_nonneg_left hlam2.le ha0.le
    nlinarith
  have hp4 : (a/4)^4 ≤ (t^2)^4 := pow_le_pow_left₀ (by positivity) ht2 4
  have hp8 : a^4/256 ≤ t^8 := by nlinarith [hp4]
  have hex := Real.pow_div_factorial_le_exp t ht 8
  norm_num at hex
  have hsq : (10321920 : ℝ) ≤ a^2 := by nlinarith
  have hexlower : a^2 ≤ Real.exp t := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg a)
    nlinarith [sq_nonneg a]
  have hsmall : Real.exp (-t) ≤ 1/a^2 := by
    rw [Real.exp_neg,one_div]
    exact inv_anti₀ (sq_pos_of_pos ha0) hexlower
  have hfact : Real.exp (-a*lam) = Real.exp (-a₀*lam)*Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have hbound : Real.exp (-a*lam) ≤ Real.exp (-a₀*lam)/a^2 := by
    rw [hfact]
    simpa only [div_eq_mul_inv, mul_one, one_mul] using
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (-a₀*lam)).le
  have hcoslow : -1 ≤ Real.cos (b*lam) := Real.neg_one_le_cos _
  nlinarith [mul_le_mul_of_nonneg_left hcoslow (Real.exp_pos (-a*lam)).le]
end CompactHeatPositivity

open Set Filter Topology
namespace CompactHeatCounting
lemma cube_step (B h : ℝ) (hB : 0<B) (hh : 0<h) :
    1/(B+h)^3 ≤ (1/B^2-1/(B+h)^2)/(2*h) := by
  have he : (1/B^2-1/(B+h)^2)/(2*h)-1/(B+h)^3 =
      h*(3*B+h)/(2*B^2*(B+h)^3) := by field_simp; ring
  have hp : 0 ≤ h*(3*B+h)/(2*B^2*(B+h)^3) := by positivity
  linarith

lemma cube_partial (M h : ℝ) (hM : 0<M) (hh : 0<h) (N : ℕ) :
    ∑ j ∈ Finset.range N, 1/(M+((j+1 : ℕ) : ℝ)*h)^3 ≤
      (1/M^2-1/(M+(N : ℝ)*h)^2)/(2*h) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hp : 0<M+(N : ℝ)*h := by positivity
    have hs := cube_step (M+(N : ℝ)*h) h hp hh
    simp only [Nat.cast_add, Nat.cast_one] at *
    have he : M+((N : ℝ)+1)*h = M+(N : ℝ)*h+h := by ring
    rw [he]
    simp only [sub_div] at *
    linarith

lemma cube_sum_bound (M h : ℝ) (hM : 0<M) (hh : 0<h) :
    Summable (fun j : ℕ => 1/(M+(j : ℝ)*h)^3) ∧
    (∑' j : ℕ, 1/(M+(j : ℝ)*h)^3) ≤ 1/M^3+1/(2*h*M^2) := by
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N, 1/(M+(j : ℝ)*h)^3 ≤ 1/M^3+1/(2*h*M^2) := by
    intro N
    cases N with
    | zero => simp; positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hs := cube_partial M h hM hh N
      have hp : 0 ≤ 1/(M+(N : ℝ)*h)^2/(2*h) := by positivity
      have he : (1/M^2-1/(M+(N : ℝ)*h)^2)/(2*h) =
        1/(2*h*M^2)-1/(M+(N : ℝ)*h)^2/(2*h) := by ring
      rw [he] at hs
      linarith
  have hs := summable_of_sum_range_le (fun j => by positivity) hpart
  refine ⟨hs, ?_⟩
  exact le_of_tendsto' hs.hasSum.tendsto_sum_nat hpart

theorem fiber_norm_bound {ι : Type*} (f : ι → ℝ) (bin : ι → ℕ) (N K : ℕ → ℝ)
    (hK : ∀ j, 0≤K j) (hN : ∀ j, 0≤N j)
    (hc : ∀ (F : Finset ι) (j : ℕ), ((F.filter (fun i => bin i=j)).card : ℝ)≤N j)
    (hf : ∀ i, ‖f i‖≤K (bin i)) (hs : Summable (fun j => N j*K j)) :
    Summable f ∧ (∑' i, ‖f i‖)≤∑' j, N j*K j := by
  classical
  have hfinite : ∀ F : Finset ι, ∑ i ∈ F, ‖f i‖≤∑' j, N j*K j := by
    intro F
    have hid := Finset.sum_fiberwise_of_maps_to (s:=F) (t:=F.image bin)
      (g:=bin) (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) (fun i => ‖f i‖)
    rw [← hid]
    calc
      _ ≤ ∑ j ∈ F.image bin, N j*K j := by
        apply Finset.sum_le_sum
        intro j hj
        have hsum : ∑ i ∈ F.filter (fun i => bin i=j), ‖f i‖ ≤
            ((F.filter (fun i => bin i=j)).card : ℝ)*K j := by
          calc
            _ ≤ ∑ i ∈ F.filter (fun i => bin i=j), K j := by
              apply Finset.sum_le_sum
              intro i hi
              have he := (Finset.mem_filter.mp hi).2
              simpa only [he] using hf i
            _ = _ := by simp
        exact hsum.trans (mul_le_mul_of_nonneg_right (hc F j) (hK j))
      _ ≤ ∑' j, N j*K j := hs.sum_le_tsum _ (fun j _ => mul_nonneg (hN j) (hK j))
  have hn := summable_of_sum_le (fun i => norm_nonneg (f i)) hfinite
  refine ⟨hn.of_norm_bounded (fun i => le_rfl), ?_⟩
  exact tsum_le_of_sum_le' (tsum_nonneg (fun j => mul_nonneg (hN j) (hK j))) hfinite
end CompactHeatCounting
namespace CompactHeatCounting

theorem offline_inverse_square_bound {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 1000 < g i) (he : ∀ i, |e i| ≤ 1/2)
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3)) :
    Summable (fun i => 1/((g i)^2-(e i)^2)^2) ∧
      (∑' i, 1/((g i)^2-(e i)^2)^2) ≤ 1/2 := by
  classical
  let bin : ι → ℕ := fun i => ⌊g i-1000⌋₊
  have hb (i : ι) : 1000+(bin i : ℝ) ≤ g i ∧ g i < 1000+(bin i : ℝ)+1 := by
    have hlo := Nat.floor_le (show 0 ≤ g i-1000 by linarith [hg i])
    have hhi := Nat.lt_floor_add_one (g i-1000)
    change 1000+(⌊g i-1000⌋₊ : ℝ) ≤ g i ∧ g i < 1000+(⌊g i-1000⌋₊ : ℝ)+1
    constructor <;> linarith
  have ht (j : ℕ) : 1000 ≤ 1000+(j : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hc (F : Finset ι) (j : ℕ) : ((F.filter (fun i => bin i=j)).card : ℝ) ≤
      100*(1000+(j : ℝ)) := by
    have hh := hcount (1000+(j : ℝ)) (ht j) (F.filter (fun i => bin i=j)) (by
      intro i hi
      simpa only [(Finset.mem_filter.mp hi).2] using hb i)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 1000+(j : ℝ)+3)
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hden (i : ι) : (1000+(bin i : ℝ))^2/2 ≤ (g i)^2-(e i)^2 := by
    have he2 : (e i)^2 ≤ 1/4 := by have := abs_le.mp (he i); nlinarith
    have hg2 : (1000+(bin i : ℝ))^2 ≤ (g i)^2 :=
      sq_le_sq₀ (by positivity) (by linarith [hg i]) |>.2 (hb i).1
    nlinarith [sq_nonneg (1000+(bin i : ℝ)-1), ht (bin i)]
  have hden0 (i : ι) : 0 < (g i)^2-(e i)^2 :=
    lt_of_lt_of_le (by positivity) (hden i)
  have hf (i : ι) : ‖1/((g i)^2-(e i)^2)^2‖ ≤ 4/(1000+(bin i : ℝ))^4 := by
    rw [Real.norm_of_nonneg (by positivity)]
    have hh := one_div_le_one_div_of_le
      (by positivity : 0 < ((1000+(bin i : ℝ))^2/2)^2)
      (sq_le_sq₀ (by positivity) (hden0 i).le |>.2 (hden i))
    calc
      _ ≤ 1/((1000+(bin i : ℝ))^2/2)^2 := hh
      _ = _ := by field_simp; ring
  have hcube := cube_sum_bound 1000 1 (by norm_num) (by norm_num)
  have heq : (fun j : ℕ => (100*(1000+(j : ℝ)))*(4/(1000+(j : ℝ))^4)) =
      (fun j : ℕ => 400*(1/(1000+(j : ℝ)*1)^3)) := by
    funext j
    field_simp
    ring
  have hseries : Summable (fun j : ℕ => (100*(1000+(j : ℝ)))*(4/(1000+(j : ℝ))^4)) := by
    rw [heq]
    exact hcube.1.mul_left 400
  have hh := fiber_norm_bound (fun i => 1/((g i)^2-(e i)^2)^2) bin
    (fun j => 100*(1000+(j : ℝ))) (fun j => 4/(1000+(j : ℝ))^4)
    (fun j => by positivity) (fun j => by positivity) hc hf hseries
  refine ⟨hh.1,?_⟩
  have hnorm : (fun i => ‖1/((g i)^2-(e i)^2)^2‖) = (fun i => 1/((g i)^2-(e i)^2)^2) := by
    funext i
    exact Real.norm_of_nonneg (by positivity)
  rw [hnorm] at hh
  rw [heq,tsum_mul_left] at hh
  have hm := mul_le_mul_of_nonneg_left hcube.2 (by norm_num : (0 : ℝ) ≤ 400)
  norm_num at hm
  linarith [hh.2]
end CompactHeatCounting

namespace CompactHeatPositivity

theorem heat_sum_positive {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 2 ≤ g i) (he : ∀ i, |e i| ≤ 1/2)
    (verified : ∀ i, g i ≤ 1000 → e i = 0)
    (anchor : ∃ i, g i ≤ 100)
    (hs : Summable (fun i => ((g i)^2-(e i)^2)⁻¹))
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (lam : ℝ) (hl : 0 < lam) :
    0 < ∑' i, Real.exp (-((g i)^2-(e i)^2)*lam)*Real.cos ((2*e i*g i)*lam) := by
  classical
  let a : ι → ℝ := fun i => (g i)^2-(e i)^2
  let H : ι → ℝ := fun i => Real.exp (-a i*lam)*Real.cos ((2*e i*g i)*lam)
  let O : Set ι := {i | e i ≠ 0}
  have he2 (i : ι) : (e i)^2 ≤ 1/4 := by have := abs_le.mp (he i); nlinarith
  have ha (i : ι) : 1 ≤ a i := by dsimp [a]; nlinarith [hg i, he2 i]
  have ha0 (i : ι) : 0 < a i := lt_of_lt_of_le (by norm_num) (ha i)
  have hheat : Summable H := by
    apply (hs.mul_left lam⁻¹).of_norm_bounded
    intro i
    have hx : 0 < a i*lam := mul_pos (ha0 i) hl
    have hex : a i*lam ≤ Real.exp (a i*lam) := by linarith [Real.add_one_le_exp (a i*lam)]
    have hb : Real.exp (-a i*lam) ≤ lam⁻¹*(a i)⁻¹ := by
      rw [neg_mul, Real.exp_neg]
      have hh := inv_anti₀ hx hex
      simpa only [mul_inv_rev] using hh
    dsimp [H]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le).trans
      (by simpa only [mul_one] using hb)
  have hoffhigh (i : O) : 1000 < g i := by
    by_contra hh
    exact i.property (verified i (le_of_not_gt hh))
  have hoffcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset O,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3) := by
    intro T hT F hF
    have hh := hcount T hT (F.map (Function.Embedding.subtype _)) (by
      intro i hi
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hi
      exact hF v hv)
    simpa using hh
  have hw := CompactHeatCounting.offline_inverse_square_bound (fun i : O => g i)
    (fun i : O => e i) hoffhigh (fun i => he i) hoffcount
  obtain ⟨i₀,hi₀⟩ := anchor
  have he₀ : e i₀ = 0 := verified i₀ (by linarith)
  have hi₀' : i₀ ∈ Oᶜ := by simpa [O] using he₀
  let A : ℝ := Real.exp (-(g i₀)^2*lam)
  have hA : 0 < A := Real.exp_pos _
  have hofflower (i : O) : -A/(a i)^2 ≤ H i := by
    have haoff : 900000 ≤ a i := by dsimp [a]; nlinarith [hoffhigh i,he2 i]
    have haanchor : (g i₀)^2 ≤ 10000 := by nlinarith [hg i₀]
    have hb : (2*e i*g i)^2 ≤ 2*a i := by
      have hh := mul_le_mul_of_nonneg_right (he2 i) (sq_nonneg (g i))
      dsimp [a]
      nlinarith [hg i,he2 i]
    simpa only [A,H,neg_div] using negative_atom_bound (a i) (2*e i*g i) ((g i₀)^2) lam haoff haanchor hb hl
  have hwoff : Summable (fun i : O => -A/(a i)^2) := by
    simpa only [a,mul_one_div] using hw.1.mul_left (-A)
  have hoff := hwoff.tsum_le_tsum hofflower (hheat.subtype (fun i => i ∈ O))
  have heq : (∑' i : O, -A/(a i)^2) = -A*(∑' i : O, 1/(a i)^2) := by
    simp only [div_eq_mul_inv,mul_one,one_mul,tsum_mul_left]
  rw [heq] at hoff
  have hwA : -A/2 ≤ -A*(∑' i : O, 1/(a i)^2) := by
    have hh := mul_le_mul_of_nonpos_left hw.2 (by linarith : -A ≤ 0)
    simpa only [a,mul_one_div] using hh
  have hcritical : A ≤ ∑' i : ↥(Oᶜ), H i := by
    have hh := (hheat.subtype (fun i => i ∈ Oᶜ)).sum_le_tsum {⟨i₀,hi₀'⟩} (by
      intro i hi
      have hei : e i = 0 := Classical.not_not.mp i.property
      dsimp [H]
      simp only [hei,mul_zero,zero_mul,Real.cos_zero,mul_one]
      exact (Real.exp_pos _).le)
    simpa [H,a,he₀,A] using hh
  have hsplit := hheat.tsum_subtype_add_tsum_subtype_compl O
  change (∑' i : O, H i)+(∑' i : ↥(Oᶜ), H i) = ∑' i, H i at hsplit
  change 0 < ∑' i, H i
  linarith
end CompactHeatPositivity

namespace BranchCompactScale
open Set Filter Topology

theorem exp_family_summable {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 0 < (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (L : ℝ) (hL : 0 < L) : Summable (fun i => Complex.exp (-(L : ℂ)*B i)) := by
  apply (hs.mul_left L⁻¹).of_norm_bounded
  intro i
  rw [Complex.norm_exp]
  have hre : (-(L : ℂ)*B i).re = -(L*(B i).re) := by simp [Complex.mul_re]
  rw [hre,Real.exp_neg]
  have hh : L*(B i).re ≤ Real.exp (L*(B i).re) := by
    linarith [Real.add_one_le_exp (L*(B i).re)]
  have hi := inv_anti₀ (mul_pos hL (hB i)) hh
  simpa only [mul_inv_rev,mul_comm] using hi

theorem compact_scale_eventually_positive {ι : Type*} (g e : ι → ℝ)
    (hg : ∀ i, 2 ≤ g i) (he : ∀ i, |e i| ≤ 1/2)
    (verified : ∀ i, g i ≤ 1000 → e i = 0)
    (anchor : ∃ i, g i ≤ 100)
    (hs : Summable (fun i => ((g i)^2-(e i)^2)⁻¹))
    (hcount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, T ≤ g i ∧ g i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (lam : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hlam : Tendsto lam atTop (𝓝 L)) :
    ∀ᶠ j : ℕ in atTop, 0 <
      (∑' i, ((1+(lam j : ℂ)*
        ((((g i)^2-(e i)^2 : ℝ) : ℂ)-(2*e i*g i : ℝ)*Complex.I)/(k j : ℂ))⁻¹)^(k j)).re := by
  let B : ι → ℂ := fun i => (((g i)^2-(e i)^2 : ℝ) : ℂ)-(2*e i*g i : ℝ)*Complex.I
  have hre (i : ι) : (B i).re = (g i)^2-(e i)^2 := by simp [B,Complex.mul_re,pow_two]
  have hb : ∀ i, 0 < (B i).re := by
    intro i
    rw [hre]
    have he2 : (e i)^2 ≤ 1/4 := by have := abs_le.mp (he i); nlinarith
    nlinarith [hg i]
  have hs' : Summable (fun i => (B i).re⁻¹) := by simpa only [hre] using hs
  have hl := CompactPoleLimit.moving_pole_sum_limit B hb hs' k hk lam L hL hlam
  have hreal := (Complex.continuous_re.tendsto _).comp hl
  have hex := exp_family_summable B hb hs' L hL
  have hsum := Complex.reCLM.map_tsum hex
  change (∑' i, Complex.exp (-(L : ℂ)*B i)).re = ∑' i, (Complex.exp (-(L : ℂ)*B i)).re at hsum
  have hterm (i : ι) : (Complex.exp (-(L : ℂ)*B i)).re =
      Real.exp (-((g i)^2-(e i)^2)*L)*Real.cos ((2*e i*g i)*L) := by
    rw [Complex.exp_re]
    have hr : (-(L : ℂ)*B i).re = -((g i)^2-(e i)^2)*L := by
      simp [B,Complex.mul_re,pow_two]
      ring
    have hi : (-(L : ℂ)*B i).im = (2*e i*g i)*L := by
      simp [B,Complex.mul_im,pow_two,Complex.mul_re]
      ring
    rw [hr,hi]
  simp only [hterm] at hsum
  have hpos : 0 < (∑' i, Complex.exp (-(L : ℂ)*B i)).re := by
    rw [hsum]
    exact CompactHeatPositivity.heat_sum_positive g e hg he verified anchor hs hcount L hL
  exact hreal.eventually (Ioi_mem_nhds hpos)
end BranchCompactScale

open Set Filter Topology
namespace ScaleAssembly

theorem positive_compact_subsequence (lam : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ n, c ≤ lam n)
    (noinf : ∀ phi : ℕ → ℕ, Tendsto phi atTop atTop →
      ¬ Tendsto (lam ∘ phi) atTop atTop) :
    ∃ L > 0, ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (lam ∘ phi) atTop (𝓝 L) := by
  have hbounded : BddAbove (Set.range lam) := by
    by_contra hnb
    have he (n : ℕ) : ∃ j : ℕ, n ≤ j ∧ (n : ℝ) ≤ lam j := by
      let F := Finset.range (n+1)
      have hF : F.Nonempty := ⟨0,by simp [F]⟩
      let M := F.sup' hF lam
      obtain ⟨y,⟨j,rfl⟩,hy⟩ := not_bddAbove_iff.mp hnb (max (n : ℝ) M)
      have hM : M < lam j := (le_max_right _ _).trans_lt hy
      have hj : n ≤ j := by
        by_contra hh
        have hmem : j ∈ F := by simp [F]; omega
        have hh' : lam j ≤ M := Finset.le_sup' lam hmem
        linarith
      exact ⟨j,hj,((le_max_left _ _).trans_lt hy).le⟩
    choose phi hphi hlam using he
    have hp : Tendsto phi atTop atTop := tendsto_atTop_mono hphi tendsto_id
    have hl : Tendsto (lam ∘ phi) atTop atTop :=
      tendsto_atTop_mono hlam tendsto_natCast_atTop_atTop
    exact noinf phi hp hl
  obtain ⟨M,hM⟩ := hbounded
  have hmem (n : ℕ) : lam n ∈ Icc c M := ⟨hlower n,hM (Set.mem_range_self n)⟩
  obtain ⟨L,hL,phi,hphi,hl⟩ := isCompact_Icc.tendsto_subseq hmem
  exact ⟨L,hc.trans_le hL.1,phi,hphi,hl⟩
end ScaleAssembly
namespace ScaleAssembly

theorem no_negative_sequence (Q : ℕ → ℝ → ℝ)
    (small : ∃ d > (0 : ℝ), ∀ (n : ℕ), 2 ≤ n → ∀ u > 0, Real.sqrt (n : ℝ)/u < d → 0 < Q n u)
    (large : ∀ k : ℕ → ℕ, Tendsto k atTop atTop → ∀ u : ℕ → ℝ,
      (∀ j, 0 < u j) → Tendsto (fun j => (k j : ℝ)/(u j)^2) atTop atTop →
      ∀ᶠ j : ℕ in atTop, 0 < Q (k j) (u j))
    (compact : ∀ k : ℕ → ℕ, Tendsto k atTop atTop → ∀ u : ℕ → ℝ,
      (∀ j, 0 < u j) → ∀ L > (0 : ℝ),
      Tendsto (fun j => (k j : ℝ)/(u j)^2) atTop (𝓝 L) →
      ∀ᶠ j : ℕ in atTop, 0 < Q (k j) (u j))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) (hk2 : ∀ j, 2 ≤ k j)
    (u : ℕ → ℝ) (hu : ∀ j, 0 < u j) (hneg : ∀ j, Q (k j) (u j) < 0) : False := by
  let lam : ℕ → ℝ := fun j => (k j : ℝ)/(u j)^2
  obtain ⟨d,hd,hsmall⟩ := small
  have hlower (j : ℕ) : d^2 ≤ lam j := by
    have hnot : ¬ Real.sqrt (k j : ℝ)/u j < d := by
      intro hh
      exact (not_lt_of_ge (hsmall (k j) (hk2 j) (u j) (hu j) hh).le) (hneg j)
    have hle := sq_le_sq₀ hd.le (by have := hu j; positivity : 0 ≤ Real.sqrt (k j : ℝ)/u j)
      |>.2 (le_of_not_gt hnot)
    simpa only [div_pow,Real.sq_sqrt (Nat.cast_nonneg (k j))] using hle
  have noinf : ∀ phi : ℕ → ℕ, Tendsto phi atTop atTop →
      ¬ Tendsto (lam ∘ phi) atTop atTop := by
    intro phi hp hlim
    have hh := large (k ∘ phi) (hk.comp hp) (u ∘ phi) (fun j => hu (phi j)) hlim
    obtain ⟨j,hj⟩ := hh.exists
    exact (not_lt_of_ge hj.le) (hneg (phi j))
  obtain ⟨L,hL,phi,hphi,hl⟩ := positive_compact_subsequence lam (d^2) (sq_pos_of_pos hd) hlower noinf
  have hh := compact (k ∘ phi) (hk.comp hphi.tendsto_atTop) (u ∘ phi)
    (fun j => hu (phi j)) L hL hl
  obtain ⟨j,hj⟩ := hh.exists
  exact (not_lt_of_ge hj.le) (hneg (phi j))
end ScaleAssembly

namespace ActualXiBranches
open Set Filter Topology XiMultiplicity

theorem compact_scale_Q_from_inputs
    (lower : ∀ i : Occurrence, 2 ≤ gamma i)
    (verified : ∀ i : Occurrence, gamma i ≤ 1000 → eps i = 0)
    (anchor : ∃ i : Occurrence, gamma i ≤ 100)
    (C : ℝ)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^((3 : ℝ)/4))
    (unitCount : ∀ T ≥ (1000 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, T ≤ gamma i ∧ gamma i < T+1) → (F.card : ℝ) ≤ 50*Real.log (T+3))
    (product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (u : ℕ → ℝ) (hu : ∀ j, 0 < u j) (L : ℝ) (hL : 0 < L)
    (hscale : Tendsto (fun j => (k j : ℝ)/(u j)^2) atTop (𝓝 L)) :
    ∀ᶠ j : ℕ in atTop, 0 < Q (k j) (u j) := by
  have hs : Summable (fun i => (B i).re⁻¹) :=
    CountedQBridge.pole_inverse_summable gamma eps lower eps_bound C (3/4) (by norm_num) count
  have hs' : Summable (fun i => ((gamma i)^2-(eps i)^2)⁻¹) := by
    simpa only [B,CountedQBridge.pole_re] using hs
  have hpos := BranchCompactScale.compact_scale_eventually_positive gamma eps lower eps_bound
    verified anchor hs' unitCount k hk (fun j => (k j : ℝ)/(u j)^2) L hL hscale
  have hid := original_Q_identity_from_inputs lower C count product
  filter_upwards [hpos,hk.eventually (eventually_ge_atTop 1)] with j hj hj1
  have hk0 : (k j : ℂ) ≠ 0 := by exact_mod_cast (by omega : k j ≠ 0)
  have hu0 : (((u j)^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sq_pos_of_pos (hu j))
  have hsum : (∑' i : Occurrence,
      ((1+(((k j : ℝ)/(u j)^2 : ℝ) : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)) =
      ∑' i : Occurrence, ((((u j)^2 : ℝ) : ℂ)/(((u j)^2 : ℂ)+B i))^(k j) := by
    apply tsum_congr
    intro i
    have he : (((k j : ℝ)/(u j)^2 : ℝ) : ℂ)*B i/(k j : ℂ) = B i/(((u j)^2 : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [he,one_add_div hu0,inv_div]
    simp only [Complex.ofReal_pow]
  change 0 < (∑' i : Occurrence,
      ((1+(((k j : ℝ)/(u j)^2 : ℝ) : ℂ)*B i/(k j : ℂ))⁻¹)^(k j)).re at hj
  rw [hsum] at hj
  rw [hid (k j) hj1 (u j) (hu j)]
  exact mul_pos (by have := hu j; positivity) hj
end ActualXiBranches

namespace ActualXiBranches
open Set Filter Topology XiMultiplicity

theorem concrete_unit_count (T : ℝ) (hT : 1000 ≤ T) (F : Finset Occurrence)
    (hF : ∀ i ∈ F, T ≤ gamma i ∧ gamma i < T+1) :
    (F.card : ℝ) ≤ 50*Real.log (T+3) := by
  classical
  let N : ℝ → ℝ := fun T =>
    ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
  have hf : {i : Occurrence | T ≤ gamma i ∧ gamma i < T+1}.Finite :=
    (occurrences_bounded_height_finite (T+1)).subset (fun i hi => hi.2.le)
  let W := hf.toFinset
  have hc : F.card ≤ W.card := Finset.card_le_card (by
    intro i hi
    simpa [W] using hF i hi)
  have heq : Nat.card {i : Occurrence // T ≤ gamma i ∧ gamma i < T+1} = W.card := by
    letI := hf.fintype
    change Nat.card ↥({i : Occurrence | T ≤ gamma i ∧ gamma i < T+1} : Set Occurrence) = _
    simp [W,Nat.card_eq_fintype_card,Set.Finite.card_toFinset]
  have hx : (Nat.card {i : Occurrence // T ≤ gamma i ∧ gamma i < T+1} : ℝ) = N (T+1)-N T :=
    BranchActualCount.strict_and_window_occurrence_count_exact.2 T
  have hbound : (F.card : ℝ) ≤ N (T+1)-N T := by
    rw [← hx, heq]
    exact_mod_cast hc
  have hw : N (T+1)-N T ≤ 50*Real.log (T+3) :=
    BranchActualCount.unit_window_bound T (by linarith)
  exact hbound.trans hw

theorem nonnegative_from_verified_height
    (verified : ∀ i : Occurrence, gamma i ≤ 1000 → eps i = 0) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by
  let N : ℝ → ℝ := fun T =>
    ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
  have lower : ∀ i : Occurrence, 2 ≤ gamma i := fun i =>
    (XiQuantitativePublished.concrete_upper_zero_lower i).2
  have anchor : ∃ i : Occurrence, gamma i ≤ 100 := by
    obtain ⟨i,hi,hl,hu,h100⟩ := XiQuantitativePublished.concrete_upper_zero_anchor
    exact ⟨i,h100⟩
  have count : ∀ y ≥ (1 : ℝ), ∀ F : Finset Occurrence,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) :=
    BranchActualCount.original_occurrence_sublinear_bound
  have product : ∀ x > 0, ((G x/G 0 : ℝ) : ℂ) = ∏' i, (1+(x : ℂ)/B i) := by
    intro x hx
    have hh := (XiPairingPublished.concrete_G_zero_product x hx.le).2
    change ((G x/G 0 : ℝ) : ℂ) = ∏' i : Occurrence,
      (1+(x : ℂ)/(-(location i-1/2)^2)) at hh
    simpa only [B_squared_zero] using hh
  intro n hn u₀ hu₀
  by_contra hh
  have hseed : Q n u₀ < 0 := lt_of_not_ge hh
  have hn2 : 2 ≤ n := by
    by_contra hh'
    have hn1 : n = 1 := by omega
    subst n
    exact (not_lt_of_ge (qbridge_concrete_result.2.2 u₀ hu₀)) hseed
  obtain ⟨v,hv0,hv⟩ := cascade_concrete_result n hn u₀ hu₀ hseed
  have hk : Tendsto (fun j : ℕ => n+j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_left j n) tendsto_id
  exact ScaleAssembly.no_negative_sequence Q qbridge_concrete_result.2.1
    (large_scale_Q_from_inputs lower verified anchor (4*(N 600+600)) count product)
    (compact_scale_Q_from_inputs lower verified anchor (4*(N 600+600)) count concrete_unit_count product)
    (fun j => n+j) hk (fun j => by omega) v (fun j => (hv j).1) (fun j => (hv j).2.1)
end ActualXiBranches

theorem solution
    (height : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 1000 → s.re = 1/2) :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    ∀ (n : ℕ), 1 ≤ n → ∀ u > 0, 0 ≤ Q n u := by
  apply ActualXiBranches.nonnegative_from_verified_height
  intro i hi
  have hz := (XiZeroGeometry.xi_zero_iff _).mp i.1.property.1
  have him : |i.1.val.im| ≤ 1000 := by
    rw [abs_of_pos i.1.property.2]
    exact hi
  have hr := height i.1.val hz.1 hz.2.1 hz.2.2 him
  change i.1.val.re-1/2 = 0
  linarith
