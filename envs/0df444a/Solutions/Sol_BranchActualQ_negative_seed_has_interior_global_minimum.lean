-- Prove2me | solution 1 for BranchActualQ.negative_seed_has_interior_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T09:46:12.936987+00:00
-- url     : https://prove2.me/submissions/94d7021e-5713-4021-b70b-33ad3d664777

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

theorem solution :
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
