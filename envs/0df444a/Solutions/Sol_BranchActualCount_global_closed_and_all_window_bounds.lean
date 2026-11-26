-- Prove2me | solution 1 for BranchActualCount.global_closed_and_all_window_bounds
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T22:32:22.242112+00:00
-- url     : https://prove2.me/submissions/583c8b7b-7cf9-4e72-a8ea-4f22485394e2

import Mathlib
import Theorems.Thm_BranchActualCount_unit_window_bound
set_option maxHeartbeats 800000
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
namespace XiMultiplicity
open EtaQBridge Set

theorem zeta_order_at_xi_zero (s : UpperZero) :
    (meromorphicOrderAt riemannZeta s.val).untopD 0 =
      (analyticOrderNatAt xi s.val : ℤ) := by
  have hr := (XiZeroGeometry.xi_zero_iff s.val).mp s.property.1
  have h1 : s.val ≠ 1 := by intro he; simp [he] at hr
  rw [(analyticOn_riemannZeta s.val h1).meromorphicOrderAt_eq,
    ← xi_zeta_order_eq s.val hr.2.1 h1,
    ← Nat.cast_analyticOrderNatAt (xi_order_finite s.val)]
  norm_cast

theorem finite_fiber_bound (F : Finset Occurrence) (s : UpperZero) :
    (F.filter (fun i => location i = s.val)).card ≤ analyticOrderNatAt xi s.val := by
  classical
  let E := (locationFiberEquiv s).trans (fiberEquiv s)
  let f : ↥(F.filter (fun i => location i = s.val)) → Fin (analyticOrderNatAt xi s.val) :=
    fun i => E ⟨i.val, (Finset.mem_filter.mp i.property).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he := E.injective hij
    exact Subtype.ext (congrArg (fun z : {i : Occurrence // location i = s.val} => z.val) he)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_fin] using hh
end XiMultiplicity
/-
Derived from smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033.
Copyright (c) 2026 Salvatore Mercuri. Released under Apache 2.0.
Full source attribution and license accompany the archive.
-/
namespace OccurrenceCountBridge
open Complex
lemma riemannZeta_one_sub_ne_zero_of_one_le_re {w : ℂ}
    (hw_re : 1 ≤ w.re) (hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0) :
    riemannZeta (1 - w) ≠ 0 := by
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre' : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre'] at hw_re; linarith
  have hw_ne_one : w ≠ 1 := by
    rintro rfl
    refine hcos ?_
    have h2 : (↑Real.pi * (1 : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_neg_nat
  have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos) hzeta_w
lemma riemannZeta_ne_zero_of_re_nonpos_im_ne_zero {z : ℂ}
    (hre : z.re ≤ 0) (him : z.im ≠ 0) : riemannZeta z ≠ 0 := by
  set w : ℂ := 1 - z with hw
  have hw_im : w.im ≠ 0 := by rw [hw]; simp [him]
  have hw_re : 1 ≤ w.re := by rw [hw]; simp; linarith
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hleft : (↑Real.pi * w / 2).im ≠ 0 := by
      rw [show (↑Real.pi * w / 2).im = Real.pi * w.im / 2 by
        simp [div_eq_mul_inv, mul_assoc]]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hw_im) two_ne_zero
    have hright : (((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im) = 0 := by
      simp [div_eq_mul_inv, mul_assoc]
    exact hleft (by rw [hk, hright])
  have hres := riemannZeta_one_sub_ne_zero_of_one_le_re hw_re hcos
  rwa [show (1 : ℂ) - w = z by rw [hw]; ring] at hres
end OccurrenceCountBridge
namespace OccurrenceCountBridge
open XiMultiplicity EtaQBridge Set

def ClosedZeros (T : ℝ) : Set ℂ := {s | s.re ∈ Set.univ ∧
  s.im ∈ Set.Ioc 0 T ∧ riemannZeta s = 0}

theorem upper_zero_of_closed {T : ℝ} {s : ℂ} (hs : s ∈ ClosedZeros T) :
    xi s = 0 ∧ 0 < s.im := by
  have hr : 0 < s.re := lt_of_not_ge (fun h =>
    riemannZeta_ne_zero_of_re_nonpos_im_ne_zero h hs.2.1.1.ne' hs.2.2)
  have hl : s.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hs.2.2)
  exact ⟨(XiZeroGeometry.xi_zero_iff s).mpr ⟨hs.2.2,hr,hl⟩,hs.2.1.1⟩

theorem closed_zeros_finite (T : ℝ) : (ClosedZeros T).Finite := by
  apply (XiZeroGeometry.xi_zeros_compact_finite (Metric.closedBall 0 (|T|+1))
    (isCompact_closedBall _ _)).subset
  intro s hs
  have hx := upper_zero_of_closed hs
  have hr := (XiZeroGeometry.xi_zero_iff s).mp hx.1
  refine ⟨?_,hx.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hb := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hr.2.1, abs_of_pos hx.2] at hb
  linarith [hr.2.2,hs.2.1.2,le_abs_self T]

noncomputable def closedCount (T : ℝ) : ℝ :=
  ∑' s : ClosedZeros T, (((meromorphicOrderAt riemannZeta (s : ℂ)).untopD 0 : ℤ) : ℝ)

theorem finite_occurrences_le_closed (T : ℝ) (F : Finset Occurrence)
    (hF : ∀ i ∈ F, (location i).im ≤ T) : (F.card : ℝ) ≤ closedCount T := by
  classical
  letI : Fintype (ClosedZeros T) := (closed_zeros_finite T).fintype
  let Z : Finset ℂ := (ClosedZeros T).toFinset
  have hmap : Set.MapsTo location (F : Set Occurrence) (Z : Set ℂ) := by
    intro i hi
    apply Set.mem_toFinset.mpr
    have hz := occurrence_location i
    exact ⟨Set.mem_univ _,⟨hz.2.2.2,hF i hi⟩,hz.1⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  have hc : closedCount T = ∑ s ∈ Z,
      (((meromorphicOrderAt riemannZeta s).untopD 0 : ℤ) : ℝ) := by
    rw [closedCount, tsum_fintype, ← Finset.sum_set_coe]
  rw [hc,hcard]
  push_cast
  apply Finset.sum_le_sum
  intro s hs
  let v : UpperZero := ⟨s,upper_zero_of_closed (Set.mem_toFinset.mp hs)⟩
  have hb := finite_fiber_bound F v
  have he := zeta_order_at_xi_zero v
  change (F.filter (fun i => location i = s)).card ≤ _ at hb
  have he' : (((meromorphicOrderAt riemannZeta s).untopD 0 : ℤ) : ℝ) =
      (analyticOrderNatAt xi s : ℝ) := by exact_mod_cast he
  rw [he']
  exact_mod_cast hb
end OccurrenceCountBridge

namespace LightZeroCount
open OccurrenceCountBridge XiMultiplicity EtaQBridge Set
def OpenZeros (T : ℝ) : Set ℂ := {s | s.re ∈ Set.univ ∧
  s.im ∈ Set.Ioo 0 T ∧ riemannZeta s = 0}
theorem open_zeros_finite (T : ℝ) : (OpenZeros T).Finite :=
  (closed_zeros_finite T).subset (fun _ hs => ⟨hs.1,⟨hs.2.1.1,hs.2.1.2.le⟩,hs.2.2⟩)
noncomputable def N (T : ℝ) : ℝ :=
  ∑' s : OpenZeros T, (((meromorphicOrderAt riemannZeta (s : ℂ)).untopD 0 : ℤ) : ℝ)
noncomputable def order (s : ℂ) : ℝ :=
  (((meromorphicOrderAt riemannZeta s).untopD 0 : ℤ) : ℝ)
theorem order_nonneg {T : ℝ} {s : ℂ} (hs : s ∈ ClosedZeros T) : 0 ≤ order s := by
  have hh := zeta_order_at_xi_zero (⟨s,upper_zero_of_closed hs⟩ : UpperZero)
  dsimp [order]
  rw [hh]
  positivity
theorem N_eq_sum (T : ℝ) : N T =
    ∑ s ∈ (open_zeros_finite T).toFinset, order s := by
  letI := (open_zeros_finite T).fintype
  have he : (open_zeros_finite T).toFinset = (OpenZeros T).toFinset := by ext s; simp
  rw [he,N,tsum_fintype,← Finset.sum_set_coe]
  rfl
theorem N_nonnegative (T : ℝ) : 0 ≤ N T := by
  rw [N_eq_sum]
  apply Finset.sum_nonneg
  intro s hs
  have h := (Set.Finite.mem_toFinset _).mp hs
  exact order_nonneg ⟨h.1,⟨h.2.1.1,h.2.1.2.le⟩,h.2.2⟩
theorem N_mono : Monotone N := by
  intro a b hab
  rw [N_eq_sum,N_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    apply (Set.Finite.mem_toFinset _).mpr
    have h := (Set.Finite.mem_toFinset _).mp hs
    exact ⟨h.1,⟨h.2.1.1,lt_of_lt_of_le h.2.1.2 hab⟩,h.2.2⟩
  · intro s hs _
    have h := (Set.Finite.mem_toFinset _).mp hs
    exact order_nonneg ⟨h.1,⟨h.2.1.1,h.2.1.2.le⟩,h.2.2⟩
theorem closed_le_shifted (T : ℝ) : closedCount T ≤ N (T+1) := by
  classical
  letI := (closed_zeros_finite T).fintype
  have hc : closedCount T = ∑ s ∈ (closed_zeros_finite T).toFinset, order s := by
    have he : (closed_zeros_finite T).toFinset = (ClosedZeros T).toFinset := by ext s; simp
    rw [he,closedCount,tsum_fintype,← Finset.sum_set_coe]
    rfl
  rw [hc,N_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    apply (Set.Finite.mem_toFinset _).mpr
    have h := (Set.Finite.mem_toFinset _).mp hs
    exact ⟨h.1,⟨h.2.1.1,by linarith [h.2.1.2]⟩,h.2.2⟩
  · intro s hs _
    have h := (Set.Finite.mem_toFinset _).mp hs
    exact order_nonneg ⟨h.1,⟨h.2.1.1,h.2.1.2.le⟩,h.2.2⟩
end LightZeroCount

namespace BranchGlobalCount

theorem integer_bound (N : ℝ → ℝ) (hm : Monotone N)
    (hw : ∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3)) :
    ∀ m : ℕ, N m ≤ N 600 + 50*(m : ℝ)*Real.log ((m : ℝ)+3) := by
  intro m
  induction m with
  | zero =>
    simpa using hm (show (0 : ℝ) ≤ 600 by norm_num)
  | succ m ih =>
    by_cases hlow : (m : ℝ) < 600
    · have hmnat : m < 600 := by exact_mod_cast hlow
      have hle : ((m+1 : ℕ) : ℝ) ≤ 600 := by exact_mod_cast (by omega : m+1 ≤ 600)
      have hp : 0 ≤ 50*((m+1 : ℕ) : ℝ)*Real.log (((m+1 : ℕ) : ℝ)+3) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
      exact (hm hle).trans (by linarith)
    · have hh := hw m (le_of_not_gt hlow)
      have hl : Real.log ((m : ℝ)+3) ≤ Real.log ((m : ℝ)+1+3) :=
        Real.log_le_log (by positivity) (by linarith)
      have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ 50*((m : ℝ)+1) by positivity)
      push_cast
      nlinarith

theorem global_bound_from_windows (N : ℝ → ℝ) (hm : Monotone N)
    (h0 : 0 ≤ N 600)
    (hw : ∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3)) :
    ∀ T ≥ (1 : ℝ), N T ≤ (N 600+600)*T^((3 : ℝ)/2) := by
  intro T hT
  have hTp : 0 < T := by linarith
  let m : ℕ := ⌊T⌋₊ + 1
  have hTm : T ≤ (m : ℝ) := by
    dsimp [m]; push_cast
    exact (Nat.lt_floor_add_one T).le
  have hmT : (m : ℝ) ≤ T+1 := by
    dsimp [m]; push_cast
    linarith [Nat.floor_le hTp.le]
  have hm2 : (m : ℝ) ≤ 2*T := by linarith
  have hlg : Real.log ((m : ℝ)+3) ≤ 6*Real.sqrt T := by
    have hlog := Real.log_le_rpow_div (show 0 ≤ (m : ℝ)+3 by positivity)
      (show (0 : ℝ) < 1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hlog
    have hs := Real.sqrt_le_sqrt (show (m : ℝ)+3 ≤ 9*T by linarith)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)] at hs
    norm_num at hs
    linarith
  have hlog0 : 0 ≤ Real.log ((m : ℝ)+3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hprod : 50*(m : ℝ)*Real.log ((m : ℝ)+3) ≤ 600*T*Real.sqrt T := by
    have ha := mul_le_mul_of_nonneg_right hm2 hlog0
    have hb := mul_le_mul_of_nonneg_left hlg (show 0 ≤ 2*T by positivity)
    nlinarith
  have hp : T^((3 : ℝ)/2) = T*Real.sqrt T := by
    rw [show (3 : ℝ)/2 = 1+1/2 by norm_num, Real.rpow_add hTp,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hpow : 1 ≤ T^((3 : ℝ)/2) := Real.one_le_rpow hT (by norm_num)
  have hN := hm hTm
  have hi := integer_bound N hm hw m
  have hb := mul_le_mul_of_nonneg_left hpow h0
  rw [hp] at *
  nlinarith

theorem shifted_bound_from_windows (N : ℝ → ℝ) (hm : Monotone N)
    (h0 : 0 ≤ N 600)
    (hw : ∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3)) :
    ∀ T ≥ (1 : ℝ), N (T+1) ≤ 4*(N 600+600)*T^((3 : ℝ)/2) := by
  intro T hT
  have hTp : 0 < T := by linarith
  have hs := Real.sqrt_le_sqrt (show T+1 ≤ 4*T by linarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hs
  norm_num at hs
  have hmul : (T+1)*Real.sqrt (T+1) ≤ 4*T*Real.sqrt T := by
    have ha := mul_le_mul_of_nonneg_right (show T+1 ≤ 2*T by linarith)
      (Real.sqrt_nonneg (T+1))
    have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*T by positivity)
    nlinarith
  have hp (x : ℝ) (hx : 0 < x) : x^((3 : ℝ)/2) = x*Real.sqrt x := by
    rw [show (3 : ℝ)/2 = 1+1/2 by norm_num, Real.rpow_add hx,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hh := global_bound_from_windows N hm h0 hw (T+1) (by linarith)
  have hb := mul_le_mul_of_nonneg_left hmul (show 0 ≤ N 600+600 by linarith)
  rw [hp (T+1) (by linarith)] at hh
  rw [hp T hTp]
  nlinarith

theorem squared_height_bound (N : ℝ → ℝ) (hm : Monotone N)
    (h0 : 0 ≤ N 600)
    (hw : ∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3)) :
    ∀ y ≥ (1 : ℝ), N (Real.sqrt y+1) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) := by
  intro y hy
  have hs : 1 ≤ Real.sqrt y := by
    have hh := Real.sqrt_le_sqrt hy
    simpa using hh
  have hh := shifted_bound_from_windows N hm h0 hw (Real.sqrt y) hs
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : 0 ≤ y)] at hh
  norm_num at hh
  simpa only [Real.sqrt_eq_rpow] using hh

end BranchGlobalCount
namespace BranchGlobalCount
theorem all_unit_windows
    (hw : ∀ T ≥ (600 : ℝ), LightZeroCount.N (T+1)-LightZeroCount.N T ≤
      50*Real.log (T+3)) :
    ∀ T ≥ (1 : ℝ), LightZeroCount.N (T+1)-LightZeroCount.N T ≤
      (LightZeroCount.N 601+50)*Real.log (T+3) := by
  intro T hT
  have hlog : 1 ≤ Real.log (T+3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  by_cases hh : 600 ≤ T
  · exact (hw T hh).trans (mul_le_mul_of_nonneg_right
      (by linarith [LightZeroCount.N_nonnegative 601]) (by linarith))
  · have hn := LightZeroCount.N_mono (show T+1 ≤ 601 by linarith)
    have hp := LightZeroCount.N_nonnegative T
    have hc := mul_le_mul_of_nonneg_left hlog (LightZeroCount.N_nonnegative 601)
    nlinarith

theorem concrete_global_bounds
    (hw : ∀ T ≥ (600 : ℝ), LightZeroCount.N (T+1)-LightZeroCount.N T ≤
      50*Real.log (T+3)) :
    (∀ T ≥ (1 : ℝ), LightZeroCount.N T ≤
      (LightZeroCount.N 600+600)*T^((3 : ℝ)/2)) ∧
    (∀ y ≥ (1 : ℝ), OccurrenceCountBridge.closedCount (Real.sqrt y) ≤
      4*(LightZeroCount.N 600+600)*y^((3 : ℝ)/4)) ∧
    (∀ T ≥ (1 : ℝ), LightZeroCount.N (T+1)-LightZeroCount.N T ≤
      (LightZeroCount.N 601+50)*Real.log (T+3)) := by
  refine ⟨global_bound_from_windows _ LightZeroCount.N_mono (LightZeroCount.N_nonnegative 600) hw, ?_,
    all_unit_windows hw⟩
  intro y hy
  exact (LightZeroCount.closed_le_shifted _).trans
    (squared_height_bound _ LightZeroCount.N_mono (LightZeroCount.N_nonnegative 600) hw y hy)
end BranchGlobalCount

theorem solution :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    let Nc : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioc 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    (∀ T ≥ (1 : ℝ), N T ≤ (N 600+600)*T^((3 : ℝ)/2)) ∧
    (∀ y ≥ (1 : ℝ), Nc (Real.sqrt y) ≤ 4*(N 600+600)*y^((3 : ℝ)/4)) ∧
    (∀ T ≥ (1 : ℝ), N (T+1)-N T ≤ (N 601+50)*Real.log (T+3)) := by
  have hw : ∀ T ≥ (600 : ℝ), LightZeroCount.N (T+1)-LightZeroCount.N T ≤ 50*Real.log (T+3) := by
    exact BranchActualCount.unit_window_bound
  exact BranchGlobalCount.concrete_global_bounds hw
