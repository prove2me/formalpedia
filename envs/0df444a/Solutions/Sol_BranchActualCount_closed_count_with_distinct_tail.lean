-- Prove2me | solution 1 for BranchActualCount.closed_count_with_distinct_tail
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:43:21.795146+00:00
-- url     : https://prove2.me/submissions/62ca69c5-a965-4492-b583-7c67c959be67

import Mathlib
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
namespace LightZeroCount
open OccurrenceCountBridge XiMultiplicity EtaQBridge Set

theorem order_one_le {T : ℝ} {s : ℂ} (hs : s ∈ ClosedZeros T) : 1 ≤ order s := by
  have hx := upper_zero_of_closed hs
  have hh := zeta_order_at_xi_zero (⟨s,hx⟩ : UpperZero)
  have hp := xi_multiplicity_pos s hx.1
  dsimp [order]
  rw [hh]
  exact_mod_cast hp

theorem closed_add_tail_le (T H : ℝ) (hT : 0 ≤ T) (hTH : T < H)
    (L : List ℂ) (hL : L.Nodup)
    (hz : ∀ s ∈ L, T < s.im ∧ s.im < H ∧ riemannZeta s = 0) :
    closedCount T + (L.length : ℝ) ≤ N H := by
  classical
  letI := (closed_zeros_finite T).fintype
  letI := (open_zeros_finite H).fintype
  let A : Finset ℂ := (ClosedZeros T).toFinset
  let B : Finset ℂ := L.toFinset
  let C : Finset ℂ := (OpenZeros H).toFinset
  have hAc : closedCount T = ∑ s ∈ A, order s := by
    rw [closedCount,tsum_fintype,← Finset.sum_set_coe]
    rfl
  have hNc : N H = ∑ s ∈ C, order s := by
    rw [N,tsum_fintype,← Finset.sum_set_coe]
    rfl
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro s ha hb
    have ha' : s ∈ ClosedZeros T := Set.mem_toFinset.mp ha
    have hb' : s ∈ L := List.mem_toFinset.mp hb
    exact (not_lt_of_ge ha'.2.1.2) (hz s hb').1
  have hsub : A ∪ B ⊆ C := by
    intro s hs
    apply Set.mem_toFinset.mpr
    rcases Finset.mem_union.mp hs with ha | hb
    · have hh : s ∈ ClosedZeros T := Set.mem_toFinset.mp ha
      exact ⟨hh.1,⟨hh.2.1.1,hh.2.1.2.trans_lt hTH⟩,hh.2.2⟩
    · have hh := hz s (List.mem_toFinset.mp hb)
      exact ⟨Set.mem_univ _,⟨hT.trans_lt hh.1,hh.2.1⟩,hh.2.2⟩
  have hsum : (∑ s ∈ A ∪ B, order s) ≤ ∑ s ∈ C, order s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro s hs _
    have hh : s ∈ OpenZeros H := Set.mem_toFinset.mp hs
    exact order_nonneg ⟨hh.1,⟨hh.2.1.1,hh.2.1.2.le⟩,hh.2.2⟩
  have htail : (L.length : ℝ) ≤ ∑ s ∈ B, order s := by
    have hh := Finset.card_nsmul_le_sum B order (1:ℝ) (by
      intro s hs
      have hz' := hz s (List.mem_toFinset.mp hs)
      exact order_one_le (T:=H) ⟨Set.mem_univ _,⟨hT.trans_lt hz'.1,hz'.2.1.le⟩,hz'.2.2⟩)
    simpa [B,List.toFinset_card_of_nodup hL] using hh
  rw [Finset.sum_union hdisj] at hsum
  rw [hAc,hNc]
  linarith
#print axioms closed_add_tail_le
end LightZeroCount
theorem solution :
  let N : ℝ → ℝ := fun H =>
    ∑' z : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 H ∧ s ∈ {w : ℂ | riemannZeta w=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (z : ℂ)).untopD 0 : ℤ) : ℝ)
  let Nc : ℝ → ℝ := fun T =>
    ∑' z : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioc 0 T ∧ s ∈ {w : ℂ | riemannZeta w=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (z : ℂ)).untopD 0 : ℤ) : ℝ)
  ∀ T H : ℝ, 0 ≤ T → T < H → ∀ L : List ℂ, L.Nodup →
    (∀ s ∈ L, T < s.im ∧ s.im < H ∧ riemannZeta s=0) →
    Nc T + (L.length : ℝ) ≤ N H := by
  dsimp only
  simpa [LightZeroCount.N,LightZeroCount.OpenZeros,
    OccurrenceCountBridge.closedCount,OccurrenceCountBridge.ClosedZeros] using
    LightZeroCount.closed_add_tail_le
#print axioms solution
