-- Prove2me | solution 1 for BranchActualCount.original_occurrence_uniform_small_scale_positive
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T07:52:35.295106+00:00
-- url     : https://prove2.me/submissions/585889d4-10ea-4be9-9478-dec601dd00d3

import Mathlib
import Theorems.Thm_BranchActualCount_global_closed_and_all_window_bounds
import Theorems.Thm_BranchActualCount_eventual_lower_density
import Theorems.Thm_BranchActualCount_strict_and_window_occurrence_count_exact
import Theorems.Thm_BranchComposition_small_scale_positive_from_counts
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

namespace LightZeroCount
noncomputable def N : ℝ → ℝ := fun T =>
  ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
    (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
theorem N_nonnegative (T : ℝ) : 0 ≤ N T := by
  have he := BranchActualCount.strict_and_window_occurrence_count_exact.1 T
  change (Nat.card {i : XiMultiplicity.Occurrence // (XiMultiplicity.location i).im < T} : ℝ) = N T at he
  rw [← he]
  positivity
end LightZeroCount
namespace OccurrenceCountBridge
open XiMultiplicity
theorem strict_occurrences_finite (T : ℝ) : {i : Occurrence | (location i).im < T}.Finite :=
  (occurrences_bounded_height_finite T).subset (fun i hi => (show (location i).im < T from hi).le)
theorem strict_count_exact (T : ℝ) :
    (Nat.card {i : Occurrence // (location i).im < T} : ℝ) = LightZeroCount.N T :=
  BranchActualCount.strict_and_window_occurrence_count_exact.1 T
theorem window_count_exact (T : ℝ) :
    (Nat.card {i : Occurrence // T ≤ (location i).im ∧ (location i).im < T+1} : ℝ) =
      LightZeroCount.N (T+1)-LightZeroCount.N T :=
  BranchActualCount.strict_and_window_occurrence_count_exact.2 T
end OccurrenceCountBridge
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace ActualSmallScale

lemma reciprocal_scale_tendsto (h : ℕ → ℝ) (hh : ∀ n, 0<h n)
    (ht : Tendsto h atTop (𝓝 0)) : Tendsto (fun n => 1/h n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hb : 0 < max b 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_right _ _)
  filter_upwards [ht.eventually_lt_const (by positivity : (0 : ℝ)<1/max b 1)] with n hn
  have hm : h n*max b 1<1 := (lt_div_iff₀ hb).1 hn
  have hr : max b 1<1/h n := (lt_div_iff₀ (hh n)).2 (by nlinarith)
  exact (le_max_left b 1).trans hr.le

/-- The concrete zeta count supplies the normalized lower-density margin. -/
theorem normalized_count_lower
    (hd : ∀ᶠ T : ℝ in atTop, T*Real.log T/(32*Real.pi) ≤ LightZeroCount.N T) (h : ℕ → ℝ) (hh : ∀ n, 0<h n)
    (ht : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1/(64*Real.pi) ≤
      h n/(1-Real.log (h n))*LightZeroCount.N (1/h n) := by
  have hi := reciprocal_scale_tendsto h hh ht
  have hcount := hi.eventually hd
  have hlog := (Real.tendsto_log_atTop.comp hi).eventually_ge_atTop 1
  filter_upwards [hcount,hlog] with n hn hl
  change 1≤Real.log (1/h n) at hl
  have he : Real.log (1/h n) = -Real.log (h n) := by simp [one_div,Real.log_inv]
  have hden : 0<1-Real.log (h n) := by linarith
  have hm := mul_le_mul_of_nonneg_left hn (div_nonneg (hh n).le hden.le)
  have heq : h n/(1-Real.log (h n))*((1/h n)*Real.log (1/h n)/(32*Real.pi))
      = Real.log (1/h n)/(32*Real.pi*(1-Real.log (h n))) := by
    field_simp [ne_of_gt (hh n),ne_of_gt hden,Real.pi_ne_zero]
  have hsmall : 1/(64*Real.pi) ≤ Real.log (1/h n)/(32*Real.pi*(1-Real.log (h n))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hl) Real.pi_pos.le]
  rw [heq] at hm
  exact hsmall.trans hm

end ActualSmallScale
namespace ActualSmallScale
open XiMultiplicity Set Filter
open scoped Topology

noncomputable def cut (T : ℝ) : Finset Occurrence :=
  (occurrences_bounded_height_finite T).toFinset

lemma mem_cut (T : ℝ) (i : Occurrence) : i ∈ cut T ↔ (location i).im ≤ T := by
  simp [cut]

lemma window_finite_bound (T : ℝ) (F : Finset Occurrence)
    (hF : ∀ i ∈ F, T ≤ (location i).im ∧ (location i).im < T+1) :
    (F.card : ℝ) ≤ LightZeroCount.N (T+1)-LightZeroCount.N T := by
  classical
  have hf : {i : Occurrence | T ≤ (location i).im ∧ (location i).im < T+1}.Finite :=
    (OccurrenceCountBridge.strict_occurrences_finite (T+1)).subset (fun i hi => hi.2)
  let W := hf.toFinset
  have hc : F.card ≤ W.card := Finset.card_le_card (by
    intro i hi
    simpa [W] using hF i hi)
  have he : Nat.card {i : Occurrence // T ≤ (location i).im ∧ (location i).im < T+1} = W.card := by
    letI := hf.fintype
    change Nat.card ↥({i : Occurrence | T ≤ (location i).im ∧ (location i).im < T+1} : Set Occurrence) = _
    simp [W,Nat.card_eq_fintype_card,Set.Finite.card_toFinset]
  rw [← OccurrenceCountBridge.window_count_exact, he]
  exact_mod_cast hc

lemma strict_le_cut (T : ℝ) : LightZeroCount.N T ≤ ((cut T).card : ℝ) := by
  classical
  let S := (OccurrenceCountBridge.strict_occurrences_finite T).toFinset
  have hc : S.card ≤ (cut T).card := Finset.card_le_card (by
    intro i hi
    apply (mem_cut T i).mpr
    have hi' : (location i).im < T := by simpa [S] using hi
    exact hi'.le)
  have he : Nat.card {i : Occurrence // (location i).im < T} = S.card := by
    letI := (OccurrenceCountBridge.strict_occurrences_finite T).fintype
    change Nat.card ↥({i : Occurrence | (location i).im < T} : Set Occurrence) = _
    simp [S,Nat.card_eq_fintype_card,Set.Finite.card_toFinset]
  rw [← OccurrenceCountBridge.strict_count_exact, he]
  exact_mod_cast hc

noncomputable def term (k : ℕ) (h : ℝ) (i : Occurrence) : ℂ :=
  (((k : ℝ)/h^2 : ℝ) : ℂ) /
    ((((k : ℝ)/h^2+(location i).im^2-((location i).re-1/2)^2 : ℝ) : ℂ) -
      (2*((location i).re-1/2)*(location i).im : ℝ)*Complex.I)

theorem actual_small_scale
    (hw : ∀ T ≥ (1 : ℝ), LightZeroCount.N (T+1)-LightZeroCount.N T ≤
      (LightZeroCount.N 601+50)*Real.log (T+3))
    (hd : ∀ᶠ T : ℝ in atTop, T*Real.log T/(32*Real.pi) ≤ LightZeroCount.N T)
    (k : ℕ → ℕ) (hk : ∀ n, 2 ≤ k n)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1)
    (ht : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ n in atTop, Summable (fun i => term (k n) (h n) i ^ k n) ∧
      0 < (∑' i, term (k n) (h n) i ^ k n).re := by
  classical
  have hL (n : ℕ) : 1 ≤ 1-Real.log (h n) := by
    have hl := Real.log_nonpos (hh n).le (hh1 n)
    linarith
  have hlower : ∀ᶠ n in atTop, 1/(64*Real.pi) ≤
      h n/(1-Real.log (h n))*((cut (1/h n)).card : ℝ) := by
    filter_upwards [normalized_count_lower hd h hh ht] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_left (strict_le_cut _) (by
      apply div_nonneg (hh n).le
      linarith [hL n]))
  have hp := BranchComposition.small_scale_positive_from_counts
    (fun i : Occurrence => (location i).re-1/2) (fun i : Occurrence => (location i).im)
    (fun i => (XiZeroGeometry.centered_zero_strip _ i.1.property.1).le)
    (fun i => i.1.property.2.le) cut mem_cut
    (LightZeroCount.N 601+50) (by linarith [LightZeroCount.N_nonnegative 601])
    (fun T hT F hF => (window_finite_bound T F hF).trans (hw T hT))
    k hk h (fun n => 1-Real.log (h n)) hh hh1 hL
    (fun n => by linarith) ht (1/(64*Real.pi)) (by positivity) hlower
  simpa only [term] using hp

end ActualSmallScale
open Filter
open scoped Topology
namespace SmallScaleQuantifiers
theorem uniform_from_sequences (P : ℕ → ℝ → Prop)
    (hseq : ∀ (k : ℕ → ℕ), (∀ n, 2 ≤ k n) →
      ∀ (h : ℕ → ℝ), (∀ n, 0 < h n) → (∀ n, h n ≤ 1) →
      Tendsto h atTop (𝓝 0) → ∀ᶠ n in atTop, P (k n) (h n)) :
    ∃ δ > (0 : ℝ), ∀ h, 0 < h → h < δ → ∀ k ≥ 2, P k h := by
  classical
  by_contra hn
  push_neg at hn
  have hb (n : ℕ) : ∃ h, 0 < h ∧ h < 1/((n : ℝ)+1) ∧ ∃ k, 2 ≤ k ∧ ¬ P k h :=
    hn (1/((n : ℝ)+1)) (by positivity)
  choose h hh hbound k hk hbad using hb
  have hh1 (n : ℕ) : h n ≤ 1 := by
    have hu : 1/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (hbound n).le.trans hu
  have ht : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hh n).le) (fun n => (hbound n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n, hn⟩ := (hseq k hk h hh hh1 ht).exists
  exact hbad n hn
end SmallScaleQuantifiers
theorem solution :
    let xi : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // xi s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt xi s.val)
    let S : ℕ → ℝ → I → ℂ := fun k h i =>
      (((((k : ℝ)/h^2 : ℝ) : ℂ) /
        ((((k : ℝ)/h^2+i.1.val.im^2-(i.1.val.re-1/2)^2 : ℝ) : ℂ) -
          (2*(i.1.val.re-1/2)*i.1.val.im : ℝ)*Complex.I)) ^ k)
    ∃ δ > (0 : ℝ), ∀ h, 0 < h → h < δ → ∀ k ≥ 2,
      Summable (S k h) ∧ 0 < (∑' i, S k h i).re := by
  dsimp only
  apply SmallScaleQuantifiers.uniform_from_sequences
  intro k hk h hh hh1 ht
  exact ActualSmallScale.actual_small_scale
    BranchActualCount.global_closed_and_all_window_bounds.2.2
    BranchActualCount.eventual_lower_density k hk h hh hh1 ht

