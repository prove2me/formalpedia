-- Prove2me | solution 1 for ConvexRiskFn.Order.strassen_icx_coupling
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T06:39:14.468897+00:00
-- url     : https://prove2.me/submissions/416210c6-1388-403b-b70b-243a5e08d8a3

import Mathlib
import Definitions.Def_ConvexRiskFn_Order_Setting
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
set_option autoImplicit false

open MeasureTheory Set

namespace RiskOrderApproximation
lemma finite_range_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (s : SimpleFunc Ω ℝ) :
    (range (P[X|MeasurableSpace.comap s inferInstance])).Finite := by
  have hm : StronglyMeasurable[MeasurableSpace.comap s inferInstance]
      (P[X|MeasurableSpace.comap s inferInstance]) := stronglyMeasurable_condExp
  obtain ⟨g, _, he⟩ := hm.exists_eq_measurable_comp
  rw [he, range_comp]
  exact s.finite_range.image g

lemma conditional_approximation_error {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (s : SimpleFunc Ω ℝ) :
    (∫ ω, |X ω - P[X|MeasurableSpace.comap s inferInstance] ω| ∂P) ≤
      2 * ∫ ω, |X ω - s ω| ∂P := by
  let m := MeasurableSpace.comap s inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := s.measurable.comap_le
  have hs : Integrable s P := s.integrable_of_isFiniteMeasure
  have hsm : StronglyMeasurable[m] s := (comap_measurable s).stronglyMeasurable
  have hCs : P[s|m] = s := condExp_of_stronglyMeasurable hm hsm hs
  have hsub := condExp_sub hX hs m
  rw [hCs] at hsub
  have hbound : ∀ᵐ ω ∂P, |X ω - P[X|m] ω| ≤ |X ω - s ω| + |P[X - ⇑s|m] ω| := by
    filter_upwards [hsub] with ω hω
    have ht := abs_sub_le (X ω) (s ω) (P[X|m] ω)
    have he : s ω - P[X|m] ω = -P[X - ⇑s|m] ω := by
      change P[X - ⇑s|m] ω = P[X|m] ω - s ω at hω
      linarith
    rw [he, abs_neg] at ht
    exact ht
  calc
    (∫ ω, |X ω - P[X|m] ω| ∂P) ≤ ∫ ω, |X ω - s ω| + |P[X - ⇑s|m] ω| ∂P :=
      integral_mono_ae (hX.sub integrable_condExp).abs
        ((hX.sub hs).abs.add integrable_condExp.abs) hbound
    _ = (∫ ω, |X ω - s ω| ∂P) + ∫ ω, |P[X - ⇑s|m] ω| ∂P :=
      integral_add (hX.sub hs).abs integrable_condExp.abs
    _ ≤ (∫ ω, |X ω - s ω| ∂P) + ∫ ω, |X ω - s ω| ∂P :=
      add_le_add le_rfl (integral_abs_condExp_le (μ := P) (m := m) (X - ⇑s))
    _ = 2 * ∫ ω, |X ω - s ω| ∂P := by ring

lemma exists_simple_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : Integrable X P) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : SimpleFunc Ω ℝ, (∫ ω, |X ω - s ω| ∂P) < ε := by
  have hm : MemLp X 1 P := memLp_one_iff_integrable.mpr hX
  obtain ⟨s, hs, hsm⟩ := hm.exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨s, ?_⟩
  have hreal := ENNReal.toReal_lt_of_lt_ofReal hs
  rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
    (hX.sub (memLp_one_iff_integrable.mp hsm)).aestronglyMeasurable] at hreal
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hreal

lemma exists_finite_lower_approximation {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Ω → ℝ, Measurable A ∧ (range A).Finite ∧ Integrable A P ∧
      StochasticOrders.MonotoneConvex.IcxOrder P P A X ∧
      (∫ ω, |X ω - A ω| ∂P) < ε := by
  obtain ⟨s, hs⟩ := exists_simple_L1 P X hX (ε / 4) (by positivity)
  let m := MeasurableSpace.comap s inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := s.measurable.comap_le
  refine ⟨P[X|m], stronglyMeasurable_condExp.mono hm |>.measurable,
    finite_range_condExp P X s, integrable_condExp, ?_, ?_⟩
  · intro φ _ hφ hiA hiX
    have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
    have hj := hφ.map_condExp_le_univ hm hc.lowerSemicontinuous hX hiX
    calc
      (∫ ω, φ (P[X|m] ω) ∂P) ≤ ∫ ω, P[φ ∘ X|m] ω ∂P :=
        integral_mono_ae hiA integrable_condExp hj
      _ = ∫ ω, φ (X ω) ∂P := integral_condExp hm
  · have hb := conditional_approximation_error P X hX s
    dsimp only [m] at *
    linarith

lemma stopLoss_integral_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) (t : ℝ) :
    (∫ ω, max (X ω - t) 0 ∂P) ≤
      (∫ ω, max (Y ω - t) 0 ∂P) + ∫ ω, |X ω - Y ω| ∂P := by
  have hiX := (hX.sub (integrable_const t)).pos_part
  have hiY := (hY.sub (integrable_const t)).pos_part
  have hb : ∀ ω, max (X ω - t) 0 ≤ max (Y ω - t) 0 + |X ω - Y ω| := by
    intro ω
    have ha := abs_max_sub_max_le_abs (X ω - t) (Y ω - t) 0
    rw [sub_sub_sub_cancel_right] at ha
    have hle := le_abs_self (max (X ω - t) 0 - max (Y ω - t) 0)
    linarith
  calc
    (∫ ω, max (X ω - t) 0 ∂P) ≤ ∫ ω, max (Y ω - t) 0 + |X ω - Y ω| ∂P :=
      integral_mono hiX (hiY.add (hX.sub hY).abs) hb
    _ = _ := integral_add hiY (hX.sub hY).abs

end RiskOrderApproximation
open MeasureTheory Set Finset
open scoped Classical
namespace RiskOrderFiniteLaw

noncomputable def finiteLaw {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (x : ι → α) (p : ι → ℝ) : Measure α :=
  Measure.sum (fun i => ENNReal.ofReal (p i) • Measure.dirac (x i))

lemma finiteLaw_apply {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (s : Set α) :
    finiteLaw x p s = ∑ i, if x i ∈ s then ENNReal.ofReal (p i) else 0 := by
  classical
  simp [finiteLaw, Measure.sum_apply_of_countable, tsum_fintype, indicator_apply]

lemma finiteLaw_integrable {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (f : α → ℝ) : Integrable f (finiteLaw x p) := by
  apply integrable_sum_dirac (fun i => ENNReal.ofReal_ne_top)
  exact summable_of_hasFiniteSupport (Set.toFinite _)

lemma finiteLaw_integral {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (f : α → ℝ) :
    (∫ z, f z ∂finiteLaw x p) = ∑ i, p i * f (x i) := by
  rw [finiteLaw, integral_sum_dirac (fun i => ENNReal.ofReal_ne_top), tsum_fintype]
  simp [ENNReal.toReal_ofReal (hp _), smul_eq_mul]

lemma finiteLaw_probability {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (x : ι → α) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteLaw x p) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hp
  rw [← hsum]
  exact hasSum_fintype p

lemma positive_atomic_representation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Finset ℝ) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ T : Finset ℝ, T.Nonempty ∧
      (∀ a ∈ T, 0 < (μ {a}).toReal) ∧
      (∑ a ∈ T, (μ {a}).toReal) = 1 ∧
      μ = finiteLaw (fun a : T => (a : ℝ)) (fun a : T => (μ {(a : ℝ)}).toReal) := by
  classical
  let T := S.filter (fun a => 0 < μ {a})
  have he : μ = ∑ a ∈ T, μ {a} • Measure.dirac a := by
    calc
      μ = ∑ a ∈ S, μ {a} • Measure.dirac a := Measure.ae_mem_finset_iff.mp hS
      _ = ∑ a ∈ T, μ {a} • Measure.dirac a := ?_
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro a ha hn
    have hz : μ {a} = 0 := by
      have : ¬0 < μ {a} := by simpa [T, ha] using hn
      exact le_zero_iff.mp (le_of_not_gt this)
    simp [hz]
  have hne : T.Nonempty := by
    by_contra hn
    have ht : T = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [ht] at he
    have hu := congrArg (fun ν : Measure ℝ => ν univ) he
    simpa using hu
  have hpos : ∀ a ∈ T, 0 < (μ {a}).toReal := by
    intro a ha
    exact ENNReal.toReal_pos (mem_filter.mp ha).2.ne' (measure_ne_top _ _)
  have hrep : μ = finiteLaw (fun a : T => (a : ℝ)) (fun a : T => (μ {(a : ℝ)}).toReal) := by
    calc
      μ = ∑ a ∈ T, μ {a} • Measure.dirac a := he
      _ = ∑ a : T, μ {(a : ℝ)} • Measure.dirac (a : ℝ) :=
        (Finset.sum_coe_sort T (fun a : ℝ => μ {a} • Measure.dirac a)).symm
      _ = finiteLaw (fun a : T => (a : ℝ)) (fun a : T => (μ {(a : ℝ)}).toReal) := by
        rw [finiteLaw, Measure.sum_fintype]
        apply sum_congr rfl
        intro a _
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨T, hne, hpos, ?_, hrep⟩
  have hi := finiteLaw_integral (fun a : T => (a : ℝ))
    (fun a : T => (μ {(a : ℝ)}).toReal) (fun a => ENNReal.toReal_nonneg) (fun _ => (1 : ℝ))
  rw [← hrep] at hi
  rw [← Finset.sum_coe_sort T (fun a : ℝ => (μ {a}).toReal)]
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] using hi.symm

end RiskOrderFiniteLaw
open Finset
namespace RiskOrderApproximation

lemma finite_source_downshift {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (H : ℝ → ℝ) (hH : ∀ t, 0 ≤ H t)
    (i₀ : ι) (hxmax : ∀ i, x i ≤ x i₀) (ε δ : ℝ) (hε : 0 ≤ ε)
    (hδ : δ ≤ ε * p i₀) (g : ℝ → ℝ)
    (hsource : ∀ t, (∑ i, p i * max (x i - t) 0) ≤ g t)
    (htarget : ∀ t, g t ≤ H t + δ) :
    ∀ t, (∑ i, p i * max (x i - ε - t) 0) ≤ H t := by
  classical
  intro t
  by_cases ht : t ≤ x i₀ - ε
  · have hd : ∀ i, 0 ≤ p i * (max (x i - t) 0 - max (x i - ε - t) 0) := by
      intro i
      apply mul_nonneg (hp i)
      apply sub_nonneg.mpr
      exact max_le_max (by linarith) le_rfl
    have hd₀ : ε * p i₀ = p i₀ * (max (x i₀ - t) 0 - max (x i₀ - ε - t) 0) := by
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    have hsum : ε * p i₀ ≤ ∑ i, p i * (max (x i - t) 0 - max (x i - ε - t) 0) := by
      rw [hd₀]
      exact single_le_sum (fun i _ => hd i) (mem_univ i₀)
    simp_rw [mul_sub, sum_sub_distrib] at hsum
    have hS := hsource t
    have hT := htarget t
    linarith
  · have hz : (∑ i, p i * max (x i - ε - t) 0) = 0 := by
      apply sum_eq_zero
      intro i _
      rw [max_eq_right (by have := hxmax i; linarith)]
      ring
    rw [hz]
    exact hH t

end RiskOrderApproximation


set_option autoImplicit false

open MeasureTheory Filter Topology

namespace RiskOrderStopLoss

theorem cxo_partC (v : ℕ → ℝ) : ∀ M k, k ≤ M →
    v k ≤ v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 := by
  intro M
  induction M with
  | zero => intro k hk; rw [Nat.le_zero.1 hk]; simp
  | succ M ih =>
    intro k hk
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge k (M+1) with h | h
    · have h1 := ih k (by omega)
      have h2 := le_max_right (v (M+1) - v M) 0
      linarith
    · have hk' : k = M + 1 := by omega
      subst hk'
      have h1 := ih M le_rfl
      have h2 := le_max_left (v (M+1) - v M) 0
      linarith

theorem cxo_partA (v : ℕ → ℝ) : ∀ M, (∀ k < M, 0 ≤ v (k+1) - v k) →
    v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 = v M := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    rw [Finset.sum_range_succ, ← add_assoc, ih (fun k hk => h k (by omega)),
      max_eq_left (h M (by omega))]
    ring

theorem cxo_partB (v : ℕ → ℝ)
    (hP : ∀ k k', k < k' → v (k+1) - v k < 0 → v (k'+1) - v k' ≤ 0) : ∀ M, ∃ k ≤ M,
    v 0 + ∑ i ∈ Finset.range M, max (v (i+1) - v i) 0 = v k := by
  intro M
  induction M with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ M ih =>
    obtain ⟨k, hk, hS⟩ := ih
    rw [Finset.sum_range_succ, ← add_assoc]
    rcases le_or_gt (v (M+1) - v M) 0 with h | h
    · refine ⟨k, by omega, ?_⟩
      rw [hS, max_eq_right h, add_zero]
    · have hall : ∀ k < M, 0 ≤ v (k+1) - v k := by
        intro k' hk'
        by_contra hneg
        push Not at hneg
        have := hP k' M hk' hneg
        linarith
      refine ⟨M+1, le_rfl, ?_⟩
      rw [cxo_partA v M hall, max_eq_left h.le]
      ring

theorem cxo_hinge {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν)
    (γ δ : ℝ) (hγ : 0 ≤ γ) :
    ∫ ω, max (γ * X ω + δ) 0 ∂μ ≤ ∫ ω, max (γ * Y ω + δ) 0 ∂ν := by
  rcases hγ.eq_or_lt with h | h
  · subst h
    simp
  · have key : ∀ z : ℝ, max (γ * z + δ) 0 = γ * max (z - (-δ / γ)) 0 := by
      intro z
      rw [mul_max_of_nonneg _ _ h.le, mul_zero]
      congr 1
      field_simp
      ring
    simp_rw [key]
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hsl _) h.le

theorem cxo_gen {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hmean : ∫ ω, X ω ∂μ ≤ ∫ ω, Y ω ∂ν)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν)
    (ψ : ℝ → ℝ) (A B : ℝ) (hB : 0 ≤ B) (s : Finset ℕ) (γ δ : ℕ → ℝ) (hγ : ∀ k, 0 ≤ γ k)
    (hψ : ∀ z, ψ z = A + B * z + ∑ k ∈ s, max (γ k * z + δ k) 0) :
    ∫ ω, ψ (X ω) ∂μ ≤ ∫ ω, ψ (Y ω) ∂ν := by
  simp_rw [hψ]
  have iX : ∀ k, Integrable (fun ω => max (γ k * X ω + δ k) 0) μ := fun k =>
    ((hX.const_mul (γ k)).add (integrable_const (δ k))).pos_part
  have iY : ∀ k, Integrable (fun ω => max (γ k * Y ω + δ k) 0) ν := fun k =>
    ((hY.const_mul (γ k)).add (integrable_const (δ k))).pos_part
  have iAX : Integrable (fun ω => A + B * X ω) μ := (integrable_const A).add (hX.const_mul B)
  have iAY : Integrable (fun ω => A + B * Y ω) ν := (integrable_const A).add (hY.const_mul B)
  have iSX : Integrable (fun ω => ∑ k ∈ s, max (γ k * X ω + δ k) 0) μ :=
    integrable_finsetSum s fun k _ => iX k
  have iSY : Integrable (fun ω => ∑ k ∈ s, max (γ k * Y ω + δ k) 0) ν :=
    integrable_finsetSum s fun k _ => iY k
  have iBX : Integrable (fun ω => B * X ω) μ := hX.const_mul B
  have iBY : Integrable (fun ω => B * Y ω) ν := hY.const_mul B
  rw [integral_add iAX iSX, integral_add iAY iSY,
    integral_add (integrable_const A) iBX, integral_add (integrable_const A) iBY,
    integral_const_mul, integral_const_mul, integral_finsetSum s fun k _ => iX k,
    integral_finsetSum s fun k _ => iY k]
  simp only [integral_const, probReal_univ, one_smul]
  have hBm := mul_le_mul_of_nonneg_left hmean hB
  have hS : ∑ k ∈ s, ∫ ω, max (γ k * X ω + δ k) 0 ∂μ ≤ ∑ k ∈ s, ∫ ω, max (γ k * Y ω + δ k) 0 ∂ν :=
    Finset.sum_le_sum fun k _ => cxo_hinge μ ν X Y hsl (γ k) (δ k) (hγ k)
  linarith

noncomputable def cxoD (φ : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin φ (Set.Ioi x) x

noncomputable def cxoT (N k : ℕ) : ℝ := ((k : ℝ) - ((N : ℝ) + 1) ^ 2) / ((N : ℝ) + 1)

noncomputable def cxoL (φ : ℝ → ℝ) (N k : ℕ) (x : ℝ) : ℝ :=
  φ (cxoT N k) + cxoD φ (cxoT N k) * (x - cxoT N k)

noncomputable def cxoPsi (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  cxoL φ N 0 x + ∑ i ∈ Finset.range (2 * (N + 1) ^ 2), max (cxoL φ N (i+1) x - cxoL φ N i x) 0

theorem cxo_Dmono {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) : Monotone (cxoD φ) := by
  intro a b hab
  have h := hφ.monotoneOn_rightDeriv (by simp : a ∈ interior Set.univ)
    (by simp : b ∈ interior Set.univ) hab
  simpa [cxoD] using h

theorem cxo_sg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x y : ℝ) :
    φ x + cxoD φ x * (y - x) ≤ φ y := by
  rcases lt_trichotomy x y with h | h | h
  · have h1 := hφ.rightDeriv_le_slope_of_mem_interior (x := x) (y := y) (by simp)
      (Set.mem_univ _) h
    rw [slope_def_field] at h1
    have h2 : 0 < y - x := sub_pos.2 h
    rw [le_div_iff₀ h2] at h1
    simp only [cxoD]
    linarith
  · subst h; simp
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (x := y) (y := x) (Set.mem_univ _)
      (by simp) h
    have h3 := hφ.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by simp)
    rw [slope_def_field] at h1
    have h2 : 0 < x - y := sub_pos.2 h
    rw [div_le_iff₀ h2] at h1
    have h4 := mul_le_mul_of_nonneg_right h3 h2.le
    simp only [cxoD]
    nlinarith

theorem cxo_T_mono (N : ℕ) {k k' : ℕ} (h : k ≤ k') : cxoT N k ≤ cxoT N k' := by
  unfold cxoT
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  gcongr

theorem cxo_T_zero (N : ℕ) : cxoT N ((N + 1) ^ 2) = 0 := by
  unfold cxoT
  push_cast
  simp

theorem cxo_e_nonneg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {a b x : ℝ} (hab : a ≤ b)
    (hbx : b ≤ x) :
    0 ≤ (φ b + cxoD φ b * (x - b)) - (φ a + cxoD φ a * (x - a)) := by
  have h1 := cxo_sg hφ a b
  have h2 := mul_nonneg (sub_nonneg.2 (cxo_Dmono hφ hab)) (sub_nonneg.2 hbx)
  nlinarith

theorem cxo_e_nonpos {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {a b x : ℝ} (hab : a ≤ b)
    (hxa : x ≤ a) :
    (φ b + cxoD φ b * (x - b)) - (φ a + cxoD φ a * (x - a)) ≤ 0 := by
  have h1 := cxo_sg hφ b a
  have h2 := mul_nonneg (sub_nonneg.2 (cxo_Dmono hφ hab)) (sub_nonneg.2 hxa)
  nlinarith

theorem cxo_psi_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (N : ℕ) (x : ℝ) :
    cxoPsi φ N x ≤ φ x := by
  have hP : ∀ k k', k < k' → cxoL φ N (k+1) x - cxoL φ N k x < 0 →
      cxoL φ N (k'+1) x - cxoL φ N k' x ≤ 0 := by
    intro k k' hkk' hneg
    have hlt : x < cxoT N (k+1) := by
      by_contra hc
      push Not at hc
      have := cxo_e_nonneg hφ (cxo_T_mono N (Nat.le_succ k)) hc
      unfold cxoL at hneg
      linarith
    have hle : x ≤ cxoT N k' := hlt.le.trans (cxo_T_mono N (by omega))
    have := cxo_e_nonpos hφ (cxo_T_mono N (Nat.le_succ k')) hle
    unfold cxoL
    linarith
  obtain ⟨k, _, hk⟩ := cxo_partB (fun k => cxoL φ N k x) hP (2 * (N + 1) ^ 2)
  unfold cxoPsi
  rw [hk]
  exact cxo_sg hφ _ _

theorem cxo_psi_ge {φ : ℝ → ℝ} (N : ℕ) (x : ℝ) :
    φ 0 + cxoD φ 0 * x ≤ cxoPsi φ N x := by
  have h := cxo_partC (fun k => cxoL φ N k x) (2 * (N + 1) ^ 2) ((N + 1) ^ 2) (by nlinarith)
  unfold cxoPsi
  refine le_trans (le_of_eq ?_) h
  simp only [cxoL, cxo_T_zero, sub_zero]

theorem cxo_psi_cont (φ : ℝ → ℝ) (N : ℕ) : Continuous (cxoPsi φ N) := by
  unfold cxoPsi cxoL
  fun_prop

theorem cxo_psi_form (φ : ℝ → ℝ) (N : ℕ) (z : ℝ) :
    cxoPsi φ N z = (φ (cxoT N 0) - cxoD φ (cxoT N 0) * cxoT N 0) + cxoD φ (cxoT N 0) * z +
      ∑ k ∈ Finset.range (2 * (N + 1) ^ 2),
        max ((cxoD φ (cxoT N (k+1)) - cxoD φ (cxoT N k)) * z +
          (φ (cxoT N (k+1)) - cxoD φ (cxoT N (k+1)) * cxoT N (k+1) - φ (cxoT N k) +
            cxoD φ (cxoT N k) * cxoT N k)) 0 := by
  unfold cxoPsi cxoL
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ring

theorem cxo_psi_tendsto {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x : ℝ) :
    Tendsto (fun N => cxoPsi φ N x) atTop (𝓝 (φ x)) := by
  have hc : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  set j : ℕ → ℕ := fun N => ⌊x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2⌋₊ with hj
  have hev : ∀ᶠ N : ℕ in atTop, |x| < (N : ℝ) + 1 := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop |x|] with N hN
    linarith
  have hpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  -- basic floor facts
  have hfacts : ∀ᶠ N : ℕ in atTop, cxoT N (j N) ≤ x ∧ x - 1 / ((N : ℝ) + 1) < cxoT N (j N) ∧
      j N ≤ 2 * (N + 1) ^ 2 := by
    filter_upwards [hev] with N hN
    have hx1 : -((N : ℝ) + 1) < x := by linarith [neg_abs_le x]
    have hx2 : x < (N : ℝ) + 1 := by linarith [le_abs_self x]
    have ha : 0 ≤ x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2 := by nlinarith [hpos N]
    have hfl := Nat.floor_le ha
    have hfl2 := Nat.lt_floor_add_one (x * ((N : ℝ) + 1) + ((N : ℝ) + 1) ^ 2)
    refine ⟨?_, ?_, ?_⟩
    · simp only [cxoT, hj]
      rw [div_le_iff₀ (hpos N)]
      linarith
    · simp only [cxoT, hj]
      rw [lt_div_iff₀ (hpos N), sub_mul, div_mul_cancel₀ _ (hpos N).ne']
      linarith
    · have : ((j N : ℕ) : ℝ) ≤ ((2 * (N + 1) ^ 2 : ℕ) : ℝ) := by
        push_cast
        simp only [hj]
        nlinarith [hpos N]
      exact_mod_cast this
  have hτ : Tendsto (fun N => cxoT N (j N)) atTop (𝓝 x) := by
    have hlow : Tendsto (fun N : ℕ => x - 1 / ((N : ℝ) + 1)) atTop (𝓝 x) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub x
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hfacts] with N hN
      exact hN.2.1.le
    · filter_upwards [hfacts] with N hN
      exact hN.1
  have hglow : Tendsto (fun N => φ (cxoT N (j N)) + cxoD φ (x - 1) * (x - cxoT N (j N)))
      atTop (𝓝 (φ x)) := by
    have h1 := (hc.tendsto x).comp hτ
    have h2 : Tendsto (fun N => cxoD φ (x - 1) * (x - cxoT N (j N))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := x)).sub hτ
      simpa using this.const_mul (cxoD φ (x - 1))
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hglow tendsto_const_nhds ?_ ?_
  · filter_upwards [hfacts] with N hN
    obtain ⟨h1, h2, h3⟩ := hN
    have hC := cxo_partC (fun k => cxoL φ N k x) (2 * (N + 1) ^ 2) (j N) h3
    have hin : x - 1 ≤ cxoT N (j N) := by
      have : 1 / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (hpos N)]
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      linarith
    have hD := cxo_Dmono hφ hin
    have hm := mul_le_mul_of_nonneg_right hD (sub_nonneg.2 h1)
    have : cxoL φ N (j N) x ≥ φ (cxoT N (j N)) + cxoD φ (x - 1) * (x - cxoT N (j N)) := by
      unfold cxoL
      linarith
    unfold cxoPsi
    linarith
  · exact Eventually.of_forall fun N => cxo_psi_le hφ N x

theorem icx_Dnonneg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (hm : Monotone φ) (x : ℝ) :
    0 ≤ cxoD φ x := by
  have h := cxo_sg hφ x (x - 1)
  have h2 := hm (show x - 1 ≤ x by linarith)
  have e : cxoD φ x * (x - 1 - x) = -cxoD φ x := by ring
  linarith

theorem icx_mean_lim {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) :
    Tendsto (fun n : ℕ => ∫ ω, max (X ω - -(n : ℝ)) 0 ∂μ + -(n : ℝ)) atTop
      (𝓝 (∫ ω, X ω ∂μ)) := by
  have e : ∀ n : ℕ, ∫ ω, max (X ω - -(n : ℝ)) 0 ∂μ + -(n : ℝ) = ∫ ω, max (X ω) (-(n : ℝ)) ∂μ := by
    intro n
    have hi : Integrable (fun ω => max (X ω - -(n : ℝ)) 0) μ :=
      (hX.sub (integrable_const _)).pos_part
    have hf : (fun ω => max (X ω) (-(n : ℝ))) = fun ω => max (X ω - -(n : ℝ)) 0 + -(n : ℝ) := by
      funext ω
      rcases le_total (X ω) (-(n : ℝ)) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    rw [hf, integral_add hi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  simp_rw [e]
  refine tendsto_integral_of_dominated_convergence (fun ω => |X ω|)
    (fun n => ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      hX.aestronglyMeasurable)) hX.abs (fun n => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => ?_)
  · rw [Real.norm_eq_abs]
    rcases le_total (X ω) (-(n : ℝ)) with h | h
    · rw [max_eq_right h]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [max_eq_left h]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-X ω)] with n hn
    rw [max_eq_left (by linarith)]

theorem icx_mean {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν) :
    ∫ ω, X ω ∂μ ≤ ∫ ω, Y ω ∂ν :=
  le_of_tendsto_of_tendsto' (icx_mean_lim μ X hX) (icx_mean_lim ν Y hY)
    fun n => by linarith [hsl (-(n : ℝ))]

open StochasticOrders.MonotoneConvex in
theorem icx_key {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν)
    (hsl : ∀ a : ℝ, ∫ ω, max (X ω - a) 0 ∂μ ≤ ∫ ω, max (Y ω - a) 0 ∂ν) :
    IcxOrder μ ν X Y := by
  intro φ hmono hφ hiX hiY
  have hmean := icx_mean μ ν X Y hX hY hsl
  have hbound : ∀ N z, ‖cxoPsi φ N z‖ ≤ |φ z| + |φ 0 + cxoD φ 0 * z| := by
    intro N z
    have h1 := cxo_psi_le hφ N z
    have h2 := cxo_psi_ge (φ := φ) N z
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (φ 0 + cxoD φ 0 * z), abs_nonneg (φ z)]
    · linarith [le_abs_self (φ z), abs_nonneg (φ 0 + cxoD φ 0 * z)]
  have tX : Tendsto (fun N => ∫ ω, cxoPsi φ N (X ω) ∂μ) atTop (𝓝 (∫ ω, φ (X ω) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |φ (X ω)| + |φ 0 + cxoD φ 0 * X ω|)
      (fun N => (cxo_psi_cont φ N).comp_aestronglyMeasurable hX.aestronglyMeasurable)
      (hiX.abs.add ((integrable_const _).add (hX.const_mul _)).abs)
      (fun N => Eventually.of_forall fun ω => hbound N (X ω))
      (Eventually.of_forall fun ω => cxo_psi_tendsto hφ (X ω))
  have tY : Tendsto (fun N => ∫ ω, cxoPsi φ N (Y ω) ∂ν) atTop (𝓝 (∫ ω, φ (Y ω) ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |φ (Y ω)| + |φ 0 + cxoD φ 0 * Y ω|)
      (fun N => (cxo_psi_cont φ N).comp_aestronglyMeasurable hY.aestronglyMeasurable)
      (hiY.abs.add ((integrable_const _).add (hY.const_mul _)).abs)
      (fun N => Eventually.of_forall fun ω => hbound N (Y ω))
      (Eventually.of_forall fun ω => cxo_psi_tendsto hφ (Y ω))
  refine le_of_tendsto_of_tendsto' tX tY fun N => ?_
  refine cxo_gen μ ν X Y hX hY hmean hsl (cxoPsi φ N) _ _ (icx_Dnonneg hφ hmono (cxoT N 0))
    _ _ _ ?_ (cxo_psi_form φ N)
  intro k
  exact sub_nonneg.2 (cxo_Dmono hφ (cxo_T_mono N (Nat.le_succ k)))


end RiskOrderStopLoss

open MeasureTheory Set Finset StochasticOrders.MonotoneConvex
open RiskOrderFiniteLaw RiskOrderStopLoss
namespace RiskOrderApproximation

lemma finite_range_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → ℝ) (hmA : Measurable A) (hFA : (range A).Finite) :
    ∃ T : Finset ℝ, T.Nonempty ∧
      (∀ a ∈ T, 0 < ((P.map A) {a}).toReal) ∧
      (∑ a ∈ T, ((P.map A) {a}).toReal) = 1 ∧
      P.map A = finiteLaw (fun a : T => (a : ℝ)) (fun a : T => ((P.map A) {(a : ℝ)}).toReal) := by
  classical
  let : IsProbabilityMeasure (P.map A) := Measure.isProbabilityMeasure_map hmA.aemeasurable
  let S := hFA.toFinset
  have hS : ∀ᵐ a ∂P.map A, a ∈ S := by
    apply (ae_map_iff hmA.aemeasurable S.measurableSet).mpr
    filter_upwards with ω
    change A ω ∈ hFA.toFinset
    exact hFA.mem_toFinset.mpr ⟨ω, rfl⟩
  exact positive_atomic_representation (P.map A) S hS

lemma payoff_of_finite_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (A : Ω → ℝ) (hmA : Measurable A) (x : ι → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hrep : P.map A = finiteLaw x p)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ ω, φ (A ω) ∂P) = ∑ i, p i * φ (x i) := by
  calc
    (∫ ω, φ (A ω) ∂P) = ∫ z, φ z ∂P.map A :=
      (integral_map_of_stronglyMeasurable hmA hφ.stronglyMeasurable).symm
    _ = _ := by rw [hrep]; exact finiteLaw_integral x p hp φ

lemma call_order {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (h : IcxOrder P P X Y) (t : ℝ) :
    (∫ ω, max (X ω - t) 0 ∂P) ≤ ∫ ω, max (Y ω - t) 0 ∂P := by
  apply h (fun z => max (z - t) 0)
  · intro a b hab; exact max_le_max (sub_le_sub_right hab t) le_rfl
  · exact ((convexOn_id (𝕜 := ℝ) convex_univ).sub (concaveOn_const t convex_univ)).sup
      (convexOn_const 0 convex_univ)
  · exact (hX.sub (integrable_const t)).pos_part
  · exact (hY.sub (integrable_const t)).pos_part

lemma exists_ordered_finite_approximations {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) (h : IcxOrder P P X Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A B : Ω → ℝ, Measurable A ∧ Measurable B ∧ (range A).Finite ∧ (range B).Finite ∧
      Integrable A P ∧ Integrable B P ∧ IcxOrder P P A B ∧
      (∫ ω, |X ω - A ω| ∂P) < ε ∧ (∫ ω, |Y ω - B ω| ∂P) < ε := by
  classical
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hmA, hFA, hiA, hAX, herrorA⟩ := exists_finite_lower_approximation P X hX η hη
  obtain ⟨T, hT, hpos, _, hrep⟩ := finite_range_law P A hmA hFA
  obtain ⟨a₀, ha₀, hmax⟩ := T.exists_max_image id hT
  let i₀ : T := ⟨a₀, ha₀⟩
  let xp : T → ℝ := fun a => (a : ℝ)
  let pp : T → ℝ := fun a => ((P.map A) {(a : ℝ)}).toReal
  have hm : 0 < pp i₀ := hpos a₀ ha₀
  let δ := η * pp i₀
  have hδ : 0 < δ := mul_pos hη hm
  obtain ⟨b, herrorB⟩ := exists_simple_L1 P Y hY (min η δ) (lt_min hη hδ)
  let B : Ω → ℝ := b
  let A' : Ω → ℝ := fun ω => A ω - η
  have hmB : Measurable B := b.measurable
  have hiB : Integrable B P := b.integrable_of_isFiniteMeasure
  have hmA' : Measurable A' := hmA.sub measurable_const
  have hiA' : Integrable A' P := hiA.sub (integrable_const η)
  have hFA' : (range A').Finite := by
    change (range ((fun z : ℝ => z - η) ∘ A)).Finite
    rw [range_comp]; exact hFA.image _
  have hBδ : (∫ ω, |Y ω - B ω| ∂P) ≤ δ :=
    (lt_of_lt_of_le herrorB (min_le_right _ _)).le
  have hBε : (∫ ω, |Y ω - B ω| ∂P) < ε := by
    have hb := lt_of_lt_of_le herrorB (min_le_left _ _)
    dsimp [η] at hb; exact lt_trans hb (by linarith)
  have hcall : ∀ t : ℝ, (∫ ω, max (A' ω - t) 0 ∂P) ≤ ∫ ω, max (B ω - t) 0 ∂P := by
    have hS : ∀ t, (∑ i, pp i * max (xp i - t) 0) ≤ ∫ ω, max (Y ω - t) 0 ∂P := by
      intro t
      rw [← payoff_of_finite_law P A hmA xp pp (fun _ => ENNReal.toReal_nonneg) hrep
        (fun z => max (z - t) 0) (by fun_prop)]
      exact (call_order P A X hiA hX hAX t).trans (call_order P X Y hX hY h t)
    have hTgt : ∀ t, (∫ ω, max (Y ω - t) 0 ∂P) ≤ (∫ ω, max (B ω - t) 0 ∂P) + δ := by
      intro t
      exact (stopLoss_integral_L1_bound P Y B hY hiB t).trans (add_le_add le_rfl hBδ)
    have hstab := finite_source_downshift xp pp (fun _ => ENNReal.toReal_nonneg)
      (fun t => ∫ ω, max (B ω - t) 0 ∂P)
      (fun t => integral_nonneg (fun _ => le_max_right _ _)) i₀
      (fun i => hmax i i.2) η δ hη.le le_rfl
      (fun t => ∫ ω, max (Y ω - t) 0 ∂P) hS hTgt
    intro t
    have he := payoff_of_finite_law P A hmA xp pp (fun _ => ENNReal.toReal_nonneg) hrep
      (fun z => max (z - η - t) 0) (by fun_prop)
    change (∫ ω, max (A ω - η - t) 0 ∂P) ≤ ∫ ω, max (B ω - t) 0 ∂P
    rw [he]
    exact hstab t
  have hord : IcxOrder P P A' B := icx_key P P A' B hiA' hiB hcall
  have hAε : (∫ ω, |X ω - A' ω| ∂P) < ε := by
    have hb : ∀ ω, |X ω - A' ω| ≤ |X ω - A ω| + η := by
      intro ω
      have ht := abs_sub_le (X ω) (A ω) (A' ω)
      have he : |A ω - A' ω| = η := by
        dsimp [A']; rw [show A ω - (A ω - η) = η by ring, abs_of_pos hη]
      rw [he] at ht; exact ht
    have ht : (∫ ω, |X ω - A' ω| ∂P) ≤ (∫ ω, |X ω - A ω| ∂P) + η := by
      calc
        _ ≤ ∫ ω, |X ω - A ω| + η ∂P := integral_mono (hX.sub hiA').abs
          ((hX.sub hiA).abs.add (integrable_const η)) hb
        _ = _ := by
          simpa only [Pi.sub_apply, integral_const, probReal_univ, one_smul] using
            (integral_add (hX.sub hiA).abs (integrable_const η))
    dsimp [η] at herrorA ht
    linarith
  exact ⟨A', B, hmA', hmB, hFA', b.finite_range, hiA', hiB, hord, hAε, hBε⟩

end RiskOrderApproximation


namespace RiskOrderFinite.Duality

/-!
# Finitely generated convex cones and primitive cones

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007,
§6.4, p. 89 (convex cone generated by `a₁, …, aₙ`) and §6.5, p. 96 (primitive cone).
Points of `ℝ^m` are elements of `EuclideanSpace ℝ (Fin m)`, so distances are Euclidean.
-/

variable {m n : ℕ}

/-- The **convex cone generated by** `a₁, …, aₙ ∈ ℝ^m` (p. 89): the set of all linear
combinations `t₁a₁ + ⋯ + tₙaₙ` with `t₁, …, tₙ ≥ 0`.  For `n = 0` it is `{0}`. -/
def coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ t : Fin n → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • a i}

/-- A **primitive cone** in `ℝ^m` (p. 96): a convex cone generated by some `k ≤ m` linearly
independent vectors (`k = 0` gives `{0}`). -/
def IsPrimitiveCone (P : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ k : ℕ, k ≤ m ∧ ∃ v : Fin k → EuclideanSpace ℝ (Fin m),
    LinearIndependent ℝ v ∧ P = coneGen v

end RiskOrderFinite.Duality

open Finset

namespace RiskOrderConicCara

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- Conic Carathéodory: a nonnegative combination of `a` is a nonnegative combination of a
linearly independent subfamily. -/
theorem exists_linIndep_repr (a : Fin n → E) :
    ∀ (k : ℕ) (t : Fin n → ℝ), (∀ i, 0 ≤ t i) → (univ.filter fun i => t i ≠ 0).card ≤ k →
      ∃ (S : Finset (Fin n)) (s : Fin n → ℝ), (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧
        LinearIndependent ℝ (fun i : S => a i) ∧ ∑ i, s i • a i = ∑ i, t i • a i := by
  intro k
  induction k with
  | zero =>
    intro t ht hk
    refine ⟨∅, t, ht, fun i _ => ?_, linearIndependent_empty_type, rfl⟩
    by_contra h
    have : i ∈ univ.filter fun i => t i ≠ 0 := by simp [h]
    simp_all
  | succ k ih =>
    intro t ht hk
    set T := univ.filter fun i => t i ≠ 0 with hT
    by_cases hli : LinearIndependent ℝ (fun i : T => a i)
    · refine ⟨T, t, ht, fun i hi => ?_, hli, rfl⟩
      by_contra h; exact hi (by simp [T, h])
    · -- a nontrivial dependency supported on T
      obtain ⟨g, hg, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hli
      -- extend to Fin n, possibly negating so that some coefficient is positive
      have hpos : ∃ μ : Fin n → ℝ, (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • a i = 0 ∧ ∃ i, 0 < μ i := by
        set μ0 : Fin n → ℝ := fun i => if h : i ∈ T then g ⟨i, h⟩ else 0
        have hsum : ∑ i, μ0 i • a i = 0 := by
          rw [← hg]
          rw [← Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by simp [μ0, hi])]
          rw [← Finset.sum_coe_sort T]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [μ0, i.2]
        have hsupp : ∀ i, i ∉ T → μ0 i = 0 := fun i hi => by simp [μ0, hi]
        have hj' : μ0 j ≠ 0 := by simp [μ0, j.2, hj]
        rcases lt_or_gt_of_ne hj' with hneg | hpos
        · refine ⟨-μ0, fun i hi => by simp [hsupp i hi], by simp [neg_smul, hsum], j, by simpa using hneg⟩
        · exact ⟨μ0, hsupp, hsum, j, hpos⟩
      obtain ⟨μ, hμT, hμsum, i₀, hi₀⟩ := hpos
      -- choose the ratio-minimizing positive coordinate
      set P := univ.filter fun i => 0 < μ i
      have hPne : P.Nonempty := ⟨i₀, by simp [P, hi₀]⟩
      obtain ⟨j₀, hj₀P, hj₀min⟩ := P.exists_min_image (fun i => t i / μ i) hPne
      have hμj₀ : 0 < μ j₀ := (Finset.mem_filter.mp hj₀P).2
      set θ := t j₀ / μ j₀
      have hθ : 0 ≤ θ := div_nonneg (ht j₀) hμj₀.le
      set t' : Fin n → ℝ := fun i => t i - θ * μ i
      have ht' : ∀ i, 0 ≤ t' i := by
        intro i
        by_cases hi : 0 < μ i
        · have := hj₀min i (by simp [P, hi])
          rw [div_le_div_iff₀ hμj₀ hi] at this
          simp only [t', sub_nonneg, θ]
          rw [div_mul_eq_mul_div, div_le_iff₀ hμj₀]
          linarith
        · push_neg at hi
          simp only [t']
          nlinarith [ht i]
      have ht'j₀ : t' j₀ = 0 := by simp [t', θ, div_mul_cancel₀ _ hμj₀.ne']
      have hsubset : (univ.filter fun i => t' i ≠ 0) ⊆ T := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hti
        apply hi
        have hti' : t i = 0 := by simpa [T] using hti
        have hμi : μ i = 0 := hμT i hti
        simp [t', hti', hμi]
      have hj₀T : j₀ ∈ T := by
        by_contra h
        have hμj₀0 : μ j₀ = 0 := hμT j₀ h
        linarith
      have hsub : (univ.filter fun i => t' i ≠ 0) ⊂ T :=
        (Finset.ssubset_iff_of_subset hsubset).mpr ⟨j₀, hj₀T, by simp [ht'j₀]⟩
      have hcard : (univ.filter fun i => t' i ≠ 0).card ≤ k := by
        have := Finset.card_lt_card hsub; omega
      obtain ⟨S, s, hs, hsS, hSli, hsum⟩ := ih t' ht' hcard
      refine ⟨S, s, hs, hsS, hSli, ?_⟩
      rw [hsum]
      simp only [t', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμsum,
        smul_zero, sub_zero]

end RiskOrderConicCara

namespace RiskOrderConeAux

open RiskOrderFinite.Duality

variable {m n : ℕ}

/-- The cone generated by the subfamily indexed by `S`, as supported combinations. -/
def subCone (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ s : Fin n → ℝ, (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧ x = ∑ i, s i • a i}

lemma subCone_subset (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    subCone a S ⊆ coneGen a := by
  rintro x ⟨s, hs, -, rfl⟩; exact ⟨s, hs, rfl⟩

/-- A linearly independent subfamily generates a primitive cone. -/
lemma subCone_primitive (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n))
    (hS : LinearIndependent ℝ (fun i : S => a i)) : IsPrimitiveCone (subCone a S) := by
  classical
  set σ : Fin S.card ≃o S := S.orderIsoOfFin rfl
  set v : Fin S.card → EuclideanSpace ℝ (Fin m) := fun r => a (σ r)
  have hv : LinearIndependent ℝ v := hS.comp σ σ.injective
  refine ⟨S.card, ?_, v, hv, ?_⟩
  · have := hv.fintype_card_le_finrank
    simpa using this
  · ext x
    constructor
    · rintro ⟨s, hs, hsS, rfl⟩
      refine ⟨fun r => s (σ r), fun r => hs _, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hsS i hi])]
      rw [← Finset.sum_coe_sort S]
      exact (Equiv.sum_comp σ.toEquiv (fun i : S => s i • a i)).symm
    · rintro ⟨t, ht, rfl⟩
      set s : Fin n → ℝ := fun i => if h : i ∈ S then t (σ.symm ⟨i, h⟩) else 0
      refine ⟨s, fun i => ?_, fun i hi => by simp [s, hi], ?_⟩
      · simp only [s]; split_ifs <;> simp [ht]
      · rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [s, hi])]
        rw [← Finset.sum_coe_sort S]
        rw [← Equiv.sum_comp σ.toEquiv (fun i : S => s i • a i)]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [s, v]

/-- Every finitely generated cone is the union of the primitive cones of its linearly independent
subfamilies. -/
lemma coneGen_eq_iUnion (a : Fin n → EuclideanSpace ℝ (Fin m)) :
    coneGen a = ⋃ (S : Finset (Fin n)) (_ : LinearIndependent ℝ (fun i : S => a i)),
      subCone a S := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨S, s, hs, hsS, hli, hsum⟩ :=
      RiskOrderConicCara.exists_linIndep_repr a _ t ht le_rfl
    exact ⟨S, hli, s, hs, hsS, hsum.symm⟩
  · rintro ⟨S, -, hx⟩; exact subCone_subset a S hx

lemma isClosed_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : IsClosed (coneGen a) := by
  classical
  rw [coneGen_eq_iUnion]
  refine isClosed_iUnion_of_finite fun S => isClosed_iUnion_of_finite fun hli => ?_
  obtain ⟨k, -, v, hv, hP⟩ := subCone_primitive a S hli
  rw [hP]
  -- a primitive cone is closed (image of the orthant under a closed embedding)
  set L : (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Fintype.linearCombination ℝ v
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  have himage : coneGen v = L '' {t | ∀ i, 0 ≤ t i} := by
    ext x
    simp only [coneGen, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
  rw [himage]
  apply (LinearMap.isClosedEmbedding_of_injective hL).isClosedMap
  have : {t : Fin k → ℝ | ∀ i, 0 ≤ t i} = ⋂ i, {t | 0 ≤ t i} := by ext; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

lemma zero_mem_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : (0 : _) ∈ coneGen a :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma convex_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : Convex ℝ (coneGen a) := by
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ α β hα hβ -
  refine ⟨fun i => α * s i + β * t i, fun i => by have := hs i; have := ht i; positivity, ?_⟩
  simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]

end RiskOrderConeAux

open RiskOrderFinite.Duality RiskOrderConeAux in
theorem riskOrderFarkasGeometric {m n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    Xor (b ∈ coneGen a)
      (∃ y : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ inner ℝ y (a i)) ∧ inner ℝ y b < 0) := by
  by_cases hb : b ∈ coneGen a
  · -- no separating vector exists
    refine Or.inl ⟨hb, ?_⟩
    rintro ⟨y, hy, hyb⟩
    obtain ⟨t, ht, rfl⟩ := hb
    have : 0 ≤ inner ℝ y (∑ i, t i • a i) := by
      rw [inner_sum]
      exact Finset.sum_nonneg fun i _ => by rw [inner_smul_right]; exact mul_nonneg (ht i) (hy i)
    linarith
  · refine Or.inr ⟨?_, hb⟩
    -- nearest point z of the closed convex cone; y = z - b separates
    obtain ⟨z, hz, hdist⟩ := (isClosed_coneGen a).exists_infDist_eq_dist ⟨0, zero_mem_coneGen a⟩ b
    have hmin : ‖b - z‖ = ⨅ w : coneGen a, ‖b - w‖ := by
      rw [← dist_eq_norm, ← hdist, Metric.infDist_eq_iInf]
      simp [dist_eq_norm]
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_coneGen a) hz).mp hmin
    -- variational inequality: ⟪b - z, w - z⟫ ≤ 0 for all w in the cone
    have hai : ∀ i, inner ℝ (b - z) (a i) ≤ 0 := by
      intro i
      obtain ⟨s, hs, rfl⟩ := hz
      have hw : (∑ j, s j • a j) + a i ∈ coneGen a :=
        ⟨fun j => s j + if j = i then 1 else 0, fun j => by
          show 0 ≤ s j + (if j = i then (1 : ℝ) else 0)
          have := hs j; split_ifs <;> linarith,
          by simp [add_smul, Finset.sum_add_distrib, Finset.sum_ite_eq']⟩
      simpa using hvar _ hw
    have hz0 : inner ℝ (b - z) z = 0 := by
      have h0 := hvar 0 (zero_mem_coneGen a)
      have h2 : (2 : ℝ) • z ∈ coneGen a := by
        obtain ⟨s, hs, hzs⟩ := hz
        exact ⟨fun j => 2 * s j, fun j => by have := hs j; positivity, by
          simp [hzs, Finset.smul_sum, mul_smul]⟩
      have h2' := hvar _ h2
      simp only [zero_sub, inner_neg_right] at h0
      rw [show (2 : ℝ) • z - z = z by module] at h2'
      linarith
    have hne : b - z ≠ 0 := by
      intro h; apply hb; rw [sub_eq_zero.mp h]; exact hz
    refine ⟨z - b, fun i => ?_, ?_⟩
    · have := hai i
      rw [show z - b = -(b - z) by abel, inner_neg_left]; linarith
    · have hpos : 0 < inner ℝ (b - z) (b - z) := real_inner_self_pos.mpr hne
      have hsplit : inner ℝ (b - z) b = inner ℝ (b - z) (b - z) + inner ℝ (b - z) z := by
        rw [← inner_add_right]; congr 1; abel
      rw [show z - b = -(b - z) by abel, inner_neg_left, hsplit, hz0]
      linarith

namespace RiskOrderFarkas

open Matrix RiskOrderFinite.Duality RiskOrderConeAux

/-- Farkas' lemma, equational form: `Ax = b, x ≥ 0` is solvable iff every `y` with `Aᵀy ≥ 0`
has `yᵀb ≥ 0`. -/
theorem farkas_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro h
    set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    rcases riskOrderFarkasGeometric a (WithLp.toLp 2 b) with ⟨hb, -⟩ | ⟨⟨y, hy, hyb⟩, -⟩
    · obtain ⟨t, ht, hbt⟩ := hb
      refine ⟨t, fun i => ht i, ?_⟩
      have hb' : b = ∑ j, t j • (fun i => A i j) := by
        have := congrArg WithLp.ofLp hbt
        simpa [a, WithLp.ofLp_sum, WithLp.ofLp_smul] using this
      rw [hb']
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · exfalso
      set y' : Fin m → ℝ := WithLp.ofLp y
      have hy' : 0 ≤ Aᵀ *ᵥ y' := by
        intro j
        have := hy j
        simp only [a] at this
        have hy_eq : y = WithLp.toLp 2 y' := rfl
        rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at this
        simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
      have := h y' hy'
      have hy_eq : y = WithLp.toLp 2 y' := rfl
      rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at hyb
      simp only [star_trivial] at hyb
      rw [dotProduct_comm] at hyb
      linarith


/-- `farkas_eq` for an arbitrary finite column index. -/
theorem farkas_eq_fintype {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ι
  set A' : Matrix (Fin m) (Fin (Fintype.card ι)) ℝ := A.submatrix id e.symm
  have hmul : ∀ x : ι → ℝ, A' *ᵥ (x ∘ e.symm) = A *ᵥ x := by
    intro x; funext i
    simp only [A', mulVec, dotProduct, submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp e.symm (fun j => A i j * x j)
  have htr : ∀ y : Fin m → ℝ, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := by
    intro y; funext j; simp [A', mulVec, dotProduct, transpose_apply]
  have hnonneg : ∀ y : Fin m → ℝ, (0 ≤ A'ᵀ *ᵥ y ↔ 0 ≤ Aᵀ *ᵥ y) := by
    intro y; rw [htr]
    constructor
    · intro h j; simpa using h (e j)
    · intro h j; exact h _
  rw [show (∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      (∀ y : Fin m → ℝ, 0 ≤ A'ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) from
      forall_congr' fun y => by rw [hnonneg]]
  rw [← farkas_eq A' b]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x ∘ e.symm, fun j => hx _, hmul x⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x' ∘ e, fun j => hx' _, ?_⟩
    rw [← hmul]; congr 1; funext j; simp


/-- Farkas, equational form, arbitrary finite row and column index types. -/
theorem farkas_eq_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : ρ → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ρ
  set A' : Matrix (Fin (Fintype.card ρ)) ι ℝ := A.submatrix e.symm id
  have h := farkas_eq_fintype A' (b ∘ e.symm)
  have hrow : ∀ x : ι → ℝ, A' *ᵥ x = (A *ᵥ x) ∘ e.symm := by
    intro x; funext r; simp [A', mulVec, dotProduct]
  have hcol : ∀ y' : Fin (Fintype.card ρ) → ℝ, A'ᵀ *ᵥ y' = Aᵀ *ᵥ (y' ∘ e) := by
    intro y'; funext j
    simp only [A', mulVec, dotProduct, transpose_apply, submatrix_apply, id, Function.comp]
    rw [← Equiv.sum_comp e (fun x => A (e.symm x) j * y' x)]
    simp
  have hdot : ∀ y' : Fin (Fintype.card ρ) → ℝ, y' ⬝ᵥ (b ∘ e.symm) = (y' ∘ e) ⬝ᵥ b := by
    intro y'
    simp only [dotProduct, Function.comp]
    rw [← Equiv.sum_comp e (fun x => y' x * b (e.symm x))]
    simp
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro hy
    obtain ⟨x, hx, hAx⟩ := h.mpr fun y' hy' => by
      rw [hcol] at hy'; rw [hdot]; exact hy _ hy'
    refine ⟨x, hx, ?_⟩
    funext r
    have := congrFun hAx (e r)
    rw [hrow] at this; simpa using this

end RiskOrderFarkas


open Matrix Finset
namespace RiskOrderFinite

noncomputable def couplingMatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (y : κ → ℝ) : Matrix (ι ⊕ (κ ⊕ ι)) ((ι × κ) ⊕ ι) ℝ := by
  classical
  exact fun r c => match r, c with
    | Sum.inl k, Sum.inl (i, _) => if k = i then 1 else 0
    | Sum.inr (Sum.inl k), Sum.inl (_, j) => if k = j then 1 else 0
    | Sum.inr (Sum.inr k), Sum.inl (i, j) => if k = i then y j else 0
    | Sum.inr (Sum.inr k), Sum.inr i => if k = i then -1 else 0
    | _, _ => 0

def couplingRhs {ι κ : Type*} (x : ι → ℝ) (p : ι → ℝ) (q : κ → ℝ) :
    (ι ⊕ (κ ⊕ ι)) → ℝ
  | Sum.inl i => p i
  | Sum.inr (Sum.inl j) => q j
  | Sum.inr (Sum.inr i) => x i * p i

lemma affine_max_properties {ι : Type*} [Fintype ι] [Nonempty ι]
    (a g : ι → ℝ) (hg : ∀ i, g i ≤ 0) :
    let φ : ℝ → ℝ := fun t => univ.sup' univ_nonempty (fun i => -a i - g i * t)
    Monotone φ ∧ ConvexOn ℝ Set.univ φ := by
  classical
  dsimp only
  constructor
  · intro r s hrs
    apply sup'_le
    intro i _
    apply le_trans ?_ (le_sup' (fun i => -a i - g i * s) (mem_univ i))
    nlinarith [hg i]
  · refine ⟨convex_univ, ?_⟩
    intro r _ s _ u v hu hv huv
    apply sup'_le
    intro i _
    have hr := le_sup' (fun i => -a i - g i * r) (mem_univ i)
    have hs := le_sup' (fun i => -a i - g i * s) (mem_univ i)
    simp only [smul_eq_mul]
    calc
      -a i - g i * (u * r + v * s) = u * (-a i - g i * r) + v * (-a i - g i * s) := by
        linear_combination a i * huv
      _ ≤ u * univ.sup' univ_nonempty (fun i => -a i - g i * r) +
          v * univ.sup' univ_nonempty (fun i => -a i - g i * s) :=
        add_le_add (mul_le_mul_of_nonneg_left hr hu) (mul_le_mul_of_nonneg_left hs hv)

theorem finite_submartingale_matrix {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (x : ι → ℝ) (y : κ → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ →
      (∑ i, p i * φ (x i)) ≤ ∑ j, q j * φ (y j)) :
    ∃ c : ι → κ → ℝ, (∀ i j, 0 ≤ c i j) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      ∀ i, x i * p i ≤ ∑ j, c i j * y j := by
  classical
  let A := couplingMatrix (ι := ι) y
  let b := couplingRhs x p q
  have hfeas : ∃ z : ((ι × κ) ⊕ ι) → ℝ, 0 ≤ z ∧ A *ᵥ z = b := by
    apply (RiskOrderFarkas.farkas_eq_gen A b).mpr
    intro w hw
    let a : ι → ℝ := fun i => w (Sum.inl i)
    let d : κ → ℝ := fun j => w (Sum.inr (Sum.inl j))
    let g : ι → ℝ := fun i => w (Sum.inr (Sum.inr i))
    have hg : ∀ i, g i ≤ 0 := by
      intro i
      have hh := hw (Sum.inr i)
      simpa [A, couplingMatrix, mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, g] using hh
    have hadg : ∀ i j, 0 ≤ a i + d j + g i * y j := by
      intro i j
      have hh := hw (Sum.inl (i, j))
      simpa [A, couplingMatrix, mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type, a, d, g, add_assoc, mul_comm] using hh
    let φ : ℝ → ℝ := fun t => univ.sup' univ_nonempty (fun i => -a i - g i * t)
    have hprops := affine_max_properties a g hg
    have hord := horder φ hprops.1 hprops.2
    have hd : ∀ j, φ (y j) ≤ d j := by
      intro j
      apply sup'_le
      intro i _
      have := hadg i j; linarith
    have ha : ∀ i, -φ (x i) ≤ a i + g i * x i := by
      intro i
      have := le_sup' (fun k => -a k - g k * x i) (mem_univ i)
      change -φ (x i) ≤ a i + g i * x i
      dsimp [φ] at *; linarith
    have hsA : -(∑ i, p i * φ (x i)) ≤ ∑ i, p i * (a i + g i * x i) := by
      calc
        -(∑ i, p i * φ (x i)) = ∑ i, p i * (-φ (x i)) := by simp
        _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (hp i)
    have hsD : (∑ j, q j * φ (y j)) ≤ ∑ j, q j * d j :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hd j) (hq j)
    have he : w ⬝ᵥ b = (∑ i, p i * (a i + g i * x i)) + ∑ j, q j * d j := by
      simp only [dotProduct, b, couplingRhs, Fintype.sum_sum_type, mul_add, sum_add_distrib]
      simp only [a, d, g]
      have he₁ : (∑ i, w (Sum.inl i) * p i) = ∑ i, p i * w (Sum.inl i) := by
        apply sum_congr rfl; intro i _; ring
      have he₂ : (∑ i, w (Sum.inr (Sum.inr i)) * (x i * p i)) =
          ∑ i, p i * (w (Sum.inr (Sum.inr i)) * x i) := by
        apply sum_congr rfl; intro i _; ring
      have he₃ : (∑ j, w (Sum.inr (Sum.inl j)) * q j) = ∑ j, q j * w (Sum.inr (Sum.inl j)) := by
        apply sum_congr rfl; intro j _; ring
      rw [he₁, he₂, he₃]; ring
    rw [he]
    linarith
  obtain ⟨z, hz, hAz⟩ := hfeas
  refine ⟨fun i j => z (Sum.inl (i, j)), fun i j => hz _, ?_, ?_, ?_⟩
  · intro i
    have hh := congrFun hAz (Sum.inl i)
    simp [A, b, couplingMatrix, couplingRhs, mulVec, dotProduct,
      Fintype.sum_sum_type, Fintype.sum_prod_type] at hh
    rw [sum_comm] at hh
    simpa using hh
  · intro j
    have hh := congrFun hAz (Sum.inr (Sum.inl j))
    simpa [A, b, couplingMatrix, couplingRhs, mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, sum_ite_irrel, sub_eq_add_neg] using hh
  · intro i
    have hh := congrFun hAz (Sum.inr (Sum.inr i))
    have hi := hz (Sum.inr i)
    change 0 ≤ z (Sum.inr i) at hi
    have he : (∑ j, y j * z (Sum.inl (i, j))) - z (Sum.inr i) = x i * p i := by
      simpa [A, b, couplingMatrix, couplingRhs, mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, sum_ite_irrel, sub_eq_add_neg] using hh
    rw [show (∑ j, z (Sum.inl (i, j)) * y j) = ∑ j, y j * z (Sum.inl (i, j)) by
      apply sum_congr rfl; intro j _; ring]
    linarith

end RiskOrderFinite

namespace RiskOrderFiniteLaw
lemma matrix_pair_law {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (p : ι → ℝ) (q : κ → ℝ) (c : ι → κ → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hrow : ∀ i, ∑ j, c i j = p i)
    (hcol : ∀ j, ∑ i, c i j = q j)
    (hmean : ∀ i, x i * p i ≤ ∑ j, c i j * y j) (hp : ∑ i, p i = 1) :
    ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = finiteLaw x p ∧ μ.map Prod.snd = finiteLaw y q ∧
      ∀ s : Set ℝ, MeasurableSet s →
        (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ := by
  classical
  let z : ι × κ → ℝ × ℝ := fun ij => (x ij.1, y ij.2)
  let w : ι × κ → ℝ := fun ij => c ij.1 ij.2
  let μ := finiteLaw z w
  have hw : ∀ ij, 0 ≤ w ij := fun ij => hc _ _
  have hsum : ∑ ij, w ij = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [w, hrow] using hp
  refine ⟨μ, finiteLaw_probability z w hw hsum, ?_, ?_, ?_⟩
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply measurable_fst hs, finiteLaw_apply, finiteLaw_apply, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    by_cases hi : x i ∈ s
    · simp only [z, w, Set.mem_preimage, hi, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hc i j), hrow]
    · simp [z, w, hi]
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply measurable_snd hs, finiteLaw_apply, finiteLaw_apply, Fintype.sum_prod_type, sum_comm]
    apply sum_congr rfl
    intro j _
    by_cases hj : y j ∈ s
    · simp only [z, w, Set.mem_preimage, hj, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hc i j), hcol]
    · simp [z, w, hj]
  · intro s hs
    rw [← integral_indicator (measurable_fst hs), ← integral_indicator (measurable_fst hs)]
    rw [finiteLaw_integral z w hw, finiteLaw_integral z w hw,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply sum_le_sum
    intro i _
    by_cases hi : x i ∈ s
    · simp only [z, w, indicator_apply, Set.mem_preimage, hi, if_true]
      have he : (∑ j, c i j * x i) = x i * p i := by
        rw [← sum_mul, hrow]; ring
      rw [he]
      exact hmean i
    · simp [z, w, indicator_apply, hi]

end RiskOrderFiniteLaw

open RiskOrderFinite RiskOrderFiniteLaw
namespace RiskOrderApproximation
lemma finite_range_coupling_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hFA : (Set.range A).Finite) (hFB : (Set.range B).Finite) (h : IcxOrder P P A B) :
    ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = P.map A ∧ μ.map Prod.snd = P.map B ∧
      ∀ s : Set ℝ, MeasurableSet s →
        (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ := by
  classical
  obtain ⟨TA, hTA, _, hmassA, hrepA⟩ := finite_range_law P A hmA hFA
  obtain ⟨TB, _, _, _, hrepB⟩ := finite_range_law P B hmB hFB
  let x : TA → ℝ := fun a => (a : ℝ)
  let y : TB → ℝ := fun b => (b : ℝ)
  let p : TA → ℝ := fun a => ((P.map A) {(a : ℝ)}).toReal
  let q : TB → ℝ := fun b => ((P.map B) {(b : ℝ)}).toReal
  letI : Nonempty TA := ⟨⟨hTA.choose, hTA.choose_spec⟩⟩
  have hp : ∀ a, 0 ≤ p a := fun _ => ENNReal.toReal_nonneg
  have hq : ∀ b, 0 ≤ q b := fun _ => ENNReal.toReal_nonneg
  have hmass : ∑ a, p a = 1 := by
    dsimp only [p]
    rw [Finset.sum_coe_sort TA (fun a : ℝ => ((P.map A) {a}).toReal)]
    exact hmassA
  have hord : ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ →
      (∑ a, p a * φ (x a)) ≤ ∑ b, q b * φ (y b) := by
    intro φ hφ hc
    have hiA : Integrable (φ ∘ A) P := by
      apply (integrable_map_measure hφ.measurable.aestronglyMeasurable hmA.aemeasurable).mp
      rw [hrepA]; exact finiteLaw_integrable x p φ
    have hiB : Integrable (φ ∘ B) P := by
      apply (integrable_map_measure hφ.measurable.aestronglyMeasurable hmB.aemeasurable).mp
      rw [hrepB]; exact finiteLaw_integrable y q φ
    rw [← payoff_of_finite_law P A hmA x p hp hrepA φ hφ.measurable,
      ← payoff_of_finite_law P B hmB y q hq hrepB φ hφ.measurable]
    exact h φ hφ hc hiA hiB
  obtain ⟨c, hc, hrow, hcol, hmean⟩ := finite_submartingale_matrix x y p q hp hq hord
  obtain ⟨μ, hμ, hfst, hsnd, htests⟩ := matrix_pair_law x y p q c hc hrow hcol hmean hmass
  exact ⟨μ, hμ, hfst.trans hrepA.symm, hsnd.trans hrepB.symm, htests⟩

lemma exists_finite_coupling_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) (h : IcxOrder P P X Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A B : Ω → ℝ, ∃ μ : Measure (ℝ × ℝ),
      Measurable A ∧ Measurable B ∧ (Set.range A).Finite ∧ (Set.range B).Finite ∧
      Integrable A P ∧ Integrable B P ∧
      (∫ ω, |X ω - A ω| ∂P) < ε ∧ (∫ ω, |Y ω - B ω| ∂P) < ε ∧
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P.map A ∧ μ.map Prod.snd = P.map B ∧
      ∀ s : Set ℝ, MeasurableSet s →
        (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ := by
  obtain ⟨A, B, hmA, hmB, hFA, hFB, hiA, hiB, hord, heA, heB⟩ :=
    exists_ordered_finite_approximations P X Y hX hY h ε hε
  obtain ⟨μ, hμ, hfst, hsnd, htests⟩ := finite_range_coupling_law P A B hmA hmB hFA hFB hord
  exact ⟨A, B, μ, hmA, hmB, hFA, hFB, hiA, hiB, heA, heB, hμ, hfst, hsnd, htests⟩

end RiskOrderApproximation

open MeasureTheory ProbabilityTheory
namespace RiskOrderCompactness

lemma integral_abs_le_of_L1_close {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X A : Ω → ℝ) (hX : Integrable X P) (hA : Integrable A P)
    (ε : ℝ) (he : (∫ ω, |X ω - A ω| ∂P) ≤ ε) :
    (∫ ω, |A ω| ∂P) ≤ (∫ ω, |X ω| ∂P) + ε := by
  have hb : ∀ ω, |A ω| ≤ |X ω| + |X ω - A ω| := by
    intro ω
    simpa only [sub_zero, abs_sub_comm, add_comm] using abs_sub_le (A ω) (X ω) 0
  calc
    (∫ ω, |A ω| ∂P) ≤ ∫ ω, |X ω| + |X ω - A ω| ∂P :=
      integral_mono hA.abs (hX.abs.add (hX.sub hA).abs) hb
    _ = (∫ ω, |X ω| ∂P) + ∫ ω, |X ω - A ω| ∂P := integral_add hX.abs (hX.sub hA).abs
    _ ≤ _ := add_le_add le_rfl he

lemma pair_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y A B : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) (hA : Integrable A P) (hB : Integrable B P)
    (μ : Measure (ℝ × ℝ)) (hf : IdentDistrib Prod.fst A μ P) (hs : IdentDistrib Prod.snd B μ P)
    (ε : ℝ) (heA : (∫ ω, |X ω - A ω| ∂P) ≤ ε) (heB : (∫ ω, |Y ω - B ω| ∂P) ≤ ε) :
    Integrable (fun z : ℝ × ℝ => ‖z‖) μ ∧
      (∫ z, ‖z‖ ∂μ) ≤ (∫ ω, |X ω| ∂P) + (∫ ω, |Y ω| ∂P) + 2 * ε := by
  have hif : Integrable Prod.fst μ := hf.integrable_iff.mpr hA
  have his : Integrable Prod.snd μ := hs.integrable_iff.mpr hB
  have hn : ∀ z : ℝ × ℝ, ‖z‖ ≤ |z.1| + |z.2| := by
    intro z
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have hi : Integrable (fun z : ℝ × ℝ => ‖z‖) μ :=
    (hif.abs.add his.abs).mono' continuous_norm.aestronglyMeasurable
      (ae_of_all _ (fun z => by simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hn z))
  refine ⟨hi, ?_⟩
  have hfabs := (hf.comp measurable_abs).integral_eq
  have hsabs := (hs.comp measurable_abs).integral_eq
  have hboundA := integral_abs_le_of_L1_close P X A hX hA ε heA
  have hboundB := integral_abs_le_of_L1_close P Y B hY hB ε heB
  calc
    (∫ z, ‖z‖ ∂μ) ≤ ∫ z, |z.1| + |z.2| ∂μ := integral_mono hi (hif.abs.add his.abs) hn
    _ = (∫ z, |z.1| ∂μ) + ∫ z, |z.2| ∂μ := integral_add hif.abs his.abs
    _ = (∫ ω, |A ω| ∂P) + ∫ ω, |B ω| ∂P := by
      exact congrArg₂ (· + ·) hfabs hsabs
    _ ≤ _ := by linarith

end RiskOrderCompactness

open MeasureTheory Set Filter
open scoped Topology

namespace RiskOrderCompactness
lemma tight_of_bounded_first_moment (μ : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n, Integrable (fun z : ℝ × ℝ => ‖z‖) (μ n : Measure (ℝ × ℝ)))
    (hbound : ∀ n, (∫ z, ‖z‖ ∂(μ n : Measure (ℝ × ℝ))) ≤ C) :
    IsTightMeasureSet (range (fun n => (μ n : Measure (ℝ × ℝ)))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases he : ε = ⊤
  · subst ε; exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hepos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' he
  let r := (C + 1) / ε.toReal
  have hr : 0 < r := div_pos (by linarith) hepos
  have hre : r * ε.toReal = C + 1 := div_mul_cancel₀ _ hepos.ne'
  refine ⟨Metric.closedBall (0 : ℝ × ℝ) r, isCompact_closedBall _ _, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hsub : (Metric.closedBall (0 : ℝ × ℝ) r)ᶜ ⊆ {z : ℝ × ℝ | r ≤ ‖z‖} := by
    intro z hz
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hmono := ENNReal.toReal_mono (measure_ne_top (μ n : Measure (ℝ × ℝ)) _)
    (measure_mono hsub)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (μ n : Measure (ℝ × ℝ))) (ae_of_all _ (fun z => norm_nonneg z)) (hint n) r
  have hb : r * ((μ n : Measure (ℝ × ℝ)) (Metric.closedBall (0 : ℝ × ℝ) r)ᶜ).toReal ≤ C :=
    (mul_le_mul_of_nonneg_left hmono hr.le).trans (hmark.trans (hbound n))
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) he).mp
  nlinarith

lemma subsequence_of_bounded_first_moment (μ : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n, Integrable (fun z : ℝ × ℝ => ‖z‖) (μ n : Measure (ℝ × ℝ)))
    (hbound : ∀ n, (∫ z, ‖z‖ ∂(μ n : Measure (ℝ × ℝ))) ≤ C) :
    ∃ ν : ProbabilityMeasure (ℝ × ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have ht := tight_of_bounded_first_moment μ C hC hint hbound
  have hs : IsTightMeasureSet {((ν : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) | ν ∈ range μ} := by
    convert ht using 1
    ext ν
    simp only [mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨m, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ν, _, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hs).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨ν, φ, hφ, hlim⟩

end RiskOrderCompactness


open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace RiskOrderCompactness

lemma tendsto_eLpNorm_one_of_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (A n - X) 1 P) atTop (𝓝 0) := by
  have hn : ∀ n, eLpNorm (A n - X) 1 P = ENNReal.ofReal (∫ ω, |X ω - A n ω| ∂P) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm ((hA n).sub hX)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by simp [Real.norm_eq_abs, abs_sub_comm])
  simp_rw [hn]
  simpa using ENNReal.tendsto_ofReal he

lemma laws_tendsto_of_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0)) :
    TendstoInDistribution A atTop X (fun _ => P) P := by
  have hn := tendsto_eLpNorm_one_of_L1 P X A hX hA he
  have hi := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 1)
    (by norm_num) (by norm_num) (fun n => (hA n).aestronglyMeasurable)
    hX.aestronglyMeasurable hn
  exact hi.tendstoInDistribution (fun n => (hA n).aemeasurable)

lemma uniform_integrability_of_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0)) :
    UnifIntegrable A 1 P := by
  exact unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num)
    (fun n => (memLp_one_iff_integrable.mpr (hA n))) (memLp_one_iff_integrable.mpr hX) (tendsto_eLpNorm_one_of_L1 P X A hX hA he)

lemma marginal_of_L1_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0))
    (μ : ℕ → ProbabilityMeasure (ℝ × ℝ)) (ν : ProbabilityMeasure (ℝ × ℝ))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hweak : Tendsto (μ ∘ φ) atTop (𝓝 ν))
    (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hmap : ∀ n, (μ n : Measure (ℝ × ℝ)).map f = P.map (A n)) :
    (ν : Measure (ℝ × ℝ)).map f = P.map X := by
  have hd := laws_tendsto_of_L1 P X A hX hA he
  have hds := hd.tendsto.comp hφ.tendsto_atTop
  have hms := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (μ ∘ φ) ν hweak hf
  have heq : (fun n => ((μ ∘ φ) n).map hf.measurable.aemeasurable) =
      (fun n => (⟨P.map (A (φ n)), Measure.isProbabilityMeasure_map (hd.forall_aemeasurable (φ n))⟩ : ProbabilityMeasure ℝ)) := by
    funext n
    apply Subtype.ext
    exact hmap (φ n)
  rw [heq] at hms
  have hu := tendsto_nhds_unique hms hds
  exact congrArg Subtype.val hu

end RiskOrderCompactness

namespace RiskOrderCompactness
lemma exists_finite_couplings_with_exact_marginal_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) (h : IcxOrder P P X Y) :
    ∃ A B : ℕ → Ω → ℝ, ∃ μ : ℕ → ProbabilityMeasure (ℝ × ℝ),
    ∃ ν : ProbabilityMeasure (ℝ × ℝ), ∃ φ : ℕ → ℕ,
      (∀ n, Measurable (A n) ∧ Measurable (B n) ∧
        (Set.range (A n)).Finite ∧ (Set.range (B n)).Finite ∧
        Integrable (A n) P ∧ Integrable (B n) P ∧
        (∫ ω, |X ω - A n ω| ∂P) < 1 / ((n : ℝ) + 1) ∧
        (∫ ω, |Y ω - B n ω| ∂P) < 1 / ((n : ℝ) + 1) ∧
        (μ n : Measure (ℝ × ℝ)).map Prod.fst = P.map (A n) ∧
        (μ n : Measure (ℝ × ℝ)).map Prod.snd = P.map (B n) ∧
        ∀ s : Set ℝ, MeasurableSet s →
          (∫ z in Prod.fst ⁻¹' s, z.1 ∂(μ n : Measure (ℝ × ℝ))) ≤
            ∫ z in Prod.fst ⁻¹' s, z.2 ∂(μ n : Measure (ℝ × ℝ))) ∧
      Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, |Y ω - B n ω| ∂P) atTop (𝓝 0) ∧
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      (ν : Measure (ℝ × ℝ)).map Prod.fst = P.map X ∧
      (ν : Measure (ℝ × ℝ)).map Prod.snd = P.map Y := by
  classical
  have hex : ∀ n : ℕ, ∃ A B : Ω → ℝ, ∃ μ : Measure (ℝ × ℝ),
      Measurable A ∧ Measurable B ∧ (Set.range A).Finite ∧ (Set.range B).Finite ∧
      Integrable A P ∧ Integrable B P ∧
      (∫ ω, |X ω - A ω| ∂P) < 1 / ((n : ℝ) + 1) ∧
      (∫ ω, |Y ω - B ω| ∂P) < 1 / ((n : ℝ) + 1) ∧
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P.map A ∧ μ.map Prod.snd = P.map B ∧
      ∀ s : Set ℝ, MeasurableSet s →
        (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ := by
    intro n
    exact RiskOrderApproximation.exists_finite_coupling_approximation P X Y hX hY h _ (by positivity)
  choose A B μ hmA hmB hFA hFB hiA hiB heA heB hμ hfst hsnd ht using hex
  let γ : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun n => ⟨μ n, hμ n⟩
  let C := (∫ ω, |X ω| ∂P) + (∫ ω, |Y ω| ∂P) + 2
  have hC : 0 ≤ C := by
    have h1 : 0 ≤ ∫ ω, |X ω| ∂P := integral_nonneg (fun ω => abs_nonneg (X ω))
    have h2 : 0 ≤ ∫ ω, |Y ω| ∂P := integral_nonneg (fun ω => abs_nonneg (Y ω))
    dsimp only [C]
    linarith
  have hb : ∀ n, Integrable (fun z : ℝ × ℝ => ‖z‖) (γ n : Measure (ℝ × ℝ)) ∧
      (∫ z, ‖z‖ ∂(γ n : Measure (ℝ × ℝ))) ≤ C := by
    intro n
    have hf : IdentDistrib Prod.fst (A n) (μ n) P :=
      ⟨measurable_fst.aemeasurable, (hmA n).aemeasurable, hfst n⟩
    have hs : IdentDistrib Prod.snd (B n) (μ n) P :=
      ⟨measurable_snd.aemeasurable, (hmB n).aemeasurable, hsnd n⟩
    have hε : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hh := pair_moment_bound P X Y (A n) (B n) hX hY (hiA n) (hiB n)
      (μ n) hf hs _ (heA n).le (heB n).le
    refine ⟨hh.1, hh.2.trans ?_⟩
    dsimp only [C]
    linarith
  obtain ⟨ν, φ, hφ, hlim⟩ := subsequence_of_bounded_first_moment γ C hC
    (fun n => (hb n).1) (fun n => (hb n).2)
  have heAX : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
      (fun n => (heA n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have heBY : Tendsto (fun n => ∫ ω, |Y ω - B n ω| ∂P) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
      (fun n => (heB n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨A, B, γ, ν, φ, ?_, heAX, heBY, hφ, hlim, ?_, ?_⟩
  · intro n
    exact ⟨hmA n, hmB n, hFA n, hFB n, hiA n, hiB n, heA n, heB n,
      hfst n, hsnd n, ht n⟩
  · exact marginal_of_L1_weak_limit P X A hX hiA heAX γ ν φ hφ hlim
      Prod.fst continuous_fst hfst
  · exact marginal_of_L1_weak_limit P Y B hY hiB heBY γ ν φ hφ hlim
      Prod.snd continuous_snd hsnd

end RiskOrderCompactness

open scoped NNReal ENNReal BoundedContinuousFunction

namespace RiskOrderCompactness
lemma full_uniform_integrability_of_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0))
    (hb : ∀ n, (∫ ω, |X ω - A n ω| ∂P) ≤ 1) :
    UniformIntegrable A 1 P := by
  let C := (∫ ω, |X ω| ∂P) + 1
  have hC : 0 ≤ C := by
    have hn : 0 ≤ ∫ ω, |X ω| ∂P := integral_nonneg (fun ω => abs_nonneg _)
    dsimp only [C]; linarith
  let c : ℝ≥0 := ⟨C, hC⟩
  refine ⟨fun n => (hA n).aestronglyMeasurable, uniform_integrability_of_L1 P X A hX hA he,
    ⟨c, ?_⟩⟩
  intro n
  have hn : eLpNorm (A n) 1 P = ENNReal.ofReal (∫ ω, |A n ω| ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hA n)]
    simp only [Real.norm_eq_abs]
  rw [hn]
  have hbound : (∫ ω, |A n ω| ∂P) ≤ C :=
    integral_abs_le_of_L1_close P X (A n) hX (hA n) 1 (hb n)
  calc
    ENNReal.ofReal (∫ ω, |A n ω| ∂P) ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hbound
    _ = (c : ℝ≥0∞) := by rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hC]; rfl

lemma uniform_abs_tails_of_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0))
    (hb : ∀ n, (∫ ω, |X ω - A n ω| ∂P) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      (∫ ω in {ω | (C : ℝ) ≤ |A n ω|}, |A n ω| ∂P) ≤ ε := by
  have hu := full_uniform_integrability_of_L1 P X A hX hA he hb
  obtain ⟨C, hC⟩ := hu.spec (by norm_num) (by norm_num) hε
  refine ⟨C, fun n => ?_⟩
  let s : Set Ω := {ω | C ≤ ‖A n ω‖₊}
  have hs : NullMeasurableSet s P :=
    ((hA n).aemeasurable.nnnorm.nullMeasurable measurableSet_Ici)
  have hi : Integrable (s.indicator (A n)) P := (hA n).indicator₀ hs
  have hn : eLpNorm (s.indicator (A n)) 1 P =
      ENNReal.ofReal (∫ ω in {ω | (C : ℝ) ≤ |A n ω|}, |A n ω| ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
    congr 1
    rw [← integral_indicator₀]
    · apply integral_congr_ae
      exact ae_of_all _ (fun ω => by
        simp only [s, Set.indicator, Real.norm_eq_abs, Set.mem_ofPred_eq]
        split_ifs <;> simp_all [← NNReal.coe_le_coe])
    · convert hs using 1
      ext ω
      simp only [s, Set.mem_ofPred_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  have h := hC n
  change eLpNorm (s.indicator (A n)) 1 P ≤ _ at h
  rw [hn] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

end RiskOrderCompactness

namespace RiskOrderCompactness
lemma abs_tail_integral_eq_of_identDistrib {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') (f : Ω → ℝ) (g : Ω' → ℝ)
    (hf : Measurable f) (hg : Measurable g) (h : IdentDistrib f g P Q) (C : ℝ) :
    (∫ ω in {ω | C ≤ |f ω|}, |f ω| ∂P) =
      ∫ ω in {ω | C ≤ |g ω|}, |g ω| ∂Q := by
  have hsf : MeasurableSet {ω | C ≤ |f ω|} := measurableSet_le measurable_const hf.abs
  have hsg : MeasurableSet {ω | C ≤ |g ω|} := measurableSet_le measurable_const hg.abs
  rw [← integral_indicator hsf, ← integral_indicator hsg]
  have hd := ((h.comp measurable_abs).comp (measurable_id.indicator (measurableSet_Ici (a := C)))).integral_eq
  simpa only [Function.comp_def, Set.indicator, Set.mem_Ici, Set.mem_ofPred_eq, id_eq] using hd

lemma uniform_law_abs_tails_of_L1 {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → ℝ) (A : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P) (hmA : ∀ n, Measurable (A n))
    (he : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0))
    (hb : ∀ n, (∫ ω, |X ω - A n ω| ∂P) ≤ 1)
    (μ : ℕ → Measure Ω') (f : Ω' → ℝ) (hf : Measurable f)
    (hmap : ∀ n, (μ n).map f = P.map (A n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      (∫ z in {z | (C : ℝ) ≤ |f z|}, |f z| ∂μ n) ≤ ε := by
  obtain ⟨C, hC⟩ := uniform_abs_tails_of_L1 P X A hX hA he hb ε hε
  refine ⟨C, fun n => ?_⟩
  have hd : IdentDistrib f (A n) (μ n) P :=
    ⟨hf.aemeasurable, (hmA n).aemeasurable, hmap n⟩
  rw [abs_tail_integral_eq_of_identDistrib (μ n) P f (A n) hf (hmA n) hd]
  exact hC n

end RiskOrderCompactness

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace RiskOrderLimit

def clip (C x : ℝ) : ℝ := max (-C) (min C x)

lemma continuous_clip (C : ℝ) : Continuous (clip C) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma abs_clip_le (C : ℝ) (hC : 0 ≤ C) (x : ℝ) : |clip C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma abs_sub_clip_le_abs (C : ℝ) (hC : 0 ≤ C) (x : ℝ) : |x - clip C x| ≤ |x| := by
  by_cases hx : x ≤ -C
  · have hxC : x ≤ C := by linarith
    rw [clip, min_eq_right hxC, max_eq_left hx, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · by_cases hxC : C ≤ x
    · rw [clip, min_eq_left hxC, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [clip, min_eq_right (le_of_not_ge hxC), max_eq_right (le_of_not_ge hx), sub_self, abs_zero]
      exact abs_nonneg _

lemma clip_eq_of_abs_lt (C x : ℝ) (hx : |x| < C) : clip C x = x := by
  obtain ⟨hl, hr⟩ := abs_lt.mp hx
  rw [clip, min_eq_right hr.le, max_eq_right hl.le]

lemma abs_sub_clip_le_tail (C : ℝ) (hC : 0 ≤ C) (x : ℝ) :
    |x - clip C x| ≤ {r : ℝ | C ≤ |r|}.indicator (fun r => |r|) x := by
  by_cases hx : C ≤ |x|
  · rw [indicator_of_mem (show x ∈ {r : ℝ | C ≤ |r|} from hx)]
    exact abs_sub_clip_le_abs C hC x
  · rw [indicator_of_notMem (show x ∉ {r : ℝ | C ≤ |r|} from hx), clip_eq_of_abs_lt C x (lt_of_not_ge hx), sub_self, abs_zero]

noncomputable def clippedTest (ψ : ℝ →ᵇ ℝ) (C : ℝ) (hC : 0 ≤ C) : (ℝ × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ψ z.1 * (clip C z.2 - clip C z.1))
    ((ψ.continuous.comp continuous_fst).mul
      (((continuous_clip C).comp continuous_snd).sub ((continuous_clip C).comp continuous_fst)))
    (‖ψ‖ * (2 * C)) (fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      have hp : |ψ z.1| ≤ ‖ψ‖ := by simpa only [Real.norm_eq_abs] using ψ.norm_coe_le_norm z.1
      have hd : |clip C z.2 - clip C z.1| ≤ 2 * C :=
        (abs_sub (clip C z.2) (clip C z.1)).trans (by linarith [abs_clip_le C hC z.2, abs_clip_le C hC z.1])
      exact mul_le_mul hp hd (abs_nonneg _) (norm_nonneg _))

lemma test_clipping_error (ψ : ℝ →ᵇ ℝ) (C : ℝ) (hC : 0 ≤ C) (z : ℝ × ℝ) :
    |ψ z.1 * (z.2 - z.1) - clippedTest ψ C hC z| ≤
      ‖ψ‖ * (|z.2 - clip C z.2| + |z.1 - clip C z.1|) := by
  change |ψ z.1 * (z.2 - z.1) - ψ z.1 * (clip C z.2 - clip C z.1)| ≤ _
  rw [← mul_sub, abs_mul]
  have he : (z.2 - z.1) - (clip C z.2 - clip C z.1) =
      (z.2 - clip C z.2) - (z.1 - clip C z.1) := by ring
  rw [he]
  have hp : |ψ z.1| ≤ ‖ψ‖ := by simpa only [Real.norm_eq_abs] using ψ.norm_coe_le_norm z.1
  exact mul_le_mul hp (abs_sub _ _) (abs_nonneg _) (norm_nonneg _)

end RiskOrderLimit

namespace RiskOrderLimit
lemma integrable_test (μ : Measure (ℝ × ℝ)) (ψ : ℝ →ᵇ ℝ)
    (hf : Integrable Prod.fst μ) (hs : Integrable Prod.snd μ) :
    Integrable (fun z : ℝ × ℝ => ψ z.1 * (z.2 - z.1)) μ :=
  (hs.sub hf).bdd_mul (ψ.continuous.comp continuous_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => ψ.norm_coe_le_norm z.1))

lemma integral_test_clipping_error (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (ψ : ℝ →ᵇ ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Integrable Prod.fst μ) (hs : Integrable Prod.snd μ) :
    |(∫ z, ψ z.1 * (z.2 - z.1) ∂μ) - (∫ z, clippedTest ψ C hC z ∂μ)| ≤
      ‖ψ‖ * ((∫ z in {z : ℝ × ℝ | C ≤ |z.1|}, |z.1| ∂μ) +
        ∫ z in {z : ℝ × ℝ | C ≤ |z.2|}, |z.2| ∂μ) := by
  let F : Set (ℝ × ℝ) := {z | C ≤ |z.1|}
  let S : Set (ℝ × ℝ) := {z | C ≤ |z.2|}
  have hF : MeasurableSet F := measurableSet_le measurable_const measurable_fst.abs
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_snd.abs
  have hiF : Integrable (F.indicator (fun z => |z.1|)) μ := hf.abs.indicator hF
  have hiS : Integrable (S.indicator (fun z => |z.2|)) μ := hs.abs.indicator hS
  have hiT := integrable_test μ ψ hf hs
  have hiC : Integrable (clippedTest ψ C hC) μ := (clippedTest ψ C hC).integrable μ
  have hb : ∀ z : ℝ × ℝ,
      |ψ z.1 * (z.2 - z.1) - clippedTest ψ C hC z| ≤
        ‖ψ‖ * (F.indicator (fun z => |z.1|) z + S.indicator (fun z => |z.2|) z) := by
    intro z
    have h1 := abs_sub_clip_le_tail C hC z.1
    have h2 := abs_sub_clip_le_tail C hC z.2
    have he1 : {r : ℝ | C ≤ |r|}.indicator (fun r => |r|) z.1 = F.indicator (fun z => |z.1|) z := by
      simp only [F, indicator, mem_ofPred_eq]
    have he2 : {r : ℝ | C ≤ |r|}.indicator (fun r => |r|) z.2 = S.indicator (fun z => |z.2|) z := by
      simp only [S, indicator, mem_ofPred_eq]
    rw [he1] at h1
    rw [he2] at h2
    exact (test_clipping_error ψ C hC z).trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
  rw [← integral_sub hiT hiC]
  calc
    |∫ z, ψ z.1 * (z.2 - z.1) - clippedTest ψ C hC z ∂μ| ≤
        ∫ z, |ψ z.1 * (z.2 - z.1) - clippedTest ψ C hC z| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => ψ z.1 * (z.2 - z.1) - clippedTest ψ C hC z)
    _ ≤ ∫ z, ‖ψ‖ * (F.indicator (fun z => |z.1|) z + S.indicator (fun z => |z.2|) z) ∂μ :=
      integral_mono (hiT.sub hiC).abs ((hiF.add hiS).const_mul ‖ψ‖) hb
    _ = _ := by
      rw [integral_const_mul, integral_add hiF hiS, integral_indicator hF, integral_indicator hS]

end RiskOrderLimit

namespace RiskOrderLimit
lemma tendsto_test_integral_of_uniform_tails
    (μ : ℕ → ProbabilityMeasure (ℝ × ℝ)) (ν : ProbabilityMeasure (ℝ × ℝ))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hf : ∀ n, Integrable Prod.fst (μ n : Measure (ℝ × ℝ)))
    (hs : ∀ n, Integrable Prod.snd (μ n : Measure (ℝ × ℝ)))
    (hvf : Integrable Prod.fst (ν : Measure (ℝ × ℝ)))
    (hvs : Integrable Prod.snd (ν : Measure (ℝ × ℝ)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      (∀ n, ((∫ z in {z : ℝ × ℝ | C ≤ |z.1|}, |z.1| ∂(μ n : Measure (ℝ × ℝ))) +
        ∫ z in {z : ℝ × ℝ | C ≤ |z.2|}, |z.2| ∂(μ n : Measure (ℝ × ℝ))) ≤ ε) ∧
      ((∫ z in {z : ℝ × ℝ | C ≤ |z.1|}, |z.1| ∂(ν : Measure (ℝ × ℝ))) +
        ∫ z in {z : ℝ × ℝ | C ≤ |z.2|}, |z.2| ∂(ν : Measure (ℝ × ℝ))) ≤ ε)
    (ψ : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, ψ z.1 * (z.2 - z.1) ∂(μ n : Measure (ℝ × ℝ))) atTop
      (𝓝 (∫ z, ψ z.1 * (z.2 - z.1) ∂(ν : Measure (ℝ × ℝ)))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / (4 * (‖ψ‖ + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : 4 * (‖ψ‖ + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  obtain ⟨C, hC, htμ, htν⟩ := htail δ hδ
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (clippedTest ψ C hC)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := (integral_test_clipping_error (μ n : Measure (ℝ × ℝ)) ψ C hC (hf n) (hs n)).trans
    (mul_le_mul_of_nonneg_left (htμ n) (norm_nonneg _))
  have h2 := (integral_test_clipping_error (ν : Measure (ℝ × ℝ)) ψ C hC hvf hvs).trans
    (mul_le_mul_of_nonneg_left htν (norm_nonneg _))
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have ha := abs_sub_le
    (∫ z, ψ z.1 * (z.2 - z.1) ∂(μ n : Measure (ℝ × ℝ)))
    (∫ z, clippedTest ψ C hC z ∂(ν : Measure (ℝ × ℝ)))
    (∫ z, ψ z.1 * (z.2 - z.1) ∂(ν : Measure (ℝ × ℝ)))
  have hb := abs_sub_le
    (∫ z, ψ z.1 * (z.2 - z.1) ∂(μ n : Measure (ℝ × ℝ)))
    (∫ z, clippedTest ψ C hC z ∂(μ n : Measure (ℝ × ℝ)))
    (∫ z, clippedTest ψ C hC z ∂(ν : Measure (ℝ × ℝ)))
  rw [abs_sub_comm (∫ z, ψ z.1 * (z.2 - z.1) ∂(ν : Measure (ℝ × ℝ)))] at h2
  nlinarith

end RiskOrderLimit

namespace RiskOrderLimit
lemma abs_tail_antitone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f P) (a b : ℝ) (hab : a ≤ b) :
    (∫ ω in {ω | b ≤ |f ω|}, |f ω| ∂P) ≤ ∫ ω in {ω | a ≤ |f ω|}, |f ω| ∂P := by
  apply setIntegral_mono_set hf.abs.integrableOn (ae_of_all _ (fun ω => abs_nonneg _))
  exact ae_of_all _ (fun ω hω => hab.trans hω)

lemma abs_tails_of_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f P) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, (∫ ω in {ω | (C : ℝ) ≤ |f ω|}, |f ω| ∂P) ≤ ε := by
  have he : Tendsto (fun _ : ℕ => ∫ ω, |f ω - f ω| ∂P) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨C, hC⟩ := RiskOrderCompactness.uniform_abs_tails_of_L1 P f (fun _ => f) hf
    (fun _ => hf) he (fun _ => by simp) ε hε
  exact ⟨C, hC 0⟩

lemma tendsto_test_integral_of_L1_marginals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (A B : ℕ → Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (hA : ∀ n, Integrable (A n) P) (hB : ∀ n, Integrable (B n) P)
    (hmA : ∀ n, Measurable (A n)) (hmB : ∀ n, Measurable (B n))
    (heA : Tendsto (fun n => ∫ ω, |X ω - A n ω| ∂P) atTop (𝓝 0))
    (heB : Tendsto (fun n => ∫ ω, |Y ω - B n ω| ∂P) atTop (𝓝 0))
    (hbA : ∀ n, (∫ ω, |X ω - A n ω| ∂P) ≤ 1)
    (hbB : ∀ n, (∫ ω, |Y ω - B n ω| ∂P) ≤ 1)
    (μ : ℕ → ProbabilityMeasure (ℝ × ℝ)) (ν : ProbabilityMeasure (ℝ × ℝ))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hfst : ∀ n, (μ n : Measure (ℝ × ℝ)).map Prod.fst = P.map (A n))
    (hsnd : ∀ n, (μ n : Measure (ℝ × ℝ)).map Prod.snd = P.map (B n))
    (hvfst : (ν : Measure (ℝ × ℝ)).map Prod.fst = P.map X)
    (hvsnd : (ν : Measure (ℝ × ℝ)).map Prod.snd = P.map Y)
    (ψ : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ z, ψ z.1 * (z.2 - z.1) ∂(μ n : Measure (ℝ × ℝ))) atTop
      (𝓝 (∫ z, ψ z.1 * (z.2 - z.1) ∂(ν : Measure (ℝ × ℝ)))) := by
  have hif : ∀ n, Integrable Prod.fst (μ n : Measure (ℝ × ℝ)) := by
    intro n
    have hd : ProbabilityTheory.IdentDistrib Prod.fst (A n) (μ n : Measure (ℝ × ℝ)) P :=
      ⟨measurable_fst.aemeasurable, (hmA n).aemeasurable, hfst n⟩
    exact hd.integrable_iff.mpr (hA n)
  have his : ∀ n, Integrable Prod.snd (μ n : Measure (ℝ × ℝ)) := by
    intro n
    have hd : ProbabilityTheory.IdentDistrib Prod.snd (B n) (μ n : Measure (ℝ × ℝ)) P :=
      ⟨measurable_snd.aemeasurable, (hmB n).aemeasurable, hsnd n⟩
    exact hd.integrable_iff.mpr (hB n)
  have hdf : ProbabilityTheory.IdentDistrib Prod.fst X (ν : Measure (ℝ × ℝ)) P :=
    ⟨measurable_fst.aemeasurable, hX.aemeasurable, hvfst⟩
  have hds : ProbabilityTheory.IdentDistrib Prod.snd Y (ν : Measure (ℝ × ℝ)) P :=
    ⟨measurable_snd.aemeasurable, hY.aemeasurable, hvsnd⟩
  have hvf := hdf.integrable_iff.mpr hX
  have hvs := hds.integrable_iff.mpr hY
  apply tendsto_test_integral_of_uniform_tails μ ν hweak hif his hvf hvs ?_ ψ
  intro ε hε
  obtain ⟨CA, hCA⟩ := RiskOrderCompactness.uniform_law_abs_tails_of_L1 P X A hX hA hmA
    heA hbA (fun n => (μ n : Measure (ℝ × ℝ))) Prod.fst measurable_fst hfst (ε / 2) (half_pos hε)
  obtain ⟨CB, hCB⟩ := RiskOrderCompactness.uniform_law_abs_tails_of_L1 P Y B hY hB hmB
    heB hbB (fun n => (μ n : Measure (ℝ × ℝ))) Prod.snd measurable_snd hsnd (ε / 2) (half_pos hε)
  obtain ⟨CF, hCF⟩ := abs_tails_of_integrable (ν : Measure (ℝ × ℝ)) Prod.fst hvf (ε / 2) (half_pos hε)
  obtain ⟨CS, hCS⟩ := abs_tails_of_integrable (ν : Measure (ℝ × ℝ)) Prod.snd hvs (ε / 2) (half_pos hε)
  let C : ℝ := max (max (CA : ℝ) (CB : ℝ)) (max (CF : ℝ) (CS : ℝ))
  have hAC : (CA : ℝ) ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hBC : (CB : ℝ) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hFC : (CF : ℝ) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hSC : (CS : ℝ) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, CA.coe_nonneg.trans hAC, ?_, ?_⟩
  · intro n
    have ha := (abs_tail_antitone (μ n : Measure (ℝ × ℝ)) Prod.fst (hif n) _ _ hAC).trans (hCA n)
    have hb := (abs_tail_antitone (μ n : Measure (ℝ × ℝ)) Prod.snd (his n) _ _ hBC).trans (hCB n)
    linarith
  · have ha := (abs_tail_antitone (ν : Measure (ℝ × ℝ)) Prod.fst hvf _ _ hFC).trans hCF
    have hb := (abs_tail_antitone (ν : Measure (ℝ × ℝ)) Prod.snd hvs _ _ hSC).trans hCS
    linarith

end RiskOrderLimit

namespace RiskOrderLimit
lemma le_condExp_of_borel_tests {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → ℝ)
    (hmA : Measurable A) (hA : Integrable A P) (hB : Integrable B P)
    (htests : ∀ s : Set ℝ, MeasurableSet s →
      (∫ ω in A ⁻¹' s, A ω ∂P) ≤ ∫ ω in A ⁻¹' s, B ω ∂P) :
    A ≤ᵐ[P] P[B|MeasurableSpace.comap A inferInstance] := by
  let m := MeasurableSpace.comap A inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := hmA.comap_le
  have hAm : StronglyMeasurable[m] A := (comap_measurable A).stronglyMeasurable
  have hCm : StronglyMeasurable[m] (P[B|m]) := stronglyMeasurable_condExp
  have htA := hA.trim hm hAm
  have htC := (integrable_condExp (μ := P) (m := m) (f := B)).trim hm hCm
  have ht : A ≤ᵐ[P.trim hm] P[B|m] := by
    apply ae_le_of_forall_setIntegral_le htA htC
    intro s hs _
    rw [← setIntegral_trim hm hAm hs, ← setIntegral_trim hm hCm hs,
      setIntegral_condExp hm hB hs]
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    exact htests t ht
  exact ae_le_of_ae_le_trim ht


lemma nonnegative_continuous_test_of_borel_tests
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hf : Integrable Prod.fst μ) (hs : Integrable Prod.snd μ)
    (ht : ∀ s : Set ℝ, MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ)
    (ψ : ℝ →ᵇ ℝ) (hψ : ∀ x, 0 ≤ ψ x) :
    0 ≤ ∫ z, ψ z.1 * (z.2 - z.1) ∂μ := by
  let m : MeasurableSpace (ℝ × ℝ) := MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) (inferInstance : MeasurableSpace ℝ)
  letI : MeasurableSpace (ℝ × ℝ) := Prod.instMeasurableSpace
  have hm : m ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) := by
    exact (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ)).comap_le
  have hψm : StronglyMeasurable[m] (fun z : ℝ × ℝ => ψ z.1) :=
    (ψ.continuous.measurable.comp (comap_measurable Prod.fst)).stronglyMeasurable
  have ha := le_condExp_of_borel_tests μ Prod.fst Prod.snd measurable_fst hf hs ht
  have hψM : AEStronglyMeasurable (fun z : ℝ × ℝ => ψ z.1) μ :=
    (ψ.continuous.comp continuous_fst).aestronglyMeasurable
  have hbound : ∀ᵐ z : ℝ × ℝ ∂μ, ‖ψ z.1‖ ≤ ‖ψ‖ :=
    ae_of_all _ (fun z => ψ.norm_coe_le_norm z.1)
  have hip := hs.bdd_mul hψM hbound
  have hif := hf.bdd_mul hψM hbound
  have hic := (integrable_condExp (μ := μ) (m := m) (f := Prod.snd)).bdd_mul hψM hbound
  have hpull := condExp_mul_of_stronglyMeasurable_left hψm hip hs
  have he : (∫ z, ψ z.1 * μ[Prod.snd|m] z ∂μ) = ∫ z, ψ z.1 * z.2 ∂μ := by
    calc
      _ = ∫ z, μ[(fun z : ℝ × ℝ => ψ z.1) * Prod.snd|m] z ∂μ :=
        (integral_congr_ae hpull).symm
      _ = _ := integral_condExp hm
  have hi : (∫ z, ψ z.1 * z.1 ∂μ) ≤ ∫ z, ψ z.1 * z.2 ∂μ := by
    rw [← he]
    apply integral_mono_ae hif hic
    filter_upwards [ha] with z hz
    exact mul_le_mul_of_nonneg_left hz (hψ z.1)
  have he2 : (∫ z, ψ z.1 * (z.2 - z.1) ∂μ) =
      (∫ z, ψ z.1 * z.2 ∂μ) - ∫ z, ψ z.1 * z.1 ∂μ := by
    simp_rw [mul_sub]
    exact integral_sub hip hif
  rw [he2]
  linarith

end RiskOrderLimit

namespace RiskOrderLimit
lemma exists_coupling_law_continuous_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) (h : IcxOrder P P X Y) :
    ∃ ν : ProbabilityMeasure (ℝ × ℝ),
      (ν : Measure (ℝ × ℝ)).map Prod.fst = P.map X ∧
      (ν : Measure (ℝ × ℝ)).map Prod.snd = P.map Y ∧
      ∀ ψ : ℝ →ᵇ ℝ, (∀ x, 0 ≤ ψ x) →
        0 ≤ ∫ z, ψ z.1 * (z.2 - z.1) ∂(ν : Measure (ℝ × ℝ)) := by
  obtain ⟨A, B, μ, ν, φ, hdata, heA, heB, hφ, hweak, hvf, hvs⟩ :=
    RiskOrderCompactness.exists_finite_couplings_with_exact_marginal_limit P X Y hX hY h
  have hmA : ∀ n, Measurable (A n) := fun n => (hdata n).1
  have hmB : ∀ n, Measurable (B n) := fun n => (hdata n).2.1
  have hiA : ∀ n, Integrable (A n) P := fun n => (hdata n).2.2.2.2.1
  have hiB : ∀ n, Integrable (B n) P := fun n => (hdata n).2.2.2.2.2.1
  have hfst : ∀ n, (μ n : Measure (ℝ × ℝ)).map Prod.fst = P.map (A n) :=
    fun n => (hdata n).2.2.2.2.2.2.2.2.1
  have hsnd : ∀ n, (μ n : Measure (ℝ × ℝ)).map Prod.snd = P.map (B n) :=
    fun n => (hdata n).2.2.2.2.2.2.2.2.2.1
  have ht : ∀ n, ∀ s : Set ℝ, MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 ∂(μ n : Measure (ℝ × ℝ))) ≤
        ∫ z in Prod.fst ⁻¹' s, z.2 ∂(μ n : Measure (ℝ × ℝ)) :=
    fun n => (hdata n).2.2.2.2.2.2.2.2.2.2
  have hbA : ∀ n, (∫ ω, |X ω - A n ω| ∂P) ≤ 1 := by
    intro n
    have hn := (hdata n).2.2.2.2.2.2.1
    have hb : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hnn := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact hn.le.trans hb
  have hbB : ∀ n, (∫ ω, |Y ω - B n ω| ∂P) ≤ 1 := by
    intro n
    have hn := (hdata n).2.2.2.2.2.2.2.1
    have hb : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hnn := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact hn.le.trans hb
  refine ⟨ν, hvf, hvs, ?_⟩
  intro ψ hψ
  have hlim := tendsto_test_integral_of_L1_marginals P X Y (A ∘ φ) (B ∘ φ) hX hY
    (fun n => hiA (φ n)) (fun n => hiB (φ n)) (fun n => hmA (φ n)) (fun n => hmB (φ n))
    (heA.comp hφ.tendsto_atTop) (heB.comp hφ.tendsto_atTop)
    (fun n => hbA (φ n)) (fun n => hbB (φ n)) (μ ∘ φ) ν hweak
    (fun n => hfst (φ n)) (fun n => hsnd (φ n)) hvf hvs ψ
  apply ge_of_tendsto' hlim
  intro n
  have hdf : ProbabilityTheory.IdentDistrib Prod.fst (A (φ n)) (μ (φ n) : Measure (ℝ × ℝ)) P :=
    ⟨measurable_fst.aemeasurable, (hmA (φ n)).aemeasurable, hfst (φ n)⟩
  have hds : ProbabilityTheory.IdentDistrib Prod.snd (B (φ n)) (μ (φ n) : Measure (ℝ × ℝ)) P :=
    ⟨measurable_snd.aemeasurable, (hmB (φ n)).aemeasurable, hsnd (φ n)⟩
  exact nonnegative_continuous_test_of_borel_tests (μ (φ n) : Measure (ℝ × ℝ))
    (hdf.integrable_iff.mpr (hiA (φ n))) (hds.integrable_iff.mpr (hiB (φ n))) (ht (φ n)) ψ hψ

end RiskOrderLimit

open MeasureTheory Set Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace RiskOrderLimit

lemma closed_test_of_continuous_tests (μ : Measure (ℝ × ℝ))
    (hf : Integrable Prod.fst μ) (hg : Integrable Prod.snd μ)
    (ht : ∀ ψ : ℝ →ᵇ ℝ, (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ z, ψ z.1 * (z.2 - z.1) ∂μ)
    (s : Set ℝ) (hs : IsClosed s) :
    0 ≤ ∫ z in Prod.fst ⁻¹' s, z.2 - z.1 ∂μ := by
  let ψ : ℕ → ℝ →ᵇ ℝ := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (hs.apprSeq n x : ℝ))
    (NNReal.continuous_coe.comp (hs.apprSeq n).continuous) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hs.apprSeq n x).coe_nonneg]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs n x)
  have hψnon : ∀ n x, 0 ≤ ψ n x := fun n x => (hs.apprSeq n x).coe_nonneg
  have hψle : ∀ n x, |ψ n x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (hψnon n x)]
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs n x
  have hψlim : ∀ x, Tendsto (fun n => ψ n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℝ)) x)) := by
    intro x
    have h := (NNReal.continuous_coe.tendsto (s.indicator (fun _ => (1 : ℝ≥0)) x)).comp
      (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hs) x)
    by_cases hx : x ∈ s <;> simpa [ψ, indicator, hx, Function.comp_def] using h
  have hlim : Tendsto (fun n => ∫ z, ψ n z.1 * (z.2 - z.1) ∂μ) atTop
      (𝓝 (∫ z, (Prod.fst ⁻¹' s).indicator (fun z : ℝ × ℝ => z.2 - z.1) z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun z : ℝ × ℝ => |z.2| + |z.1|)
      (fun n => ((ψ n).continuous.comp continuous_fst).mul
        (continuous_snd.sub continuous_fst) |>.aestronglyMeasurable)
      (hg.abs.add hf.abs)
    · intro n
      apply ae_of_all
      intro z
      simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
      rw [abs_mul]
      calc
        |ψ n z.1| * |z.2 - z.1| ≤ 1 * |z.2 - z.1| :=
          mul_le_mul_of_nonneg_right (hψle n z.1) (abs_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using abs_sub z.2 z.1
    · apply ae_of_all
      intro z
      have he : s.indicator (fun _ => (1 : ℝ)) z.1 * (z.2 - z.1) =
          (Prod.fst ⁻¹' s).indicator (fun z : ℝ × ℝ => z.2 - z.1) z := by
        by_cases hz : z.1 ∈ s <;> simp [indicator, hz]
      simpa only [he, Pi.mul_apply, Pi.sub_apply, Function.comp_apply] using (hψlim z.1).mul (tendsto_const_nhds (x := z.2 - z.1))
  rw [integral_indicator (measurable_fst hs.measurableSet)] at hlim
  exact ge_of_tendsto' hlim (fun n => ht (ψ n) (hψnon n))

end RiskOrderLimit

open MeasureTheory Set
open scoped ENNReal Topology
namespace RiskOrderLimit

noncomputable def firstWeightedLaw (μ : Measure (ℝ × ℝ)) (w : ℝ × ℝ → ℝ) : Measure ℝ :=
  (μ.withDensity (fun z => ENNReal.ofReal (w z))).map Prod.fst

lemma firstWeightedLaw_finite (μ : Measure (ℝ × ℝ)) (w : ℝ × ℝ → ℝ)
    (hw : Integrable w μ) (hwn : ∀ z, 0 ≤ w z) : IsFiniteMeasure (firstWeightedLaw μ w) := by
  have he := ofReal_integral_eq_lintegral_ofReal hw (ae_of_all _ hwn)
  have hi : (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≠ ⊤ := by rw [← he]; exact ENNReal.ofReal_ne_top
  letI := isFiniteMeasure_withDensity hi
  exact Measure.isFiniteMeasure_map _ _

lemma firstWeightedLaw_apply (μ : Measure (ℝ × ℝ)) (w : ℝ × ℝ → ℝ)
    (hw : Integrable w μ) (hwn : ∀ z, 0 ≤ w z) (s : Set ℝ) (hs : MeasurableSet s) :
    firstWeightedLaw μ w s = ENNReal.ofReal (∫ z in Prod.fst ⁻¹' s, w z ∂μ) := by
  rw [firstWeightedLaw, Measure.map_apply measurable_fst hs,
    withDensity_apply _ (measurable_fst hs)]
  exact (ofReal_integral_eq_lintegral_ofReal hw.integrableOn (ae_of_all _ hwn)).symm

lemma borel_test_of_closed_tests (μ : Measure (ℝ × ℝ))
    (hf : Integrable Prod.fst μ) (hg : Integrable Prod.snd μ)
    (ht : ∀ s : Set ℝ, IsClosed s → 0 ≤ ∫ z in Prod.fst ⁻¹' s, z.2 - z.1 ∂μ) :
    ∀ s : Set ℝ, MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ := by
  let p : ℝ × ℝ → ℝ := fun z => max (z.2 - z.1) 0
  let q : ℝ × ℝ → ℝ := fun z => max (-(z.2 - z.1)) 0
  have hp : Integrable p μ := (hg.sub hf).pos_part
  have hq : Integrable q μ := (hg.sub hf).neg_part
  have hpn : ∀ z, 0 ≤ p z := fun z => le_max_right _ _
  have hqn : ∀ z, 0 ≤ q z := fun z => le_max_right _ _
  let M := firstWeightedLaw μ p
  let N := firstWeightedLaw μ q
  letI : IsFiniteMeasure M := firstWeightedLaw_finite μ p hp hpn
  letI : IsFiniteMeasure N := firstWeightedLaw_finite μ q hq hqn
  have hd : ∀ z : ℝ × ℝ, p z - q z = z.2 - z.1 := by
    intro z
    dsimp only [p, q]
    by_cases hz : 0 ≤ z.2 - z.1
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right (le_of_not_ge hz), max_eq_left (by linarith)]; ring
  have he : ∀ s : Set ℝ, (∫ z in Prod.fst ⁻¹' s, z.2 - z.1 ∂μ) =
      (∫ z in Prod.fst ⁻¹' s, p z ∂μ) - ∫ z in Prod.fst ⁻¹' s, q z ∂μ := by
    intro s
    rw [← integral_sub hp.integrableOn hq.integrableOn]
    exact integral_congr_ae (ae_of_all _ (fun z => (hd z).symm))
  have hclosed : ∀ s : Set ℝ, IsClosed s → N s ≤ M s := by
    intro s hs
    have hi := ht s hs
    rw [he s] at hi
    change firstWeightedLaw μ q s ≤ firstWeightedLaw μ p s
    rw [firstWeightedLaw_apply μ q hq hqn s hs.measurableSet,
      firstWeightedLaw_apply μ p hp hpn s hs.measurableSet]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  intro s hs
  have hNM : N s ≤ M s := by
    rw [hs.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top N s)]
    refine iSup_le (fun K => iSup_le (fun hKs => iSup_le (fun hK => ?_)))
    exact (hclosed K hK).trans (measure_mono hKs)
  change firstWeightedLaw μ q s ≤ firstWeightedLaw μ p s at hNM
  rw [firstWeightedLaw_apply μ q hq hqn s hs, firstWeightedLaw_apply μ p hp hpn s hs] at hNM
  have hpos : 0 ≤ ∫ z in Prod.fst ⁻¹' s, p z ∂μ := integral_nonneg hpn
  have hreal := (ENNReal.ofReal_le_ofReal_iff hpos).mp hNM
  have hi : 0 ≤ ∫ z in Prod.fst ⁻¹' s, z.2 - z.1 ∂μ := by rw [he s]; linarith
  rw [integral_sub hg.integrableOn hf.integrableOn] at hi
  linarith

end RiskOrderLimit

open MeasureTheory Set Filter
open scoped Topology
open ConvexRiskFn.Order

namespace RiskOrderQuantile
lemma cdfOf_eq_cdf_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    cdfOf P X = ProbabilityTheory.cdf (P.map X) := by
  let : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  funext t
  rw [ProbabilityTheory.cdf_eq_real, Measure.real, Measure.map_apply hX measurableSet_Iic]
  rfl

lemma level_nonempty (F : ℝ → ℝ) (h1 : Tendsto F atTop (𝓝 1))
    (t : ℝ) (ht : t < 1) : {s : ℝ | t ≤ F s}.Nonempty := by
  obtain ⟨s, hs⟩ := (h1.eventually (Ioi_mem_nhds ht)).exists
  exact ⟨s, hs.le⟩

lemma level_bddBelow (F : ℝ → ℝ) (hmono : Monotone F)
    (h0 : Tendsto F atBot (𝓝 0)) (t : ℝ) (ht : 0 < t) :
    BddBelow {s : ℝ | t ≤ F s} := by
  obtain ⟨s, hs⟩ := (h0.eventually (Iio_mem_nhds ht)).exists
  refine ⟨s, ?_⟩
  intro x hx
  by_contra hn
  have := hmono (le_of_lt (lt_of_not_ge hn))
  exact (not_le_of_gt hs) (hx.trans this)

lemma inverse_order (F₁ F₂ : ℝ → ℝ) (hmono : Monotone F₁)
    (h0 : Tendsto F₁ atBot (𝓝 0)) (h1 : Tendsto F₂ atTop (𝓝 1))
    (hF : ∀ s, F₂ s ≤ F₁ s) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    cdfInv F₁ t ≤ cdfInv F₂ t := by
  exact csInf_le_csInf (level_bddBelow F₁ hmono h0 t ht.1)
    (level_nonempty F₂ h1 t ht.2) (fun s hs => hs.trans (hF s))

lemma inverse_le_iff (F : StieltjesFunction ℝ)
    (h0 : Tendsto F atBot (𝓝 0)) (h1 : Tendsto F atTop (𝓝 1))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : ℝ) :
    cdfInv F t ≤ x ↔ t ≤ F x := by
  have hb := level_bddBelow F F.mono h0 t ht.1
  have hn := level_nonempty F h1 t ht.2
  constructor
  · intro hx
    rw [← F.iInf_Ioi_eq x]
    apply le_ciInf
    intro r
    obtain ⟨s, hs, hsr⟩ := (csInf_lt_iff hb hn).mp (lt_of_le_of_lt hx r.2)
    exact hs.trans (F.mono hsr.le)
  · intro hx
    exact csInf_le hb hx

lemma inverse_zero_of_nonpos (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x)
    (t : ℝ) (ht : t ≤ 0) : cdfInv F t = 0 := by
  have he : {s : ℝ | t ≤ F s} = univ := by
    ext s; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact ht.trans (hF s)
  rw [cdfInv, he, csInf_of_not_bddBelow (s := (univ : Set ℝ)) not_bddBelow_univ, Real.sInf_empty]

lemma inverse_zero_of_gt_one (F : ℝ → ℝ) (hF : ∀ x, F x ≤ 1)
    (t : ℝ) (ht : 1 < t) : cdfInv F t = 0 := by
  have he : {s : ℝ | t ≤ F s} = ∅ := by
    ext s; simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr (lt_of_le_of_lt (hF s) ht)
  rw [cdfInv, he, Real.sInf_empty]

lemma inverse_measurable (F : StieltjesFunction ℝ)
    (h0 : Tendsto F atBot (𝓝 0)) (h1 : Tendsto F atTop (𝓝 1))
    (hnonneg : ∀ x, 0 ≤ F x) (hone : ∀ x, F x ≤ 1) :
    Measurable (cdfInv F) := by
  apply measurable_of_Iic
  intro x
  have he : (cdfInv F) ⁻¹' Set.Iic x =
      {t : ℝ | (0 < t ∧ t < 1 ∧ t ≤ F x) ∨
        (t ≤ 0 ∧ 0 ≤ x) ∨ (1 < t ∧ 0 ≤ x) ∨ (t = 1 ∧ cdfInv F 1 ≤ x)} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Iic, mem_ofPred_eq]
    by_cases ht0 : t ≤ 0
    · rw [inverse_zero_of_nonpos F hnonneg t ht0]
      simp [ht0, not_lt.mpr ht0, show ¬1 < t by linarith, show t ≠ 1 by linarith]
    · by_cases ht1 : 1 < t
      · rw [inverse_zero_of_gt_one F hone t ht1]
        simp [ht0, ht1, not_lt.mpr ht1.le, ne_of_gt ht1]
      · by_cases ht : t = 1
        · subst t; simp
        · have hi : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_not_ge ht0, lt_of_le_of_ne (le_of_not_gt ht1) ht⟩
          rw [inverse_le_iff F h0 h1 t hi x]
          simp [hi.1, hi.2, ht0, ht1, ht]
  rw [he]
  measurability

lemma uniform_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U) :
    P.map U = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  let : IsProbabilityMeasure (P.map U) := Measure.isProbabilityMeasure_map hU.1.aemeasurable
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hU.1 measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  by_cases ht0 : t < 0
  · have hzero := hU.2 0 (by simp)
    have hsub : {ω | U ω ≤ t} ⊆ {ω | U ω ≤ 0} := fun ω hω => hω.trans ht0.le
    have he : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = ∅ := by ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]; intro hx; linarith [hx.1,hx.2.1]
    change P {ω | U ω ≤ t} = _
    rw [he, measure_empty]
    apply le_antisymm ?_ zero_le
    simpa only [hzero, ENNReal.ofReal_zero] using (measure_mono (μ := P) hsub)
  · by_cases ht1 : t ≤ 1
    · have he : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨hxt, hx0, _⟩; exact ⟨hx0, hxt⟩
        · rintro ⟨hx0, hxt⟩; exact ⟨hxt, hx0, hxt.trans ht1⟩
      change P {ω | U ω ≤ t} = _
      rw [hU.2 t ⟨le_of_not_gt ht0, ht1⟩, he, Real.volume_Icc, sub_zero]
    · have hsub : {ω | U ω ≤ 1} ⊆ {ω | U ω ≤ t} := fun ω hω => hω.trans (le_of_not_ge ht1)
      have he : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
        apply Set.inter_eq_right.mpr
        intro x hx; exact hx.2.trans (le_of_not_ge ht1)
      change P {ω | U ω ≤ t} = _
      rw [he]; simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
      apply le_antisymm (prob_le_one) ?_
      simpa only [hU.2 1 (by simp), ENNReal.ofReal_one] using (measure_mono (μ := P) hsub)

lemma uniform_ae_interior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U) :
    ∀ᵐ ω ∂P, U ω ∈ Set.Ioo (0 : ℝ) 1 := by
  apply ae_of_ae_map hU.1.aemeasurable
  rw [uniform_map P U hU]
  filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne (volume.restrict (Set.Icc (0 : ℝ) 1)) 0, Measure.ae_ne (volume.restrict (Set.Icc (0 : ℝ) 1)) 1] with x hx hx0 hx1
  exact ⟨lt_of_le_of_ne hx.1 hx0.symm, lt_of_le_of_ne hx.2 hx1⟩

end RiskOrderQuantile

open ProbabilityTheory RiskOrderQuantile
namespace RiskOrderStochastic
lemma quantile_identDistrib {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U)
    (Q : Measure Ω') [IsProbabilityMeasure Q] (X : Ω' → ℝ) (hX : Measurable X) :
    IdentDistrib (fun ω => cdfInv (cdfOf Q X) (U ω)) X P Q := by
  let : IsProbabilityMeasure (Q.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hc := cdfOf_eq_cdf_map Q X hX
  have hq : Measurable (fun ω => cdfInv (cdfOf Q X) (U ω)) := by
    rw [hc]
    exact (inverse_measurable (cdf (Q.map X)) (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)
      (cdf_nonneg _) (cdf_le_one _)).comp hU.1
  refine ⟨hq.aemeasurable, hX.aemeasurable, ?_⟩
  let : IsProbabilityMeasure (P.map (fun ω => cdfInv (cdfOf Q X) (U ω))) :=
    Measure.isProbabilityMeasure_map hq.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hq measurableSet_Iic, Measure.map_apply hX measurableSet_Iic]
  change P {ω | cdfInv (cdfOf Q X) (U ω) ≤ t} = Q {ω | X ω ≤ t}
  rw [hc]
  calc
    P {ω | cdfInv (cdf (Q.map X)) (U ω) ≤ t} = P {ω | U ω ≤ cdf (Q.map X) t} := by
      apply measure_congr
      filter_upwards [uniform_ae_interior P U hU] with ω hω
      exact propext (inverse_le_iff _ (tendsto_cdf_atBot _) (tendsto_cdf_atTop _) _ hω t)
    _ = ENNReal.ofReal (cdf (Q.map X) t) := hU.2 _ ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
    _ = Q {ω | X ω ≤ t} := by
      rw [ofReal_cdf, Measure.map_apply hX measurableSet_Iic]; rfl

end RiskOrderStochastic

open RiskOrderStochastic
namespace RiskOrderRealization
lemma realize_pair_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → ℝ) (hU : IsUniformRV P U)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] :
    ∃ Z : Ω → ℝ × ℝ, Measurable Z ∧ P.map Z = μ := by
  let e : (ℝ × ℝ) ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable not_countable not_countable
  have hd := quantile_identDistrib P U hU μ e e.measurable
  let q : Ω → ℝ := fun ω => cdfInv (cdfOf μ e) (U ω)
  have hm : Measurable q := by
    let : IsProbabilityMeasure (μ.map e) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
    rw [show q = (fun ω => cdfInv (ProbabilityTheory.cdf (μ.map e)) (U ω)) by
      simp only [q, cdfOf_eq_cdf_map μ e e.measurable]]
    exact (inverse_measurable _ (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)
      (cdf_nonneg _) (cdf_le_one _)).comp hU.1
  refine ⟨e.symm ∘ q, e.symm.measurable.comp hm, ?_⟩
  rw [← Measure.map_map e.symm.measurable hm, hd.map_eq,
    Measure.map_map e.symm.measurable e.measurable]
  simpa only [e.symm_comp_self, Measure.map_id]


lemma le_condExp_of_borel_tests {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → ℝ)
    (hmA : Measurable A) (hA : Integrable A P) (hB : Integrable B P)
    (htests : ∀ s : Set ℝ, MeasurableSet s →
      (∫ ω in A ⁻¹' s, A ω ∂P) ≤ ∫ ω in A ⁻¹' s, B ω ∂P) :
    A ≤ᵐ[P] P[B|MeasurableSpace.comap A inferInstance] := by
  let m := MeasurableSpace.comap A inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := hmA.comap_le
  have hAm : StronglyMeasurable[m] A := (comap_measurable A).stronglyMeasurable
  have hCm : StronglyMeasurable[m] (P[B|m]) := stronglyMeasurable_condExp
  have htA := hA.trim hm hAm
  have htC := (integrable_condExp (μ := P) (m := m) (f := B)).trim hm hCm
  have ht : A ≤ᵐ[P.trim hm] P[B|m] := by
    apply ae_le_of_forall_setIntegral_le htA htC
    intro s hs _
    rw [← setIntegral_trim hm hAm hs, ← setIntegral_trim hm hCm hs,
      setIntegral_condExp hm hB hs]
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    exact htests t ht
  exact ae_le_of_ae_le_trim ht

lemma realization_preserves_submartingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure (ℝ × ℝ))
    (Z : Ω → ℝ × ℝ) (hmZ : Measurable Z) (hZ : P.map Z = μ)
    (hfst : Integrable Prod.fst μ) (hsnd : Integrable Prod.snd μ)
    (htests : ∀ s : Set ℝ, MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ) :
    (fun ω => (Z ω).1) ≤ᵐ[P]
      P[(fun ω => (Z ω).2)|MeasurableSpace.comap (fun ω => (Z ω).1) inferInstance] := by
  have hf : Integrable (fun ω => (Z ω).1) P := by
    apply (integrable_map_measure (measurable_fst.aestronglyMeasurable) hmZ.aemeasurable).mp
    rwa [hZ]
  have hg : Integrable (fun ω => (Z ω).2) P := by
    apply (integrable_map_measure (measurable_snd.aestronglyMeasurable) hmZ.aemeasurable).mp
    rwa [hZ]
  apply le_condExp_of_borel_tests P _ _ (measurable_fst.comp hmZ) hf hg
  intro s hs
  have he₁ := setIntegral_map (μ := P) (g := Z) (f := Prod.fst)
    (measurable_fst hs) measurable_fst.aestronglyMeasurable hmZ.aemeasurable
  have he₂ := setIntegral_map (μ := P) (g := Z) (f := Prod.snd)
    (measurable_fst hs) measurable_snd.aestronglyMeasurable hmZ.aemeasurable
  rw [hZ] at he₁ he₂
  change (∫ ω in Z ⁻¹' (Prod.fst ⁻¹' s), (Z ω).1 ∂P) ≤
    ∫ ω in Z ⁻¹' (Prod.fst ⁻¹' s), (Z ω).2 ∂P
  rw [← he₁, ← he₂]
  exact htests s hs

lemma pair_law_lifts_to_original {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p)
    (U : Ω → ℝ) (hU : IsUniformRV P U) (X Y : Ω → ℝ)
    (hX : MemLp X p P) (hY : MemLp Y p P)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hfst : μ.map Prod.fst = P.map X) (hsnd : μ.map Prod.snd = P.map Y)
    (htests : ∀ s : Set ℝ, MeasurableSet s →
      (∫ z in Prod.fst ⁻¹' s, z.1 ∂μ) ≤ ∫ z in Prod.fst ⁻¹' s, z.2 ∂μ) :
    ∃ A B : Ω → ℝ, Measurable A ∧ Measurable B ∧ MemLp A p P ∧ MemLp B p P ∧
      (∀ t : ℝ, P {ω | A ω ≤ t} = P {ω | X ω ≤ t}) ∧
      (∀ t : ℝ, P {ω | B ω ≤ t} = P {ω | Y ω ≤ t}) ∧
      A ≤ᵐ[P] P[B|MeasurableSpace.comap A inferInstance] := by
  obtain ⟨Z, hmZ, hZ⟩ := realize_pair_law P U hU μ
  let A : Ω → ℝ := fun ω => (Z ω).1
  let B : Ω → ℝ := fun ω => (Z ω).2
  have hmA : Measurable A := measurable_fst.comp hmZ
  have hmB : Measurable B := measurable_snd.comp hmZ
  have hdA : IdentDistrib A X P P := by
    refine ⟨hmA.aemeasurable, hX.aestronglyMeasurable.aemeasurable, ?_⟩
    change P.map (Prod.fst ∘ Z) = P.map X
    rw [← Measure.map_map measurable_fst hmZ, hZ, hfst]
  have hdB : IdentDistrib B Y P P := by
    refine ⟨hmB.aemeasurable, hY.aestronglyMeasurable.aemeasurable, ?_⟩
    change P.map (Prod.snd ∘ Z) = P.map Y
    rw [← Measure.map_map measurable_snd hmZ, hZ, hsnd]
  have hdf : IdentDistrib Prod.fst X μ P :=
    ⟨measurable_fst.aemeasurable, hX.aestronglyMeasurable.aemeasurable, hfst⟩
  have hds : IdentDistrib Prod.snd Y μ P :=
    ⟨measurable_snd.aemeasurable, hY.aestronglyMeasurable.aemeasurable, hsnd⟩
  refine ⟨A, B, hmA, hmB, hdA.memLp_iff.mpr hX, hdB.memLp_iff.mpr hY,
    fun t => hdA.measure_mem_eq measurableSet_Iic,
    fun t => hdB.measure_mem_eq measurableSet_Iic, ?_⟩
  exact realization_preserves_submartingale P μ Z hmZ hZ
    (hdf.integrable_iff.mpr (hX.integrable hp1)) (hds.integrable_iff.mpr (hY.integrable hp1)) htests

end RiskOrderRealization

open ConvexRiskFn.Order
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hU : ∃ U : Ω → ℝ, IsUniformRV P U) (X₁ X₂ : Ω → ℝ) (h₁ : MemLp X₁ p P) (h₂ : MemLp X₂ p P)
    (h : StochasticOrders.MonotoneConvex.IcxOrder P P X₁ X₂) :
    ∃ Xh₁ Xh₂ : Ω → ℝ, Measurable Xh₁ ∧ Measurable Xh₂ ∧ MemLp Xh₁ p P ∧ MemLp Xh₂ p P ∧
      (∀ t : ℝ, P {ω | Xh₁ ω ≤ t} = P {ω | X₁ ω ≤ t}) ∧
      (∀ t : ℝ, P {ω | Xh₂ ω ≤ t} = P {ω | X₂ ω ≤ t}) ∧
      Xh₁ ≤ᵐ[P] P[Xh₂|MeasurableSpace.comap Xh₁ inferInstance]  := by
  obtain ⟨U, hU⟩ := hU
  obtain ⟨ν, hvf, hvs, ht⟩ := RiskOrderLimit.exists_coupling_law_continuous_tests
    P X₁ X₂ (h₁.integrable hp1) (h₂.integrable hp1) h
  have hdf : ProbabilityTheory.IdentDistrib Prod.fst X₁ (ν : Measure (ℝ × ℝ)) P :=
    ⟨measurable_fst.aemeasurable, h₁.aestronglyMeasurable.aemeasurable, hvf⟩
  have hds : ProbabilityTheory.IdentDistrib Prod.snd X₂ (ν : Measure (ℝ × ℝ)) P :=
    ⟨measurable_snd.aemeasurable, h₂.aestronglyMeasurable.aemeasurable, hvs⟩
  have hf := hdf.integrable_iff.mpr (h₁.integrable hp1)
  have hs := hds.integrable_iff.mpr (h₂.integrable hp1)
  have hb := RiskOrderLimit.borel_test_of_closed_tests (ν : Measure (ℝ × ℝ)) hf hs
    (fun s hclosed => RiskOrderLimit.closed_test_of_continuous_tests (ν : Measure (ℝ × ℝ)) hf hs ht s hclosed)
  exact RiskOrderRealization.pair_law_lifts_to_original P p hp1 U hU X₁ X₂ h₁ h₂
    (ν : Measure (ℝ × ℝ)) hvf hvs hb

#print axioms solution

open MeasureTheory
namespace ConvexRiskFn.Order

/-- Proof of Theorem 5.1, p. 446 (Müller and Stoyan, Corollary 1.5.21; Blackwell; Strassen): if
`X₁ ⪯_icx X₂` in `ℒ_p(Ω, ℱ, P)` and `(Ω, ℱ, P)` carries a uniform random variable, there are
random variables `X̂₁ ∼ X₁`, `X̂₂ ∼ X₂` on the same `Ω` with `X̂₁ ≤ 𝔼[X̂₂ | X̂₁]` a.s. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hU : ∃ U : Ω → ℝ, IsUniformRV P U) (X₁ X₂ : Ω → ℝ) (h₁ : MemLp X₁ p P) (h₂ : MemLp X₂ p P)
    (h : StochasticOrders.MonotoneConvex.IcxOrder P P X₁ X₂) :
    ∃ Xh₁ Xh₂ : Ω → ℝ, Measurable Xh₁ ∧ Measurable Xh₂ ∧ MemLp Xh₁ p P ∧ MemLp Xh₂ p P ∧
      (∀ t : ℝ, P {ω | Xh₁ ω ≤ t} = P {ω | X₁ ω ≤ t}) ∧
      (∀ t : ℝ, P {ω | Xh₂ ω ≤ t} = P {ω | X₂ ω ≤ t}) ∧
      Xh₁ ≤ᵐ[P] P[Xh₂|MeasurableSpace.comap Xh₁ inferInstance] := by
  exact solution P p hp1 hpt hU X₁ X₂ h₁ h₂ h

end ConvexRiskFn.Order

#print axioms solution
