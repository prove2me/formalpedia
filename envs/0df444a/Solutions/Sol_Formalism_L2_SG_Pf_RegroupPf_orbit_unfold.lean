-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RegroupPf.orbit_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:21.239912+00:00
-- url     : https://prove2.me/submissions/2df76f30-53e0-4671-981c-0f0239d018d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RegroupPfUnfold
import Theorems.Thm_Formalism_L2_SG_Pf_RegroupPf_isFund_of_exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RegroupPf
variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
namespace Formalism.L2.SG.Pf.RegroupPf
theorem _root_.solution (μ : Measure H) [μ.IsMulLeftInvariant]
    (N : Subgroup H) [Countable N] {C : Type*} [Countable C] (act : N → C → C) (h1 : ∀ c, act 1 c = c)
    (hmul : ∀ n m c, act (n * m) c = act n (act m c))
    (F : C → H → ℂ) (hFm : ∀ c, Measurable (F c)) (hFeq : ∀ (n : N) c y, F (act n c) y = F c ((n : H)⁻¹ * y))
    (Ω : Set H) (hΩm : MeasurableSet Ω) (hΩc : ∀ x, ∃ n : N, (n : H) * x ∈ Ω)
    (hΩu : ∀ x ∈ Ω, ∀ n : N, (n : H) * x ∈ Ω → n = 1)
    {J : Type*} (r : J → C) (hcov : ∀ c, ∃ j n, act n (r j) = c) (huniq : ∀ j j' n, act n (r j) = r j' → j = j')
    (ΩJ : J → Set H) (hJm : ∀ j, MeasurableSet (ΩJ j))
    (hJc : ∀ j x, ∃ n : N, act n (r j) = r j ∧ (n : H) * x ∈ ΩJ j)
    (hJu : ∀ j, ∀ x ∈ ΩJ j, ∀ n : N, act n (r j) = r j → (n : H) * x ∈ ΩJ j → n = 1)
    (hint : ∫⁻ y in Ω, ∑' c, ‖F c y‖ₑ ∂μ < ⊤) :
    IntegrableOn (fun y => ∑' c, F c y) Ω μ ∧
      ∫ y in Ω, ∑' c, F c y ∂μ = ∑' j, ∫ y in ΩJ j, F (r j) y ∂μ := by
  classical
  have hsm : ∀ (n : N) (y : H), n⁻¹ • y = (n : H)⁻¹ * y := fun n y => by
    first | rfl | simp [Subgroup.smul_def]
  have hFeq' : ∀ (n : N) (j : J) (y : H), F (act n (r j)) y = F (r j) (n⁻¹ • y) := by
    intro n j y; rw [hFeq, hsm]
  have hrinj : Function.Injective r := fun j j' h => huniq j j' 1 (by rw [h1, h])
  haveI : Countable J := hrinj.countable
  haveI : MeasurableConstSMul N H := by
    first
      | infer_instance
      | exact ⟨fun n => measurable_const_mul (n : H)⟩
  haveI : SMulInvariantMeasure N H μ := by
    first
      | infer_instance
      | exact ⟨fun n ⦃s⦄ _ => measure_preimage_mul μ (n : H) s⟩

  have hΩ : IsFundamentalDomain N Ω μ := by
    refine isFund_of_exact μ N Ω hΩm (fun x => ?_) (fun x hx g hg hgx => ?_)
    · obtain ⟨n, hn⟩ := hΩc x
      exact ⟨n, n.2, hn⟩
    · have := hΩu x hx ⟨g, hg⟩ hgx
      simpa using congrArg Subtype.val this

  have hbij : ∀ y : H, Function.Bijective
      (fun p : ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)) =>
        act (p : J × N).2 (r (p : J × N).1)) := by
    intro y
    constructor
    · rintro ⟨⟨j, n⟩, hy⟩ ⟨⟨j', n'⟩, hy'⟩ heq
      have hy1 : n⁻¹ • y ∈ ΩJ j := hy
      have hy2 : n'⁻¹ • y ∈ ΩJ j' := hy'
      have heq' : act n (r j) = act n' (r j') := heq
      have e1 : act (n'⁻¹ * n) (r j) = r j' := by
        rw [hmul, heq', ← hmul, inv_mul_cancel, h1]
      obtain rfl : j = j' := huniq j j' _ e1
      have e2 : n'⁻¹ * n = 1 := by
        refine hJu j _ hy1 _ e1 ?_
        have hh : ((n'⁻¹ * n : N) : H) * (n⁻¹ • y) = n'⁻¹ • y := by
          simp only [hsm]
          first | simp [mul_assoc] | group
        rw [hh]
        exact hy2
      obtain rfl : n = n' := (inv_mul_eq_one.mp e2).symm
      rfl
    · intro c
      obtain ⟨j, n0, hc⟩ := hcov c
      obtain ⟨s, hs1, hs2⟩ := hJc j (n0⁻¹ • y)
      have hmem : (n0 * s⁻¹)⁻¹ • y ∈ ΩJ j := by
        have hh : (n0 * s⁻¹)⁻¹ • y = (s : H) * (n0⁻¹ • y) := by
          simp only [hsm]
          first | simp [mul_assoc] | group
        rw [hh]
        exact hs2
      refine ⟨⟨(j, n0 * s⁻¹), hmem⟩, ?_⟩
      show act (n0 * s⁻¹) (r j) = c
      have hsi : act s⁻¹ (r j) = r j := by
        calc act s⁻¹ (r j) = act s⁻¹ (act s (r j)) := by rw [hs1]
          _ = r j := by rw [← hmul, inv_mul_cancel, h1]
      rw [hmul, hsi, hc]
  have key : ∀ (y : H) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (G : C → M),
      ∑' p : J × N, ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)).indicator
        (fun p => G (act p.2 (r p.1))) p = ∑' c, G c := by
    intro y M _ _ G
    rw [← tsum_subtype]
    exact (Equiv.ofBijective _ (hbij y)).tsum_eq G
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : J × N → H → ℂ,
      Ψ = fun p y => (ΩJ p.1).indicator (F (r p.1)) (p.2⁻¹ • y) := ⟨_, rfl⟩
  have hΨ : ∀ y p, Ψ p y = ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)).indicator
      (fun p => F (act p.2 (r p.1)) y) p := by
    intro y p
    subst hΨdef
    by_cases h : p.2⁻¹ • y ∈ ΩJ p.1
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte, hFeq']
        | simp [Set.indicator_apply, h, hFeq']
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte]
        | simp [Set.indicator_apply, h]
  have hΨe : ∀ y p, ‖Ψ p y‖ₑ = ({p : J × N | p.2⁻¹ • y ∈ ΩJ p.1} : Set (J × N)).indicator
      (fun p => ‖F (act p.2 (r p.1)) y‖ₑ) p := by
    intro y p
    rw [hΨ y p]
    by_cases h : p.2⁻¹ • y ∈ ΩJ p.1
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte]
        | simp [Set.indicator_apply, h]
    · first
        | simp only [Set.indicator_apply, Set.mem_setOf_eq, h, ↓reduceIte, enorm_zero]
        | simp [Set.indicator_apply, h]
  have hΨm : ∀ p, Measurable (Ψ p) := by
    intro p
    subst hΨdef
    simp only [hsm]
    exact ((hFm _).indicator (hJm _)).comp (measurable_const_mul _)
  have sumC : ∀ y, ∑' p, Ψ p y = ∑' c, F c y := fun y =>
    (tsum_congr (hΨ y)).trans (key y (fun c => F c y))
  have sumE : ∀ y, ∑' p, ‖Ψ p y‖ₑ = ∑' c, ‖F c y‖ₑ := fun y =>
    (tsum_congr (hΨe y)).trans (key y (fun c => ‖F c y‖ₑ))
  have hT : ∑' p : J × N, ∫⁻ x in Ω, ‖Ψ p x‖ₑ ∂μ = ∫⁻ x in Ω, ∑' c, ‖F c x‖ₑ ∂μ := by
    rw [← lintegral_tsum (fun p => (hΨm p).enorm.aemeasurable)]
    exact lintegral_congr (fun x => sumE x)
  have hTfin : ∑' p : J × N, ∫⁻ x in Ω, ‖Ψ p x‖ₑ ∂μ ≠ ⊤ := by
    rw [hT]
    exact hint.ne

  have hIJ : ∀ j, ∫ y in ΩJ j, F (r j) y ∂μ = ∑' n : N, ∫ y in Ω, Ψ (j, n) y ∂μ := by
    intro j
    have hrow : ∫⁻ x, ‖(ΩJ j).indicator (F (r j)) x‖ₑ ∂μ
        = ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j, n) x‖ₑ ∂μ := by
      refine (hΩ.lintegral_eq_tsum' _).trans ?_
      subst hΨdef
      rfl
    have hlt : ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j, n) x‖ₑ ∂μ < ⊤ := by
      refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hTfin)
      calc ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j, n) x‖ₑ ∂μ
          ≤ ∑' j' : J, ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j', n) x‖ₑ ∂μ :=
            ENNReal.le_tsum (f := fun j' => ∑' n : N, ∫⁻ x in Ω, ‖Ψ (j', n) x‖ₑ ∂μ) j
        _ = ∑' p : J × N, ∫⁻ x in Ω, ‖Ψ p x‖ₑ ∂μ :=
            (ENNReal.tsum_prod (f := fun a b => ∫⁻ x in Ω, ‖Ψ (a, b) x‖ₑ ∂μ)).symm
    have hfi : Integrable ((ΩJ j).indicator (F (r j))) μ := by
      refine ⟨((hFm (r j)).indicator (hJm j)).aestronglyMeasurable, ?_⟩
      first
        | (show ∫⁻ x, ‖(ΩJ j).indicator (F (r j)) x‖ₑ ∂μ < ⊤
           rw [hrow]
           exact hlt)
        | (rw [hasFiniteIntegral_iff_enorm, hrow]
           exact hlt)
    calc ∫ y in ΩJ j, F (r j) y ∂μ = ∫ x, (ΩJ j).indicator (F (r j)) x ∂μ :=
          (integral_indicator (hJm j)).symm
      _ = ∑' n : N, ∫ x in Ω, (ΩJ j).indicator (F (r j)) (n⁻¹ • x) ∂μ :=
          hΩ.integral_eq_tsum' _ hfi
      _ = ∑' n : N, ∫ y in Ω, Ψ (j, n) y ∂μ := by
          subst hΨdef
          rfl
  have hmain : ∫ y in Ω, ∑' c, F c y ∂μ = ∑' p : J × N, ∫ y in Ω, Ψ p y ∂μ := by
    rw [← integral_tsum (fun p => (hΨm p).aestronglyMeasurable) hTfin]
    first
      | simp only [sumC]
      | exact integral_congr_ae (Filter.Eventually.of_forall fun y => (sumC y).symm)
  have hsplit : ∑' p : J × N, ∫ y in Ω, Ψ p y ∂μ
      = ∑' j, ∑' n : N, ∫ y in Ω, Ψ (j, n) y ∂μ := by
    have hasum : Summable fun p : J × N => ∫ y in Ω, Ψ p y ∂μ := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
        (ENNReal.summable_toReal hTfin))
      have h0 := norm_integral_le_lintegral_norm (μ := μ.restrict Ω) (Ψ p)
      first
        | simpa only [ofReal_norm_eq_enorm] using h0
        | simpa using h0
        | exact h0
    exact ((hasum.hasSum.prod_fiberwise fun j => (hasum.prod_factor j).hasSum).tsum_eq).symm
  refine ⟨?_, ?_⟩
  · have hEm : Measurable fun y => ∑' c, ‖F c y‖ₑ :=
      Measurable.ennreal_tsum fun c => (hFm c).enorm
    have hfin_ae : ∀ᵐ y ∂(μ.restrict Ω), ∑' c, ‖F c y‖ₑ < ⊤ := ae_lt_top hEm hint.ne
    have hsN : ∀ y, ∑' c, ‖F c y‖ₑ < ⊤ → Summable fun c => ‖F c y‖ := by
      intro y hy
      have h0 := ENNReal.summable_toReal hy.ne
      first
        | simpa only [toReal_enorm] using h0
        | simpa using h0
    have hgint : Integrable (fun y => (∑' c, ‖F c y‖ₑ).toReal) (μ.restrict Ω) :=
      integrable_toReal_of_lintegral_ne_top hEm.aemeasurable hint.ne
    have hbound : ∀ᵐ y ∂(μ.restrict Ω), ‖∑' c, F c y‖ ≤ (∑' c, ‖F c y‖ₑ).toReal := by
      filter_upwards [hfin_ae] with y hy
      rw [ENNReal.tsum_toReal_eq (fun c => by first | exact enorm_ne_top | simp)]
      simp only [toReal_enorm]
      exact norm_tsum_le_tsum_norm (hsN y hy)
    have hgm : AEStronglyMeasurable (fun y => ∑' c, F c y) (μ.restrict Ω) := by
      haveI : Encodable C := Encodable.ofCountable C
      have hlim : ∀ᵐ y ∂(μ.restrict Ω), Filter.Tendsto (fun s : Finset C => ∑ c ∈ s, F c y)
          Filter.atTop (nhds (∑' c, F c y)) := by
        filter_upwards [hfin_ae] with y hy
        exact (Summable.of_norm (hsN y hy)).hasSum
      have hfs : ∀ s : Finset C, Measurable fun y => ∑ c ∈ s, F c y := fun s => by
        first
          | exact Finset.measurable_sum s (fun c _ => hFm c)
          | fun_prop
      first
        | exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
            (fun s => (hfs s).aestronglyMeasurable) hlim
        | exact (aemeasurable_of_tendsto_metrizable_ae Filter.atTop
            (fun s => (hfs s).aemeasurable) hlim).aestronglyMeasurable
    exact Integrable.mono' hgint hgm hbound
  · rw [hmain, hsplit]
    exact tsum_congr fun j => (hIJ j).symm
end Formalism.L2.SG.Pf.RegroupPf
