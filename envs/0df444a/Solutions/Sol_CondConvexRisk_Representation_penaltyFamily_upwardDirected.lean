-- Prove2me | solution 1 for CondConvexRisk.Representation.penaltyFamily_upwardDirected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:56:25.13253+00:00
-- url     : https://prove2.me/submissions/165f9d4e-289f-42b8-9619-68f2300a7f69

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem aux_pfud_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure Q] (hQP : Q ≪ P) (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    Integrable X Q := by
  have h : MemLp X ⊤ Q := by
    refine ⟨hX.1.mono_ac hQP, ?_⟩
    rw [eLpNorm_exponent_top]
    refine lt_of_le_of_lt (eLpNormEssSup_mono_measure X hQP) ?_
    rw [← eLpNorm_exponent_top]
    exact hX.2
  exact h.integrable le_top

theorem aux_pfud_transfer {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P Q : Measure Ω) (hm : m ≤ mΩ) (hQ : ∀ A, MeasurableSet[m] A → Q A = P A)
    (f g : Ω → ℝ) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
    (h : f =ᵐ[Q] g) : f =ᵐ[P] g := by
  have htrim : Q.trim hm = P.trim hm := by
    refine @Measure.ext _ m _ _ (fun s hs => ?_)
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, hQ s hs]
  rw [← hf.ae_eq_trim_iff hm hg] at h ⊢
  rwa [htrim] at h

end CondConvexRisk.Representation

open MeasureTheory Filter Topology CondConvexRisk.Representation

theorem solution {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ) (Q : PG m P) :
    IsUpwardDirected P (penaltyFamily m P ρ Q) := by
  intro X Y
  obtain ⟨hQprob, hQP, hQG⟩ := Q.2
  have := hQprob
  have hBXm : StronglyMeasurable[m] (fun ω => -(Q.1[X.1 | m]) ω - ρ X.1 ω) :=
    (stronglyMeasurable_condExp.neg).sub (hρ.stronglyMeasurable X.1 X.2)
  have hBYm : StronglyMeasurable[m] (fun ω => -(Q.1[Y.1 | m]) ω - ρ Y.1 ω) :=
    (stronglyMeasurable_condExp.neg).sub (hρ.stronglyMeasurable Y.1 Y.2)
  let A : Set Ω := {ω | -(Q.1[Y.1 | m]) ω - ρ Y.1 ω ≤ -(Q.1[X.1 | m]) ω - ρ X.1 ω}
  have hAm : MeasurableSet[m] A := measurableSet_le hBYm.measurable hBXm.measurable
  have hAm' : MeasurableSet A := hm _ hAm
  let Λ : Ω → ℝ := A.indicator (fun _ => (1:ℝ))
  have hΛm : StronglyMeasurable[m] Λ := stronglyMeasurable_const.indicator hAm
  have hΛb : ∀ᵐ ω ∂P, 0 ≤ Λ ω ∧ Λ ω ≤ 1 := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    by_cases h : ω ∈ A <;> simp [Λ, h]
  let Zf : Ω → ℝ := Λ * X.1 + (1 - Λ) * Y.1
  have hZeq : Zf = A.indicator X.1 + Aᶜ.indicator Y.1 := by
    funext ω
    by_cases h : ω ∈ A <;> simp [Zf, Λ, h]
  have hZmem : MemLp Zf ⊤ P := by
    rw [hZeq]; exact (X.2.indicator hAm').add (Y.2.indicator hAm'.compl)
  have hconv : ρ Zf ≤ᵐ[P] Λ * ρ X.1 + (1 - Λ) * ρ Y.1 :=
    hρ.convex X.1 Y.1 Λ X.2 Y.2 hΛm hΛb
  have hXi := aux_pfud_integrable P Q.1 hQP X.1 X.2
  have hYi := aux_pfud_integrable P Q.1 hQP Y.1 Y.2
  have hcondQ : Q.1[Zf | m] =ᵐ[Q.1]
      A.indicator (Q.1[X.1 | m]) + Aᶜ.indicator (Q.1[Y.1 | m]) := by
    rw [hZeq]
    refine (condExp_add (hXi.indicator hAm') (hYi.indicator hAm'.compl) m).trans ?_
    exact (condExp_indicator hXi hAm).add (condExp_indicator hYi hAm.compl)
  have hcondP : Q.1[Zf | m] =ᵐ[P]
      A.indicator (Q.1[X.1 | m]) + Aᶜ.indicator (Q.1[Y.1 | m]) :=
    aux_pfud_transfer m P Q.1 hm hQG _ _ stronglyMeasurable_condExp
      ((stronglyMeasurable_condExp.indicator hAm).add
        (stronglyMeasurable_condExp.indicator hAm.compl)) hcondQ
  have key : ∀ᵐ ω ∂P,
      -(Q.1[X.1 | m] ω) - ρ X.1 ω ≤ -(Q.1[Zf | m] ω) - ρ Zf ω ∧
      -(Q.1[Y.1 | m] ω) - ρ Y.1 ω ≤ -(Q.1[Zf | m] ω) - ρ Zf ω := by
    filter_upwards [hconv, hcondP] with ω h1 h2
    have hA : ω ∈ A ↔ -(Q.1[Y.1 | m] ω) - ρ Y.1 ω ≤ -(Q.1[X.1 | m] ω) - ρ X.1 ω := Iff.rfl
    by_cases hω : ω ∈ A
    · have hΛ1 : Λ ω = 1 := by simp [Λ, hω]
      have hω' : ω ∉ Aᶜ := fun h => h hω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, hΛ1] at h1
      simp only [Pi.add_apply, Set.indicator_of_mem hω, Set.indicator_of_notMem hω'] at h2
      have := hA.1 hω
      constructor <;> linarith
    · have hΛ0 : Λ ω = 0 := by simp [Λ, hω]
      have hω' : ω ∈ Aᶜ := hω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, hΛ0] at h1
      simp only [Pi.add_apply, Set.indicator_of_mem hω', Set.indicator_of_notMem hω] at h2
      have := mt hA.2 hω
      constructor <;> linarith
  refine ⟨⟨Zf, hZmem⟩, ?_, ?_⟩
  · filter_upwards [key] with ω hω
    exact EReal.coe_le_coe_iff.2 hω.1
  · filter_upwards [key] with ω hω
    exact EReal.coe_le_coe_iff.2 hω.2
