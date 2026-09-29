-- Prove2me | solution 1 for CondConvexRisk.Representation.minimalPenalty_minimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:25:02.64635+00:00
-- url     : https://prove2.me/submissions/74b9b58a-70fc-487e-b08f-e98e6c0ae0dc

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- `L∞(P)` transfers to `L∞(Q)` for `Q ≪ P`. -/
theorem aux_mpm_memLp_top {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}
    (hQP : Q ≪ P) {X : Ω → ℝ} (hX : MemLp X ⊤ P) : MemLp X ⊤ Q := by
  refine ⟨hX.1.mono_ac hQP, ?_⟩
  rw [eLpNorm_exponent_top]
  exact lt_of_le_of_lt (eLpNormEssSup_mono_measure X hQP)
    (by rw [← eLpNorm_exponent_top]; exact hX.2)

/-- Pointwise `EReal` inequality used for the first part. -/
theorem aux_mpm_ereal (r s : ℝ) (a : ENNReal)
    (h : ((r : ℝ) : EReal) - (a : EReal) ≤ (s : EReal)) :
    (((r - s : ℝ)) : EReal) ≤ (a : EReal) := by
  induction a with
  | top => simp
  | coe a =>
    have : ((a : ENNReal) : EReal) = ((a : ℝ) : EReal) := rfl
    rw [this] at h ⊢
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]
    linarith

end CondConvexRisk.Representation

open CondConvexRisk.Representation

open MeasureTheory Filter Topology

theorem solution {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (αstar : PG m P → Ω → ENNReal) (hstar : IsMinimalPenalty m P ρ αstar) :
    (∀ α : PG m P → Ω → ENNReal, IsPenaltyFor m P ρ α →
      ∀ Q : PG m P, αstar Q ≤ᵐ[P] α Q) ∧
    ∀ Q : PG m P,
      IsEssSup P
        (fun X : {X : Ω → ℝ // MemLp X ⊤ P ∧ ρ X ≤ᵐ[P] 0} =>
          fun ω => ((-(Q.1[X.1 | m]) ω : ℝ) : EReal))
        (fun ω => (αstar Q ω : EReal)) := by
  refine ⟨?_, ?_⟩
  · intro α hα Q
    have hW : AEMeasurable (fun ω => (α Q ω : EReal)) P :=
      (measurable_coe_ennreal_ereal.comp ((hα.1 Q).mono hm le_rfl)).aemeasurable
    have key := (hstar Q).2.2 _ hW (by
      intro X
      have h := (hα.2 X.1 X.2).2.1 Q
      filter_upwards [h] with ω hω
      simp only [reprFamily] at hω
      simp only [penaltyFamily]
      exact aux_mpm_ereal _ _ _ hω)
    filter_upwards [key] with ω hω
    exact_mod_cast hω
  · intro Q
    refine ⟨(hstar Q).1, ?_, ?_⟩
    · intro X
      filter_upwards [(hstar Q).2.1 ⟨X.1, X.2.1⟩, X.2.2] with ω h1 h2
      simp only [penaltyFamily] at h1
      refine le_trans ?_ h1
      rw [EReal.coe_le_coe_iff]
      simp only [Pi.zero_apply] at h2
      linarith
    · intro W hW hWle
      apply (hstar Q).2.2 W hW
      intro X
      have : IsProbabilityMeasure Q.1 := Q.2.1
      have hQP : Q.1 ≪ P := Q.2.2.1
      have hQm : ∀ A, MeasurableSet[m] A → Q.1 A = P A := Q.2.2.2
      have hRX : MemLp (ρ X.1) ⊤ P := hρ.memLp X.1 X.2
      have hRXm : StronglyMeasurable[m] (ρ X.1) := hρ.stronglyMeasurable X.1 X.2
      have hX' : MemLp (X.1 + ρ X.1) ⊤ P := X.2.add hRX
      have hρX' : ρ (X.1 + ρ X.1) ≤ᵐ[P] 0 := by
        filter_upwards [hρ.translation X.1 (ρ X.1) X.2 hRX hRXm] with ω hω
        rw [hω]
        simp
      have h1 := hWle ⟨X.1 + ρ X.1, hX', hρX'⟩
      -- conditional expectation identity, Q-a.e.
      have hXQ : Integrable X.1 Q.1 :=
        (aux_mpm_memLp_top hQP X.2).integrable le_top
      have hRQ : Integrable (ρ X.1) Q.1 :=
        (aux_mpm_memLp_top hQP hRX).integrable le_top
      have hce : Q.1[X.1 + ρ X.1 | m] =ᵐ[Q.1] Q.1[X.1 | m] + ρ X.1 := by
        filter_upwards [condExp_add hXQ hRQ m] with ω hω
        rw [hω, condExp_of_stronglyMeasurable hm hRXm hRQ]
      -- transfer to P-a.e. via measurability w.r.t. m
      have hceP : Q.1[X.1 + ρ X.1 | m] =ᵐ[P] Q.1[X.1 | m] + ρ X.1 := by
        have hmeas : MeasurableSet[m] {ω | Q.1[X.1 + ρ X.1 | m] ω = (Q.1[X.1 | m] + ρ X.1) ω} :=
          StronglyMeasurable.measurableSet_eq_fun stronglyMeasurable_condExp
            (stronglyMeasurable_condExp.add hRXm)
        have hQ0 : Q.1 {ω | Q.1[X.1 + ρ X.1 | m] ω = (Q.1[X.1 | m] + ρ X.1) ω}ᶜ = 0 :=
          ae_iff.mp hce
        have hP0 : P {ω | Q.1[X.1 + ρ X.1 | m] ω = (Q.1[X.1 | m] + ρ X.1) ω}ᶜ = 0 := by
          rw [← hQm _ hmeas.compl]; exact hQ0
        exact mem_ae_iff.mpr hP0
      filter_upwards [h1, hceP] with ω hω1 hω2
      simp only [penaltyFamily]
      rw [hω2] at hω1
      simp only [Pi.add_apply] at hω1 ⊢
      convert hω1 using 2
      ring
