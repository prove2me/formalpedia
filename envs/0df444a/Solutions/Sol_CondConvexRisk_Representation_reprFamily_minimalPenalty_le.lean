-- Prove2me | solution 1 for CondConvexRisk.Representation.reprFamily_minimalPenalty_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:06:35.372161+00:00
-- url     : https://prove2.me/submissions/fba7234b-72ce-45a4-b86c-72704713641d

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure
import Definitions.Def_CondConvexRisk_Representation_Representable

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

theorem aux_rfmp_ereal_le (a c : ℝ) (b : ENNReal) (h : ((a - c : ℝ) : EReal) ≤ (b : EReal)) :
    (a : EReal) - (b : EReal) ≤ (c : EReal) := by
  rcases eq_or_ne b ⊤ with hb | hb
  · subst hb
    simp
  · lift b to NNReal using hb
    have h' : a - c ≤ (b : ℝ) := by
      have : ((b : ENNReal) : EReal) = ((b : ℝ) : EReal) := rfl
      rw [this] at h
      exact_mod_cast h
    have : ((b : ENNReal) : EReal) = ((b : ℝ) : EReal) := rfl
    rw [this, ← EReal.coe_sub]
    exact_mod_cast (by linarith : a - (b : ℝ) ≤ c)

end CondConvexRisk.Representation

open CondConvexRisk.Representation
open MeasureTheory Filter Topology

theorem solution {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (ρ : (Ω → ℝ) → Ω → ℝ) (hρ : IsCondConvexRiskMeasure m P ρ)
    (α : PG m P → Ω → ENNReal) (hα : IsMinimalPenalty m P ρ α)
    (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    (∀ Q : PG m P, reprFamily m P α X Q ≤ᵐ[P] fun ω => (ρ X ω : EReal)) ∧
    ∀ W : Ω → EReal, IsEssSup P (reprFamily m P α X) W →
      W ≤ᵐ[P] fun ω => (ρ X ω : EReal) := by
  have h1 : ∀ Q : PG m P, reprFamily m P α X Q ≤ᵐ[P] fun ω => (ρ X ω : EReal) := by
    intro Q
    have hQ := (hα Q).2.1 ⟨X, hX⟩
    filter_upwards [hQ] with ω hω
    simp only [penaltyFamily] at hω
    simp only [reprFamily]
    exact aux_rfmp_ereal_le _ _ _ hω
  refine ⟨h1, ?_⟩
  intro W hW
  apply hW.2.2
  · have hs : StronglyMeasurable[mΩ] (ρ X) := (hρ.stronglyMeasurable X hX).mono hm
    exact (measurable_coe_real_ereal.comp hs.measurable).aemeasurable
  · exact h1
