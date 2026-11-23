-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.comb_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:36.909566+00:00
-- url     : https://prove2.me/submissions/eb96dd42-ea49-41a3-9b82-abf9b43a3f0a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
open Classical
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {A₁ C₁ A₂ C₂ Θ : Type} [Fintype A₁] [Fintype C₁] [Fintype A₂] [Fintype C₂]
    [Fintype Θ] (P₁ : A₁ → C₁ → Prop) (P₂ : A₂ → C₂ → Prop) (ta : Θ → A₁ → A₂) (tc : Θ → C₁ → C₂)
    (Q : Θ → A₁ → C₁ → A₂ → C₂ → Prop)
    (hQ : ∀ θ a₁ c₁ a₂ c₂, Q θ a₁ c₁ a₂ c₂ ↔ a₂ = ta θ a₁ ∧ c₂ = tc θ c₁)
    (hP : ∀ θ a c, P₂ (ta θ a) (tc θ c) ↔ P₁ a c) (f₁ : A₁ → C₁ → ℂ) (f₂ : A₂ → C₂ → ℂ) :
    ∑ s : (A₁ × C₁) × (A₂ × C₂), (if P₁ s.1.1 s.1.2 ∧ P₂ s.2.1 s.2.2 then
        (Nat.card {θ // Q θ s.1.1 s.1.2 s.2.1 s.2.2} : ℂ) else 0) * f₁ s.1.1 s.1.2 * f₂ s.2.1 s.2.2 =
      ∑ θ, ∑ a, ∑ c, if P₁ a c then f₁ a c * f₂ (ta θ a) (tc θ c) else 0 := by
  have key : ∀ s : (A₁ × C₁) × (A₂ × C₂), (if P₁ s.1.1 s.1.2 ∧ P₂ s.2.1 s.2.2 then
        (Nat.card {θ // Q θ s.1.1 s.1.2 s.2.1 s.2.2} : ℂ) else 0) * f₁ s.1.1 s.1.2 * f₂ s.2.1 s.2.2 =
      ∑ θ, if s.2 = (ta θ s.1.1, tc θ s.1.2) then
        (if P₁ s.1.1 s.1.2 then f₁ s.1.1 s.1.2 * f₂ (ta θ s.1.1) (tc θ s.1.2) else 0) else 0 := by
    rintro ⟨⟨a₁, c₁⟩, ⟨a₂, c₂⟩⟩
    simp only
    have h1 : ∀ θ, (if (a₂, c₂) = (ta θ a₁, tc θ c₁) then
        (if P₁ a₁ c₁ then f₁ a₁ c₁ * f₂ (ta θ a₁) (tc θ c₁) else 0) else 0) =
        (if P₁ a₁ c₁ ∧ P₂ a₂ c₂ then ((if Q θ a₁ c₁ a₂ c₂ then 1 else 0 : ℕ) : ℂ) else 0) *
          f₁ a₁ c₁ * f₂ a₂ c₂ := by
      intro θ
      by_cases h : a₂ = ta θ a₁ ∧ c₂ = tc θ c₁
      · obtain ⟨rfl, rfl⟩ := h
        have hq : Q θ a₁ c₁ (ta θ a₁) (tc θ c₁) := (hQ _ _ _ _ _).2 ⟨rfl, rfl⟩
        by_cases hp : P₁ a₁ c₁
        · simp [hq, hP, hp]
        · simp [hp]
      · have hq : ¬ Q θ a₁ c₁ a₂ c₂ := fun hq => h ((hQ _ _ _ _ _).1 hq)
        have hne : ¬ (a₂, c₂) = (ta θ a₁, tc θ c₁) := fun he => h (Prod.ext_iff.1 he)
        simp [hq, hne]
    rw [Finset.sum_congr rfl fun θ _ => h1 θ, ← Finset.sum_mul, ← Finset.sum_mul,
      Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    congr 2
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun s _ => key s, Fintype.sum_prod_type]
  simp only
  have h2 : ∀ x : A₁ × C₁, (∑ y : A₂ × C₂, ∑ θ, if y = (ta θ x.1, tc θ x.2) then
        (if P₁ x.1 x.2 then f₁ x.1 x.2 * f₂ (ta θ x.1) (tc θ x.2) else 0) else 0) =
      ∑ θ, if P₁ x.1 x.2 then f₁ x.1 x.2 * f₂ (ta θ x.1) (tc θ x.2) else 0 := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Fintype.sum_prod_type]
end Formalism.FourierDecayAlt.P.A5x8
