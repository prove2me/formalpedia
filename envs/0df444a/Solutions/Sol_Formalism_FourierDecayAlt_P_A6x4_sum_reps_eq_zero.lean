-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.sum_reps_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:01.861861+00:00
-- url     : https://prove2.me/submissions/9fa0ed84-0dd4-43f3-90a6-71eddb2e22b2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {L₁ L₂ : AddSubgroup K} {S : Finset K} (hle : L₁ ≤ L₂)
    (hS : IsReps S L₂ L₁) (f : K → ℂ) (hmul : ∀ x ∈ L₂, ∀ y ∈ L₂, f (x + y) = f x * f y)
    (h1 : ∀ l ∈ L₁, f l = 1) {l₀ : K} (hl₀ : l₀ ∈ L₂) (hne : f l₀ ≠ 1) : ∑ σ ∈ S, f σ = 0 := by
  classical
  choose! ρ hρ using fun l hl => (hS.2 l hl).exists
  have huniq : ∀ l ∈ L₂, ∀ y ∈ S, l - y ∈ L₁ → y = ρ l :=
    fun l hl y hy h => (hS.2 l hl).unique ⟨hy, h⟩ (hρ l hl)
  have key : ∀ l ∈ L₂, f (ρ l) = f l := by
    intro l hl
    have h := hρ l hl
    have e : f l = f (ρ l) * f (l - ρ l) := by
      rw [← hmul _ (hS.1 _ h.1) _ (hle h.2)]
      congr 1
      ring
    rw [e, h1 _ h.2, mul_one]
  have hsum : ∑ σ ∈ S, f (σ + l₀) = ∑ σ ∈ S, f σ := by
    refine Finset.sum_nbij' (fun σ => ρ (σ + l₀)) (fun σ => ρ (σ - l₀)) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      exact (hρ _ (L₂.add_mem (hS.1 σ hσ) hl₀)).1
    · intro σ hσ
      exact (hρ _ (L₂.sub_mem (hS.1 σ hσ) hl₀)).1
    · intro σ hσ
      have h := hρ _ (L₂.add_mem (hS.1 σ hσ) hl₀)
      refine (huniq _ (L₂.sub_mem (hS.1 _ h.1) hl₀) σ hσ ?_).symm
      have := L₁.neg_mem h.2
      have e : ρ (σ + l₀) - l₀ - σ = -(σ + l₀ - ρ (σ + l₀)) := by ring
      rw [e]
      exact this
    · intro σ hσ
      have h := hρ _ (L₂.sub_mem (hS.1 σ hσ) hl₀)
      refine (huniq _ (L₂.add_mem (hS.1 _ h.1) hl₀) σ hσ ?_).symm
      have := L₁.neg_mem h.2
      have e : ρ (σ - l₀) + l₀ - σ = -(σ - l₀ - ρ (σ - l₀)) := by ring
      rw [e]
      exact this
    · intro σ hσ
      exact (key _ (L₂.add_mem (hS.1 σ hσ) hl₀)).symm
  have h2 : ∑ σ ∈ S, f (σ + l₀) = (∑ σ ∈ S, f σ) * f l₀ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ hσ => hmul _ (hS.1 σ hσ) _ hl₀
  have h3 : (∑ σ ∈ S, f σ) * (f l₀ - 1) = 0 := by
    rw [mul_sub, ← h2, hsum, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)
end Formalism.FourierDecayAlt.P.A6x4
