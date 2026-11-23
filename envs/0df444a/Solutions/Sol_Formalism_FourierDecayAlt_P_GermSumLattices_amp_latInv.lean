-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.amp_latInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:28.947202+00:00
-- url     : https://prove2.me/submissions/aeee3139-7265-4c68-b72f-18e2162d189a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_amp_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (h h' : Point K) (t₁ ζ : Kˣ) (Om Esq : Set K) (Λ' Λ₁ Λ₂ : AddSubgroup K)
    (hγ2 : ∀ a b : Kˣ, γ (a * b ^ 2) = γ a)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hOmU : ∀ z ∈ Om, IsUnit z)
    (hML : ∀ z ∈ Om, ∀ l ∈ Λ', IsUnit (z + l) ∧ modK R (z + l) = modK R z ∧
      l * Ring.inverse z ∈ Esq)
    (hsq : ∀ a : Kˣ, (a : K) - 1 ∈ Esq → ∃ b : Kˣ, a = b ^ 2)
    (hLC1 : ∀ z z' : Kˣ, (z : K) ∈ Om → (z' : K) - (z : K) ∈ Λ₁ → ∀ w' : Point K,
      Kp R ψ (addBlock h (m + 1) z') w' = Kp R ψ (addBlock h (m + 1) z) w')
    (hLC2 : ∀ z z' : Kˣ, (z : K) ∈ Om → (z' : K) - (z : K) ∈ Λ₂ → ∀ w' : Point K,
      Kp R ψ (addBlock h' (m + 1) z') w' = Kp R ψ (addBlock h' (m + 1) z) w')
    (h1 : ∀ l ∈ Λ', l ∈ Λ₁) (h2 : ∀ l ∈ Λ', (ζ : K) * l ∈ Λ₂)
    (hζ : ∀ z ∈ Om, (ζ : K) * z ∈ Om) :
    LatInv Λ' Om (amp R ψ m γ h h' t₁ ζ) := by
  intro z hz l hl
  obtain ⟨u, rfl⟩ := hOmU z hz
  obtain ⟨hu', hmod, hE⟩ := hML _ hz l hl
  obtain ⟨u', hu'⟩ := hu'
  rw [← hu', amp_unit, amp_unit, hu', hmod]
  rw [Ring.inverse_unit] at hE
  obtain ⟨b, hb⟩ := hsq (u' * u⁻¹) (by
    rw [Units.val_mul, hu', add_mul, Units.mul_inv, add_sub_cancel_left]
    exact hE)
  have hub : u' = u * b ^ 2 := by rw [← hb]; simp
  have e1 : γ (u' * t₁) = γ (u * t₁) := by
    rw [hub, mul_right_comm, hγ2]
  have e2 : γ (ζ * u' * t₁) = γ (ζ * u * t₁) := by
    rw [hub, ← mul_assoc, mul_right_comm, hγ2]
  have e3 : Kp R ψ (addBlock h (m + 1) u') (addBlock h' (m + 1) (ζ * u')) =
      Kp R ψ (addBlock h (m + 1) u) (addBlock h' (m + 1) (ζ * u)) := by
    rw [hLC1 u u' hz (by rw [hu', add_sub_cancel_left]; exact h1 l hl), hherm,
      hLC2 (ζ * u) (ζ * u') (by rw [Units.val_mul]; exact hζ _ hz) (by
        rw [Units.val_mul, Units.val_mul, hu', mul_add, add_sub_cancel_left]
        exact h2 l hl), ← hherm]
  rw [e1, e2, e3]
end Formalism.FourierDecayAlt.P.GermSumLattices
