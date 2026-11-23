-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.abstract_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:45.397424+00:00
-- url     : https://prove2.me/submissions/2ab57158-6e1a-48a0-a1e7-a682f6cea6fa

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_inner_sum_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_normSq_mean
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_sum_sub_prod

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.MeanNormSquaredBound
theorem _root_.solution (AB : AvgBound) {X Y : Type} (F : Finset X) (a : X → ℂ) (A B : Finset Y)
    (u : X → Y × Y → E) (T : E →ₗ[ℂ] E) (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (e₁ e₂ : Y → ℂ)
    (he₁ : ∀ ρ ∈ A, ‖e₁ ρ‖ = 1)
    (horth : ∀ h ∈ F, ∀ h' ∈ F, ∀ ρ ∈ A, ∀ ρ' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, ρ ≠ ρ' →
      inner ℂ (u h (ρ, b)) (u h' (ρ', b')) = 0) :
    ∃ r₁ r₂ : ℝ, r₁ ≤ r₂ ∧
      (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((((A.card : ℂ) * (B.card : ℂ))⁻¹) ^ 2 * ∑ p ∈ A ×ˢ B, ∑ p' ∈ A ×ˢ B,
          (e₁ p.1 * e₂ p.2) * conj (e₁ p'.1 * e₂ p'.2) * inner ℂ (T (u h' p')) (T (u h p))) ∧
      (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((A.card : ℂ)⁻¹ * ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b)))) := by
  set w : Y × Y → E := fun p => ∑ h ∈ F, a h • u h p with hw
  have key := AB E ↥A ↥B (fun p => w (p.1.1, p.2.1)) T (fun ρ => e₁ ρ.1) (fun b => e₂ b.1) hT
    (fun ρ => he₁ ρ.1 ρ.2) (by
      intro ρ ρ' b b' hne
      have hne' : ρ.1 ≠ ρ'.1 := fun h => hne (Subtype.ext h)
      simp only [hw]
      rw [inner_sum_sum]
      refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
      rw [horth h' hh' h hh ρ.1 ρ.2 ρ'.1 ρ'.2 b.1 b.2 b'.1 b'.2 hne', mul_zero])
  simp only [Fintype.card_coe] at key
  have e1 : (∑ p : ↥A × ↥B, (e₁ p.1.1 * e₂ p.2.1) • w (p.1.1, p.2.1)) =
      ∑ p ∈ A ×ˢ B, (e₁ p.1 * e₂ p.2) • w p :=
    sum_sub_prod A B (fun p => (e₁ p.1 * e₂ p.2) • w p)
  have e2 : (∑ ρ : ↥A, ‖(B.card : ℂ)⁻¹ • ∑ b : ↥B, e₂ b.1 • w (ρ.1, b.1)‖ ^ 2) =
      ∑ ρ ∈ A, ‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort A]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Finset.sum_coe_sort B]
  rw [e1, e2] at key
  refine ⟨_, _, key, ?_, ?_⟩
  · exact normSq_mean T _ (by simp) (A ×ˢ B) (fun p => e₁ p.1 * e₂ p.2) F a u
  · have h3 : ∀ ρ, ((‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 : ℝ) : ℂ) =
        ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') * (((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b))) := fun ρ =>
      normSq_mean LinearMap.id _ (by simp) B e₂ F a (fun h b => u h (ρ, b))
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sum]
    simp only [h3, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
