-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.thx_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.16733+00:00
-- url     : https://prove2.me/submissions/c03631fe-03e9-4781-9d83-4114f130b639

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psd_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psd_mix
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psd_comap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (hG : ∀ F' : Finset (Point K × Kˣ), (∀ p ∈ F', ∀ p' ∈ F', p.1.1.sum = p'.1.1.sum) →
      ∀ (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ), IsCr R cr →
      IsPSD F' (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2))
    (m n₀ : ℕ) (F : Finset (Point K)) (A B : Finset K) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hF : ∀ h ∈ F, h.1.sum = n₀) (hcr : IsCr R cr) (z : K) :
    IsPSD F (thx R ψ m cr A B τ z) := by
  classical
  have h1 : ∀ ρ : K, IsPSD F (fun h h' => ∑ b ∈ B, ∑ b' ∈ B,
      ψ (-(z * b)) * conj (ψ (-(z * b'))) *
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b'))) := by
    intro ρ
    refine psd_mix F B (fun b => ψ (-(z * b)))
      (fun q q' => uGram R ψ m cr Set.univ q.1 q'.1 (τ (ρ + q.2)) (τ (ρ + q'.2))) ?_
    refine psd_comap (fun p p' : Point K × Kˣ => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2)
      (fun q : Point K × K => (q.1, τ (ρ + q.2))) (F ×ˢ B) (hG _ ?_ m cr hcr)
    intro p hp p' hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hp'
    exact (hF _ (Finset.mem_product.mp hq).1).trans (hF _ (Finset.mem_product.mp hq').1).symm
  have h2 := psd_smul F _ ((A.card : ℝ)⁻¹) (by positivity)
    (psd_sum F A _ fun ρ _ => psd_smul F _ (((B.card : ℝ)⁻¹) ^ 2) (by positivity) (h1 ρ))
  have e : thx R ψ m cr A B τ z = fun h h' => (((A.card : ℝ)⁻¹ : ℝ) : ℂ) * ∑ ρ ∈ A,
      ((((B.card : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) * ∑ b ∈ B, ∑ b' ∈ B,
        ψ (-(z * b)) * conj (ψ (-(z * b'))) *
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) := by
    funext h h'
    unfold thx
    push_cast
    rfl
  rw [e]
  exact h2
end Formalism.FourierDecayAlt.P.AveragedKernelSums
