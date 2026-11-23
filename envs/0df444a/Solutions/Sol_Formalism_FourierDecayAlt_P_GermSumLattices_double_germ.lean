-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.double_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:49.065571+00:00
-- url     : https://prove2.me/submissions/5957776a-20aa-41f2-906c-ea00ac7b51be

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_finsum_if
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_germSum_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_roots_reindex

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
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (h h' : Point K) (t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K)
    (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hSfin : {x | (cr x : K) ∈ S}.Finite)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hG1 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h m t₁ (cr x)) w' =
      germSum R ψ m γ t₁ (cr x) (fun z => Kp R ψ (addBlock h (m + 1) z) w'))
    (hG2 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h' m t₂ (cr x)) w' =
      germSum R ψ m γ t₂ (cr x) (fun z => Kp R ψ (addBlock h' (m + 1) z) w'))
    (hκ : κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m) :
    uGram R ψ m cr S h h' t₁ t₂ =
      ((modK R ((t₁ : K) * (t₂ : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
      ((((modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
        ((modK R (t₂ : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ)) *
      ∑ ζ ∈ μ, ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ (ζ * κ * z)) *
          Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z))) := by
  unfold uGram
  congr 1
  rw [finsum_if hSfin, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : (cr x : K) ∈ S := by simpa using hx
  rw [hG1 x hx', germSum_eq R ψ m γ hroots, Finset.sum_comm, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : z ^ (m + 1) = (-t₁) ^ m * cr x := by simpa using hz
  rw [hherm (pt2 h' m t₂ (cr x)) (addBlock h (m + 1) z), hG2 x hx', germSum_eq R ψ m γ hroots,
    map_mul, Complex.conj_ofReal, map_sum]
  have hz₀ : (κ * z) ^ (m + 1) = (-t₂) ^ m * cr x := by
    rw [mul_pow, hκ, hz', ← mul_assoc, ← mul_pow]
    congr 2
    rw [mul_neg, mul_assoc, inv_mul_cancel, mul_one]
  rw [roots_reindex m μ hμ hroots _ (κ * z) hz₀, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  rw [map_mul, ← hherm, mul_assoc ζ κ z]
  ring
end Formalism.FourierDecayAlt.P.GermSumLattices
