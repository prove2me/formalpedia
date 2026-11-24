-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.norm_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:49.209312+00:00
-- url     : https://prove2.me/submissions/b54bfdc6-86dd-48d8-a07f-a247700a57a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_NormTraceLemmas_trace_formula
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_NormTraceLemmas_norm_chi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.NormTraceLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
variable [NumberField K]
namespace Formalism.IndefR.LatticeTransfer.NormTraceLemmas
theorem _root_.solution (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b))‖ ≤ (finrank K T : ℝ) := by
  classical
  rw [trace_formula, map_mul, norm_mul]
  have hA : ‖σ ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹)‖ =
      (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by
    simp [map_mul, map_inv₀, map_natCast, norm_inv]
  rw [hA]
  have hB : ‖σ (∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b))‖ ≤
      ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) := by
    rw [map_sum]
    refine norm_sum_le_of_le _ fun h₀ _ => ?_
    rw [map_sum]
    refine norm_sum_le_of_le _ fun h _ => ?_
    rw [map_mul, map_mul, norm_mul, norm_mul, norm_chi, norm_chi, one_mul, one_mul]
    exact ((hC K G T τ _).2 σ).2
  have hpos : (0 : ℝ) ≤ (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by positivity
  calc (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ‖_‖ ≤
        (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) :=
        mul_le_mul_of_nonneg_left hB hpos
    _ = (finrank K T : ℝ) := by
        have h0 : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        have h1 : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        field_simp
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
