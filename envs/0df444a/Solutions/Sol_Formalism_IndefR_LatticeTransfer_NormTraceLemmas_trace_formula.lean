-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.trace_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:16.051334+00:00
-- url     : https://prove2.me/submissions/593fd707-915a-47ee-be21-431299363f9f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing

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
open Classical
namespace Formalism.IndefR.LatticeTransfer.NormTraceLemmas
theorem _root_.solution (τ : Representation K G T) (H₀ H : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (χ : H →* (𝓞 K)ˣ) (a b : G) :
    LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) =
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹) *
        ∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b) := by
  simp only [← Module.End.mul_eq_comp, epP, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, map_sum, smul_eq_mul, ← map_mul, charOf, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h₀ _ => Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (algebraMap (𝓞 K) K)]
  ring
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
