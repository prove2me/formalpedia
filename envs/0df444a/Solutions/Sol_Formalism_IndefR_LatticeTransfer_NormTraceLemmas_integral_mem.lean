-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.NormTraceLemmas.integral_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.406035+00:00
-- url     : https://prove2.me/submissions/913b99a3-8afc-4bb6-8680-721e7ebebc36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_NormTraceLemmas_trace_formula

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
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) :
    (Fintype.card G : K) ^ 2 * LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) ∈
      integralClosure ℤ K := by
  classical
  rw [trace_formula]
  have hG0 : (Fintype.card G : K) = (Nat.card H₀ : K) * (H₀.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hG1 : (Fintype.card G : K) = (Nat.card H : K) * (H.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hsq : (Fintype.card G : K) ^ 2 =
      ((Nat.card H₀ : K) * (H₀.index : K)) * ((Nat.card H : K) * (H.index : K)) := by
    rw [sq]
    nth_rw 1 [hG0]
    rw [hG1]
  have h0 : (Nat.card H₀ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsq, show ∀ x : K, (Nat.card H₀ : K) * (H₀.index : K) * ((Nat.card H : K) * (H.index : K)) *
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹ * x) = (H₀.index : K) * (H.index : K) * x from
      fun x => by field_simp]
  refine mul_mem (mul_mem (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
    (Subalgebra.sum_mem _ fun h₀ _ => Subalgebra.sum_mem _ fun h _ => mul_mem (mul_mem ?_ ?_) ?_)
  · exact RingOfIntegers.isIntegral_coe _
  · exact RingOfIntegers.isIntegral_coe _
  · exact (hC K G T τ _).1
end Formalism.IndefR.LatticeTransfer.NormTraceLemmas
