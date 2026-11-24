-- Prove2me | solution 1 for Formalism.HC.Der.frob_iff_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:44.296359+00:00
-- url     : https://prove2.me/submissions/2050c3dc-7195-4a2b-850f-54c96bc0b50a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.Der
theorem _root_.solution {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] [SMulCommClass G ℤ S]
    (P : Ideal S) (F σ : G) (hF : IsArithFrobAt ℤ F P) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : S, (σ * F⁻¹) • x - x ∈ P := by
  have hF' : ∀ x : S, F • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hF
  constructor
  · intro hσ x
    have hσ' : ∀ x : S, σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hσ
    have h1 := P.sub_mem (hσ' (F⁻¹ • x)) (hF' (F⁻¹ • x))
    rwa [smul_inv_smul, ← mul_smul, sub_sub_sub_cancel_right] at h1
  · intro hρ x
    show σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    have h1 := P.add_mem (hρ (F • x)) (hF' x)
    rwa [← mul_smul, inv_mul_cancel_right, sub_add_sub_cancel] at h1
end Formalism.HC.Der
