-- Prove2me | solution 1 for Formalism.HC.Frame.hostCharSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:41.188831+00:00
-- url     : https://prove2.me/submissions/36d91cce-5631-4898-9631-53813b6b58fa

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_card_GG
import Theorems.Thm_Formalism_HC_Frame_chC_apply
import Theorems.Thm_Formalism_HC_Frame_twHom_eq_one_iff
import Theorems.Thm_Formalism_HC_Frame_chC_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_chC_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_chC_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_twHom_eq_one_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_GG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
open Classical
namespace Formalism.HC.Frame
theorem _root_.solution :
    (∀ χ : φ.GG →* ℂˣ,
      (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        if χ = 1 then (2 * φ.ord : ℂ) else if χ = φ.chC then -(2 * φ.ord : ℂ) else 0) ∧
    ∀ g : φ.GG,
      4 * (if g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
        (1 - ((φ.chD g : ℤˣ) : ℤ)) * (1 + ((φ.chQ g : ℤˣ) : ℤ)) := by
  refine ⟨fun χ => ?_, fun g => ?_⟩
  · let f : φ.GG →* ℂ := Formalism.FrobeniusOrbits.Misc2.conjHom χ
    have hfg : ∀ g, f g = starRingEnd ℂ ((χ g : ℂˣ) : ℂ) := fun g => rfl
    have hT1 : (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∈ φ.Psi), f g) +
        (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = ∑ g, f g :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hT2 : (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∈ φ.Psi), f g) -
        (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = ∑ g, φ.twHom χ g := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : φ.GG => g ∈ φ.Psi)
        (φ.twHom χ), sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.mem_filter] at hg
        show f g = ((φ.chC g : ℂˣ) : ℂ) * f g
        rw [φ.chC_apply, (mem_Psi_iff g).1 hg.2]
        simp
      · apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.mem_filter] at hg
        show -f g = ((φ.chC g : ℂˣ) : ℂ) * f g
        rw [φ.chC_apply, (Int.units_eq_one_or _).resolve_left (fun h => hg.2 ((mem_Psi_iff g).2 h))]
        simp
    have hf1 : f = 1 ↔ χ = 1 := by
      constructor
      · intro h
        ext g
        have h1 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 := by rw [← hfg, h, MonoidHom.one_apply]
        have h2 := congrArg (starRingEnd ℂ) h1
        rw [Complex.conj_conj, map_one] at h2
        first
        | exact h2
        | exact Units.ext h2
      · intro h
        ext g
        rw [hfg, h]
        simp
    have hS1 : (∑ g, f g) = if χ = 1 then (4 * φ.ord : ℂ) else 0 := by
      rw [sum_hom_units]
      by_cases h : χ = 1
      · rw [if_pos (hf1.2 h), if_pos h, φ.card_GG]
        norm_num
      · rw [if_neg (fun h' => h (hf1.1 h')), if_neg h, Nat.cast_zero]
    have hS2 : (∑ g, φ.twHom χ g) = if χ = φ.chC then (4 * φ.ord : ℂ) else 0 := by
      rw [sum_hom_units]
      by_cases h : χ = φ.chC
      · rw [if_pos ((φ.twHom_eq_one_iff χ).2 h), if_pos h, φ.card_GG]
        norm_num
      · rw [if_neg (fun h' => h ((φ.twHom_eq_one_iff χ).1 h')), if_neg h, Nat.cast_zero]
    show (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = _
    rw [hS1] at hT1
    rw [hS2] at hT2
    by_cases h1 : χ = 1
    · have h2 : χ ≠ φ.chC := fun h => φ.chC_ne_one (h.symm.trans h1)
      rw [if_pos h1] at hT1 ⊢
      rw [if_neg h2] at hT2
      linear_combination (hT1 - hT2) / 2
    · rw [if_neg h1] at hT1 ⊢
      by_cases h2 : χ = φ.chC
      · rw [if_pos h2] at hT2 ⊢
        linear_combination (hT1 - hT2) / 2
      · rw [if_neg h2] at hT2 ⊢
        linear_combination (hT1 - hT2) / 2
  · obtain ⟨⟨q, d⟩, a⟩ := g
    show 4 * (if ((q, d) : G0) = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
      (1 - ((d : ℤˣ) : ℤ)) * (1 + ((q : ℤˣ) : ℤ))
    rcases Int.units_eq_one_or q with rfl | rfl <;> rcases Int.units_eq_one_or d with rfl | rfl <;>
      norm_num [int_units_neg_one_ne_one, int_units_neg_one_ne_one.symm]
end Formalism.HC.Frame
