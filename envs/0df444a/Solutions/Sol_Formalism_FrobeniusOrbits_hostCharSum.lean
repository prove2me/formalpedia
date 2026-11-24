-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostCharSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:50:38.111729+00:00
-- url     : https://prove2.me/submissions/e5dfee11-0057-4b13-8929-367a596ed209

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_chC_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_conjHom_eq_one_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_twHom_eq_one_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_chC_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_card_extended_galois_group
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Misc2
open Classical
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostCharSum := by
  intro e
  refine ⟨fun χ => ?_, fun g => ?_⟩
  · have hpt : ∀ g : GG e, 2 * (if g ∉ Psi e then starRingEnd ℂ ((χ g : ℂˣ) : ℂ) else 0) =
        conjHom χ g - twHom e χ g := by
      intro g
      simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, chC_apply, mem_Psi_iff]
      rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp <;> ring
    have hA := sum_hom_units (conjHom χ)
    have hB := sum_hom_units (twHom e χ)
    simp only [conjHom_eq_one_iff, twHom_eq_one_iff, Nat.cast_ite, Nat.cast_zero] at hA hB
    have hS : 2 * (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e),
        starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        (∑ g : GG e, conjHom χ g) - ∑ g : GG e, twHom e χ g := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun g _ => hpt g)
    rw [hA, hB, card_extended_galois_group] at hS
    have hne := chC_ne_one e
    split_ifs at hS ⊢ with h1 h2 h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hne)
    · linear_combination hS / 2
    · linear_combination hS / 2
    · linear_combination hS / 2
  · simp only [chD, chQ, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, Prod.ext_iff]
    rcases Int.units_eq_one_or g.1.1 with h | h <;> rcases Int.units_eq_one_or g.1.2 with h' | h' <;>
      rw [h, h'] <;> decide
end Formalism.FrobeniusOrbits
