-- Prove2me | solution 1 for Formalism.HC.Frame.hostOrbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:23.044808+00:00
-- url     : https://prove2.me/submissions/032a01b7-6fd4-4390-9882-4e0af79f7f9d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_TwoGroup_even_orderOf
import Theorems.Thm_Formalism_HC_Frame_pow_mul_mem_Psi_iff
import Theorems.Thm_P2M_Formalism_HC_Frame_hostOrbits__2cb81a5b86d8
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
private theorem not_mem_Psi_of_fst_eq_c0_or (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    g ∉ φ.Psi := by
  rw [mem_Psi_iff]
  rcases hg with h | h <;> rw [h] <;> exact int_units_neg_one_ne_one
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (h2 : φ.TwoGroup) (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    (∀ τ ∈ φ.Psi, ∀ i : ℕ, g ^ i * τ ∈ φ.Psi ↔ Even i) ∧
    (g.1 = c0 → g.2 ≠ 1 → Even (orderOf g.2) ∧ orderOf g = orderOf g.2) := by
  have hg' := not_mem_Psi_of_fst_eq_c0_or φ g hg
  refine ⟨fun τ hτ i => φ.pow_mul_mem_Psi_iff hg' hτ i, fun hc h1 => ?_⟩
  have he := h2.even_orderOf h1
  exact ⟨he, (φ.hostOrbits' g hg).2 hc he⟩
end Formalism.HC.Frame
