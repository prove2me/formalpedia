-- Prove2me | solution 1 for Formalism.HC.Frame.pow_mul_mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:07:37.480056+00:00
-- url     : https://prove2.me/submissions/7a95bdd2-ccca-4efc-badf-ff7e3a6a7aaf

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
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
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution {g : φ.GG} (hg : g ∉ φ.Psi) {τ : φ.GG} (hτ : τ ∈ φ.Psi) (i : ℕ) :
    g ^ i * τ ∈ φ.Psi ↔ Even i := by
  rw [mem_Psi_iff] at hg hτ
  rw [mem_Psi_iff]
  have hg' : g.1.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
  show g.1.2 ^ i * τ.1.2 = 1 ↔ Even i
  rw [hg', hτ, mul_one]
  exact neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one
end Formalism.HC.Frame
