-- Prove2me | solution 1 for Formalism.HC.Frame.hostOrbitCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:54.279723+00:00
-- url     : https://prove2.me/submissions/46cae38b-dc9c-4743-b4aa-1bac6d21645d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_hostOrbitsPlaces
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitsPlaces

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
private theorem ncard_range_pow_eq_orderOf {M : Type*} [Group M] (x : M) :
    (Set.range fun i : ℕ => x ^ i).ncard = orderOf x := by
  have h : Nat.card (Submonoid.powers x) = orderOf x := Nat.card_submonoidPowers
  rw [← h, ← Submonoid.coe_powers]
  exact (Nat.card_coe_set_eq _).symm
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (g : φ.GG) (h0 : g.1 = c0) (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    (Set.range fun i : ℕ => placeOf (g ^ i * τ)).ncard = orderOf g.2 := by
  have hfun : (fun i : ℕ => placeOf (g ^ i * τ)) =
      (fun y : φ.MA => ((τ.1, y * τ.2) : φ.GG)) ∘ (fun i : ℕ => g.2 ^ i) := by
    funext i
    obtain ⟨h1, h2, -⟩ := φ.hostOrbitsPlaces g (Or.inl h0) τ hτ i
    exact Prod.ext (h2 h0) h1
  rw [hfun, Set.range_comp, Set.ncard_image_of_injective _
    (fun y y' h => mul_right_cancel (congrArg Prod.snd h)), ncard_range_pow_eq_orderOf]
end Formalism.HC.Frame
