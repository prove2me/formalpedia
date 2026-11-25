-- Prove2me | solution 1 for Formalism.HC.Frame.hostOrbitCountSg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:50:16.510375+00:00
-- url     : https://prove2.me/submissions/396e14b8-c5f4-41bb-8e6f-95e6fc3d17b0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_hostOrbitsPlaces
import Theorems.Thm_Formalism_HC_Frame_orbEmb_injective
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
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
private theorem sign_group_sq_eq_one_var (x : G0) : x ^ 2 = 1 :=
  Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)
private theorem ncard_range_pow_eq_orderOf {M : Type*} [Group M] (x : M) :
    (Set.range fun i : ℕ => x ^ i).ncard = orderOf x := by
  have h : Nat.card (Submonoid.powers x) = orderOf x := Nat.card_submonoidPowers
  rw [← h, ← Submonoid.coe_powers]
  exact (Nat.card_coe_set_eq _).symm
private theorem orderOf_int_units_neg_one_eq_two : orderOf (-1 : ℤˣ) = 2 :=
  orderOf_eq_prime (Int.units_sq _) int_units_neg_one_ne_one
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (g : φ.GG) (h0 : g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    orderOf g = Nat.lcm 2 (orderOf g.2) ∧
    (Set.range fun i : ℕ => placeOf (g ^ i * τ)).ncard = orderOf g := by
  have hsq : orderOf g.1 = 2 := by
    rw [h0]
    exact orderOf_eq_prime (sign_group_sq_eq_one_var _) (fun h => int_units_neg_one_ne_one (congrArg Prod.snd h))
  have hord : orderOf g = Nat.lcm 2 (orderOf g.2) := by rw [Prod.orderOf, hsq]
  refine ⟨hord, ?_⟩
  have hfun : (fun i : ℕ => placeOf (g ^ i * τ)) =
      φ.orbEmb τ ∘ (fun i : ℕ => (((-1 : ℤˣ), g.2) : ℤˣ × φ.MA) ^ i) := by
    funext i
    obtain ⟨h1, -, h3⟩ := φ.hostOrbitsPlaces g (Or.inr h0) τ hτ i
    refine Prod.ext ?_ h1
    rw [h3 h0]
    show _ = (if ((-1 : ℤˣ) ^ i) = 1 then 1 else φ.sg.1) * τ.1
    by_cases hi : Even i
    · rw [if_pos hi, if_pos ((neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one).1 h))]
  rw [hfun, Set.range_comp, Set.ncard_image_of_injective _ (φ.orbEmb_injective τ),
    ncard_range_pow_eq_orderOf, hord, Prod.orderOf]
  exact congrArg (fun n => Nat.lcm n (orderOf g.2)) orderOf_int_units_neg_one_eq_two
end Formalism.HC.Frame
