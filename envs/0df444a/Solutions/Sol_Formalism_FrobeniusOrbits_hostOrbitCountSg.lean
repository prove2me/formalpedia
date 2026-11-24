-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostOrbitCountSg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:54:54.053567+00:00
-- url     : https://prove2.me/submissions/80d14a85-1d11-4493-89e1-8f170cf76a9e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_orderOf_negOne
import Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_orderOf_oneNeg
import Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_emb_injective
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrbitsPlaces


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open OrbitSg
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostOrbitCountSg := by
  intro e φ h0 τ hτ
  have hord : orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
    rw [Prod.orderOf, h0, orderOf_oneNeg]
  refine ⟨hord, ?_⟩
  have hpl : (fun i : ℕ => placeOf (φ ^ i * τ)) =
      emb τ ∘ (fun i : ℕ => (((-1 : ℤˣ), φ.2) : ℤˣ × HGrp e) ^ i) := by
    funext i
    have hP := hostOrbitsPlaces e φ (Or.inr h0) τ hτ i
    refine Prod.ext ?_ ?_
    · rw [hP.2.2 h0]
      simp only [Function.comp_apply, emb, Prod.pow_fst]
      congr 1
      rcases Nat.even_or_odd i with he | ho
      · rw [if_pos he, if_pos he.neg_one_pow]
      · rw [if_neg (Nat.not_even_iff_odd.2 ho), if_neg (by rw [ho.neg_one_pow]; decide)]
    · rw [hP.1]
      simp [emb]
  rw [hpl, Set.range_comp, Set.ncard_image_of_injective _ (emb_injective τ),
    ← Submonoid.coe_powers, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_submonoidPowers,
    hord, Prod.orderOf, orderOf_negOne]
end Formalism.FrobeniusOrbits
