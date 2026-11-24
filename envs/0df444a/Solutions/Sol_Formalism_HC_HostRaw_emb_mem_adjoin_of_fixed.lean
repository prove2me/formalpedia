-- Prove2me | solution 1 for Formalism.HC.HostRaw.emb_mem_adjoin_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:32.877366+00:00
-- url     : https://prove2.me/submissions/77378c60-9fc9-49e9-9c94-21ef945a1d5d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_HC_Der_cyc_isGalois
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_HC_Der_tauN_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution {m : ℕ} (hm : m ∣ H.condN) (x : H.E)
    (hx : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] → H.gal.symm (H.art u) x = x) :
    emb H x ∈ adjoin ℚ {y : Cond.Cyc H.condN | y ^ m = 1} := by
  have := cyc_isGalois H.condN
  rw [← IsGalois.fixedField_fixingSubgroup (adjoin ℚ {y : Cond.Cyc H.condN | y ^ m = 1}), mem_fixedField_iff]
  intro τ hτ
  obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
  rw [← emb_art, hx u]
  obtain ⟨k, hk⟩ := hm
  have hz : IsPrimitiveRoot ((H.cycZeta : Cond.Cyc H.condN) ^ k) m :=
    H.cycZeta_prim.pow (Nat.pos_of_ne_zero H.condN_ne_zero) (hk.trans (mul_comm _ _))
  have h1 := (mem_fixingSubgroup_iff _ _).1 hτ _ (subset_adjoin _ _ (show _ ^ m = 1 from hz.pow_eq_one))
  rw [tauN_root _ _ _ (hz.pow_eq_one_iff_dvd _ |>.2 ⟨k, hk⟩)] at h1
  obtain ⟨w, hw⟩ := hz.isUnit (Nat.pos_of_ne_zero fun h => H.condN_ne_zero (by rw [hk, h, zero_mul])).ne'
  rw [hz.eq_orderOf, ← hw, orderOf_units, ← pow_eq_pow_iff_modEq, pow_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hw]
  exact h1
end Formalism.HC.HostRaw
