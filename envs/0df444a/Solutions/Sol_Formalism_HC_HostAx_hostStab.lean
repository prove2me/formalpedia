-- Prove2me | solution 1 for Formalism.HC.HostAx.hostStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:54.108214+00:00
-- url     : https://prove2.me/submissions/9fd6e8e5-c732-4bf8-ae30-eebf09a3fae5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_HostAx_hostFiniteOrder
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFiniteOrder
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (k g : ℕ) (hg : g.Prime) (hlt : 4 * φ.ord * k < g - 1)
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin k) H.E)) (hΓ : ∀ γ ∈ Γ, ∃ m : ℕ, orderOf γ = g ^ m) : Γ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro γ hγ
  obtain ⟨m, hm⟩ := hΓ γ hγ
  cases m with
  | zero => simpa using hm
  | succ m =>
    exfalso
    have h1 := orderOf_pow_orderOf_div (x := γ) (n := g) (by rw [hm]; exact pow_ne_zero _ hg.ne_zero)
      (by rw [hm]; exact dvd_pow_self g (Nat.succ_ne_zero m))
    have hpow := pow_orderOf_eq_one (γ ^ (orderOf γ / g))
    rw [h1] at hpow
    have hMg : (((γ ^ (orderOf γ / g) : Matrix.GeneralLinearGroup (Fin k) H.E)) : Matrix (Fin k) (Fin k) H.E) ^ g = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
    have hne : (((γ ^ (orderOf γ / g) : Matrix.GeneralLinearGroup (Fin k) H.E)) : Matrix (Fin k) (Fin k) H.E) ≠ 1 := by
      intro h
      have h0 : γ ^ (orderOf γ / g) = 1 := Units.ext (by rw [Units.val_one]; exact h)
      rw [h0, orderOf_one] at h1
      exact hg.one_lt.ne h1
    have := H.hostFiniteOrder k g hg _ hMg hne
    omega
end Formalism.HC.HostAx
