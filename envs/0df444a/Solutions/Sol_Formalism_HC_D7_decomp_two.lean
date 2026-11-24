-- Prove2me | solution 1 for Formalism.HC.D7.decomp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:14.072351+00:00
-- url     : https://prove2.me/submissions/18fbbc25-8f6b-43d9-bbf8-e91703192622

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_cop_qd
import Theorems.Thm_Formalism_HC_D7_jac_2q
import Theorems.Thm_Formalism_HC_D7_jac_2d
import Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_exists_art
import Theorems.Thm_Formalism_HC_D7_exists_rep
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution (g : FrobeniusOrbits.GG e) : g.1.2 = 1 ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 2 ^ k [MOD q * d] ∧ g = art0 e hH u := by
  have hJ : ∀ k : ℕ, jacobiSym ((2 ^ k : ℕ) : ℤ) q = (-1) ^ k ∧ jacobiSym ((2 ^ k : ℕ) : ℤ) d = 1 := by
    intro k
    rw [Nat.cast_pow, jacobiSym.pow_left, jacobiSym.pow_left, jac_2q hH, jac_2d hH, one_pow]
    exact ⟨rfl, rfl⟩
  constructor
  · intro hg
    obtain ⟨x, v, hv, hx⟩ := exists_rep e g.2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((g.1.1 : ℤˣ) : ℤ) = (-1) ^ k := by
      rcases Int.units_eq_one_or g.1.1 with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    obtain ⟨u, -, hq, hd, hu⟩ := exists_art e hH g x (2 ^ k) (2 ^ k) v hv hx
      (by rw [hk, (hJ k).1]) (by rw [hg, Units.val_one, (hJ k).2])
    exact ⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨hq, hd⟩, hu⟩
  · rintro ⟨u, k, hu, rfl⟩
    apply Units.ext
    rw [artinMap_second_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), (hJ k).2, Units.val_one]
end Formalism.HC.D7
