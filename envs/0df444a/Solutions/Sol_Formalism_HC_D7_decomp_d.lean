-- Prove2me | solution 1 for Formalism.HC.D7.decomp_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:11.633603+00:00
-- url     : https://prove2.me/submissions/3a5de88c-9090-4609-8e13-f670d972048c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_exists_sign
import Theorems.Thm_Formalism_HC_D7_hcl_pow
import Theorems.Thm_Formalism_HC_D7_cop_2q
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_jac_dq
import Theorems.Thm_Formalism_HC_D7_artinMap_first_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_artinMap_dyadic_eq_of_modEq
import Theorems.Thm_Formalism_HC_D7_exists_art

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution (ud : (ZMod (2 ^ (e + 2)))ˣ) (hud : (ud : ZMod (2 ^ (e + 2))) = (d : ZMod _)) (g : FrobeniusOrbits.GG e) :
    (∃ k : ℕ, g.1.1 = (-1) ^ k ∧ g.2 = hcl e ud ^ k) ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ d ^ k [MOD 2 ^ (e + 2) * q] ∧ g = art0 e hH u := by
  have hJ : ∀ k : ℕ, jacobiSym ((d ^ k : ℕ) : ℤ) q = (-1) ^ k := by
    intro k
    rw [Nat.cast_pow, jacobiSym.pow_left, jac_dq hH]
  have hV : ∀ k : ℕ, ((ud ^ k : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((d ^ k : ℕ) : ZMod _) := by
    intro k
    rw [Units.val_pow_eq_pow_val, hud, Nat.cast_pow]
  constructor
  · rintro ⟨k, hk1, hk2⟩
    obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) g.1.2
    obtain ⟨u, h1, h2, -, hu⟩ := exists_art e hH g (d ^ k) (d ^ k) z (ud ^ k) (hV k)
      (by rw [hk2, hcl_pow]) (by rw [hk1, hJ k]; push_cast; rfl) hz.symm
    exact ⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨h1, h2⟩, hu⟩
  · rintro ⟨u, k, hu, rfl⟩
    refine ⟨k, Units.ext ?_, ?_⟩
    · rw [artinMap_first_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), hJ k]
      push_cast
      rfl
    · rw [artinMap_dyadic_eq_of_modEq e hH u (hu.of_dvd (dvd_mul_right _ _)) (ud ^ k) (hV k), hcl_pow]
end Formalism.HC.D7
