-- Prove2me | solution 1 for Formalism.HC.D7.decomp_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:12.825887+00:00
-- url     : https://prove2.me/submissions/839908c5-0977-4247-98c3-564c98820664

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_exists_sign
import Theorems.Thm_Formalism_HC_D7_hcl_pow
import Theorems.Thm_Formalism_HC_D7_cop_2d
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_D7_jac_qd
import Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym_of_modEq
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
theorem _root_.solution (uq : (ZMod (2 ^ (e + 2)))ˣ) (huq : (uq : ZMod (2 ^ (e + 2))) = (q : ZMod _)) (g : FrobeniusOrbits.GG e) :
    (g.1.2 = 1 ∧ ∃ k : ℕ, g.2 = hcl e uq ^ k) ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ q ^ k [MOD 2 ^ (e + 2) * d] ∧ g = art0 e hH u := by
  have hJ : ∀ k : ℕ, jacobiSym ((q ^ k : ℕ) : ℤ) d = 1 := by
    intro k
    rw [Nat.cast_pow, jacobiSym.pow_left, jac_qd hH, one_pow]
  have hV : ∀ k : ℕ, ((uq ^ k : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((q ^ k : ℕ) : ZMod _) := by
    intro k
    rw [Units.val_pow_eq_pow_val, huq, Nat.cast_pow]
  constructor
  · rintro ⟨hg, k, hk⟩
    obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) g.1.1
    obtain ⟨u, h1, -, h3, hu⟩ := exists_art e hH g (q ^ k) y (q ^ k) (uq ^ k) (hV k)
      (by rw [hk, hcl_pow]) hy.symm (by rw [hg, Units.val_one, hJ k])
    exact ⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨h1, h3⟩, hu⟩
  · rintro ⟨u, k, hu, rfl⟩
    refine ⟨Units.ext ?_, k, ?_⟩
    · rw [artinMap_second_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), hJ k, Units.val_one]
    · rw [artinMap_dyadic_eq_of_modEq e hH u (hu.of_dvd (dvd_mul_right _ _)) (uq ^ k) (hV k), hcl_pow]
end Formalism.HC.D7
