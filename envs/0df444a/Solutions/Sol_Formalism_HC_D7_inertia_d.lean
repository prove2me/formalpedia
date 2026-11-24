-- Prove2me | solution 1 for Formalism.HC.D7.inertia_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:41:15.968129+00:00
-- url     : https://prove2.me/submissions/da8024db-da88-42c4-927a-be943d412015

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_exists_sign
import Theorems.Thm_Formalism_HC_D7_cop_2q
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_artinMap_first_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_artinMap_dyadic_eq_of_modEq
import Theorems.Thm_Formalism_HC_D7_exists_art
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
theorem _root_.solution (g : FrobeniusOrbits.GG e) : (g = 1 ∨ g = ((1, -1), 1)) ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2) * q] ∧ g = art0 e hH u := by
  constructor
  · intro hg
    have hg2 : g.2 = hcl e 1 := by
      rcases hg with rfl | rfl <;> rfl
    have hg11 : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) q := by
      rcases hg with rfl | rfl <;> simp [jacobiSym.one_left]
    obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) g.1.2
    obtain ⟨u, h1, h2, -, hu⟩ := exists_art e hH g 1 1 z 1 (by simp) hg2 hg11 hz.symm
    exact ⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨h1, h2⟩, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have h1 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)] := hu.of_dvd (dvd_mul_right _ _)
    have h2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q] := hu.of_dvd (dvd_mul_left _ _)
    have e1 := artinMap_dyadic_eq_of_modEq e hH u h1 1 (by simp)
    have e2' : (art0 e hH u).1.1 = 1 := Units.ext (by rw [artinMap_first_eq_jacobiSym_of_modEq e hH u h2]; simp [jacobiSym.one_left])
    have e1' : (art0 e hH u).2 = 1 := by rw [e1]; rfl
    rcases Int.units_eq_one_or (art0 e hH u).1.2 with h | h
    · exact Or.inl (Prod.ext (Prod.ext e2' h) e1')
    · exact Or.inr (Prod.ext (Prod.ext e2' h) e1')
end Formalism.HC.D7
