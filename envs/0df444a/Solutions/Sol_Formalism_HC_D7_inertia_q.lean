-- Prove2me | solution 1 for Formalism.HC.D7.inertia_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:15.263568+00:00
-- url     : https://prove2.me/submissions/99fed175-58ca-49c1-9b86-0c68cf9632d8

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_exists_sign
import Theorems.Thm_Formalism_HC_D7_cop_2d
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym_of_modEq
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
theorem _root_.solution (g : FrobeniusOrbits.GG e) : (g = 1 ∨ g = sg e) ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2) * d] ∧ g = art0 e hH u := by
  constructor
  · intro hg
    have hg2 : g.2 = hcl e 1 := by
      rcases hg with rfl | rfl <;> rfl
    have hg12 : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) d := by
      rcases hg with rfl | rfl <;> simp [sg, jacobiSym.one_left]
    obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) g.1.1
    obtain ⟨u, h1, -, h3, hu⟩ := exists_art e hH g 1 y 1 1 (by simp) hg2 hy.symm hg12
    exact ⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨h1, h3⟩, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have h2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)] := hu.of_dvd (dvd_mul_right _ _)
    have h3 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d] := hu.of_dvd (dvd_mul_left _ _)
    have e2 := artinMap_dyadic_eq_of_modEq e hH u h2 1 (by simp)
    have e3' : (art0 e hH u).1.2 = 1 := Units.ext (by rw [artinMap_second_eq_jacobiSym_of_modEq e hH u h3]; simp [jacobiSym.one_left])
    have e2' : (art0 e hH u).2 = 1 := by rw [e2]; rfl
    rcases Int.units_eq_one_or (art0 e hH u).1.1 with h | h
    · exact Or.inl (Prod.ext (Prod.ext h e3') e2')
    · exact Or.inr (Prod.ext (Prod.ext h e3') e2')
end Formalism.HC.D7
