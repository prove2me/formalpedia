-- Prove2me | solution 1 for Formalism.HC.D7.inertia_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:41:16.349428+00:00
-- url     : https://prove2.me/submissions/7a1a6341-989e-4c13-8242-eedb18881c45

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_cop_qd
import Theorems.Thm_Formalism_HC_D7_artinMap_first_eq_jacobiSym_of_modEq
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
theorem _root_.solution (g : FrobeniusOrbits.GG e) : g.1 = 1 ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q * d] ∧ g = art0 e hH u := by
  constructor
  · intro hg
    obtain ⟨x, v, hv, hx⟩ := exists_rep e g.2
    have h1 : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) q := by
      rw [hg]
      simp [jacobiSym.one_left]
    have h2 : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) d := by
      rw [hg]
      simp [jacobiSym.one_left]
    obtain ⟨u, -, hq, hd, hu⟩ := exists_art e hH g x 1 1 v hv hx h1 h2
    exact ⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨hq, hd⟩, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have hq : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q] := hu.of_dvd (dvd_mul_right _ _)
    have hd : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d] := hu.of_dvd (dvd_mul_left _ _)
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [artinMap_first_eq_jacobiSym_of_modEq e hH u hq]
      simp [jacobiSym.one_left]
    · rw [artinMap_second_eq_jacobiSym_of_modEq e hH u hd]
      simp [jacobiSym.one_left]
end Formalism.HC.D7
