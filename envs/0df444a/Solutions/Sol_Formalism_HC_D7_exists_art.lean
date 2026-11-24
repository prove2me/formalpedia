-- Prove2me | solution 1 for Formalism.HC.D7.exists_art
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:33.471841+00:00
-- url     : https://prove2.me/submissions/8cac61e4-e00d-4863-ab3d-29a909052992

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_exists_unit
import Theorems.Thm_Formalism_HC_D7_artinMap_first_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_artinMap_dyadic_eq_of_modEq

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
theorem _root_.solution (g : FrobeniusOrbits.GG e) (x y z : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (x : ZMod (2 ^ (e + 2)))) (hx : g.2 = hcl e v)
    (hy : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) q) (hz : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym (z : ℤ) d) :
    ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ, (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ x [MOD 2 ^ (e + 2)] ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q] ∧ (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ z [MOD d] ∧
      g = art0 e hH u := by
  have hx' : Nat.Coprime x (2 ^ (e + 2)) := by
    rw [← ZMod.isUnit_iff_coprime, ← hv]
    exact v.isUnit
  have hy' : Nat.Coprime y q := by
    haveI : NeZero q := ⟨hH.1.ne_zero⟩
    have h0 : jacobiSym (y : ℤ) q ≠ 0 := by
      rw [← hy]
      exact Units.ne_zero _
    have h1 := mt jacobiSym.eq_zero_iff_not_coprime.mpr h0
    push_neg at h1
    rwa [Int.gcd_natCast_natCast] at h1
  have hz' : Nat.Coprime z d := by
    haveI : NeZero d := ⟨hH.2.1.ne_zero⟩
    have h0 : jacobiSym (z : ℤ) d ≠ 0 := by
      rw [← hz]
      exact Units.ne_zero _
    have h1 := mt jacobiSym.eq_zero_iff_not_coprime.mpr h0
    push_neg at h1
    rwa [Int.gcd_natCast_natCast] at h1
  obtain ⟨u, h1, h2, h3⟩ := exists_unit e hH x y z hx' hy' hz'
  refine ⟨u, h1, h2, h3, Prod.ext (Prod.ext (Units.ext ?_) (Units.ext ?_)) ?_⟩
  · rw [artinMap_first_eq_jacobiSym_of_modEq e hH u h2, hy]
  · rw [artinMap_second_eq_jacobiSym_of_modEq e hH u h3, hz]
  · rw [artinMap_dyadic_eq_of_modEq e hH u h1 v hv, hx]
end Formalism.HC.D7
