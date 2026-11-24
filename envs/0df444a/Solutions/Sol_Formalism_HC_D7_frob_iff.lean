-- Prove2me | solution 1 for Formalism.HC.D7.frob_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:36.192081+00:00
-- url     : https://prove2.me/submissions/13610284-cf31-4aee-ba0e-80813acabe7d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_jac_recip
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_artinMap_first_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_artinMap_second_eq_jacobiSym_of_modEq
import Theorems.Thm_Formalism_HC_D7_artinMap_dyadic_eq_of_modEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_two_dvd


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
theorem _root_.solution {p : ℕ} (hp : p % 2 = 1) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)) = (p : ZMod (2 ^ (e + 2) * q * d))) (g : FrobeniusOrbits.GG e) :
    (((g.1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧ ((g.1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
      ∃ v : (ZMod (2 ^ (e + 2)))ˣ, (v : ZMod (2 ^ (e + 2))) = (p : ZMod _) ∧ g.2 = hcl e v) ↔ g = art0 e hH u := by
  haveI := neZeroN e hH
  have hup : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD 2 ^ (e + 2) * q * d] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [ZMod.natCast_zmod_val, hu])
  have eq1 : (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p := by
    rw [artinMap_first_eq_jacobiSym_of_modEq e hH u (hup.of_dvd (q_dvd e q d)), jac_recip (q4 hH) hp]
  have eq2 : (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p := by
    rw [artinMap_second_eq_jacobiSym_of_modEq e hH u (hup.of_dvd (d_dvd e q d)), jac_recip (d4 hH) hp]
  have hc : Nat.Coprime p (2 ^ (e + 2)) := by
    have : Nat.Coprime p 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    exact this.pow_right (e + 2)
  constructor
  · rintro ⟨h1, h2, v, hv, h3⟩
    exact Prod.ext (Prod.ext (Units.ext (h1.trans eq1.symm)) (Units.ext (h2.trans eq2.symm)))
      (h3.trans (artinMap_dyadic_eq_of_modEq e hH u (hup.of_dvd (two_dvd e q d)) v hv).symm)
  · rintro rfl
    exact ⟨eq1, eq2, ZMod.unitOfCoprime p hc, ZMod.coe_unitOfCoprime _ _,
      artinMap_dyadic_eq_of_modEq e hH u (hup.of_dvd (two_dvd e q d)) _ (ZMod.coe_unitOfCoprime _ _)⟩
end Formalism.HC.D7
