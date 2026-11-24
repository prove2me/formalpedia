-- Prove2me | solution 1 for Formalism.BasicNotions.Host.psAt_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:15.3198+00:00
-- url     : https://prove2.me/submissions/5cdb16b2-3da8-403f-bfe2-ed134c3ca748

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
include H
namespace Formalism.BasicNotions.Host
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ H.condN) : H.psAt p = jacobiSym (-(H.q : ℤ)) p := by
  have hc : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have hh := H.hyp
  unfold HostHyp at hh
  obtain ⟨hq, -, hq8, -, -⟩ := hh
  have hq4 : H.q % 4 = 3 := by omega
  have h2 : p ≠ 2 := by
    intro h2
    apply h
    rw [h2]
    have h5 : 2 ∣ H.QS := dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h5 _) _
  have hpo : Odd p := hp.odd_of_ne_two h2
  have hqo : Odd H.q := hq.odd_of_ne_two (by omega)
  have step1 : H.psAt p = jacobiSym (p : ℤ) H.q := by
    unfold HostRaw.psAt
    rw [dif_pos hc, H.flPS (ZMod.unitOfCoprime p hc)]
    apply jacobiSym.mod_left'
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Int.natCast_mod]
    apply Int.emod_emod_of_dvd
    exact Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp hpo
    omega
  rw [step1, jacobiSym.neg _ hpo]
  rcases h4 with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hq4]
    ring
end Formalism.BasicNotions.Host
