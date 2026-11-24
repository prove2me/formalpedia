-- Prove2me | solution 1 for Formalism.NG.powSubPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:44.48235+00:00
-- url     : https://prove2.me/submissions/3bed0e0d-f438-4dff-912e-3ad9f74abcf2

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.NG
private lemma vInt_eq_emult (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  rw [padicValInt.of_ne_one_ne_zero hl.out.ne_one hz]
  exact (FiniteMultiplicity.emultiplicity_eq_multiplicity
    (Int.finiteMultiplicity_iff.mpr ⟨by simpa using hl.out.ne_one, hz⟩)).symm
end Formalism.NG
end

set_option autoImplicit false
open Finset
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatPowSubPow := by
  intro l hl hl2 x hx1 hx2 a b hab
  have hp : l.Prime := hl.out
  have hodd : Odd l := hp.odd_of_ne_two hl2
  have hpi : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by
      have := dvd_sub h hx1
      simpa using this
    exact hpi.not_dvd_one h1
  have hx1ne : x - 1 ≠ 0 := by
    intro h; exact hx2 (by rw [h]; exact dvd_zero _)
  have hv1 : padicValInt l (x - 1) = 1 := by
    have h1 := (padicValInt_dvd_iff (p := l) 1 (x - 1)).mp (by simpa using hx1)
    have h2 : ¬ (2 ≤ padicValInt l (x - 1)) := fun h =>
      hx2 ((padicValInt_dvd_iff (p := l) 2 (x - 1)).mpr (Or.inr h))
    rcases h1 with h1 | h1
    · exact absurd h1 hx1ne
    · omega
  set n := b - a with hn
  have hn0 : n ≠ 0 := by omega
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd (x := x) (y := 1) (by simpa using hx1) hx n
  rw [one_pow] at hlte
  rw [← vInt_eq_emult l hx1ne, hv1, ← padicValNat_eq_emultiplicity_of_ne_one hp.ne_one hn0] at hlte
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hlte
    have h' : ((1 + padicValNat l n : ℕ) : ℕ∞) = ⊤ := by push_cast; exact hlte.symm
    exact ENat.natCast_ne_top _ h'
  have hv : padicValInt l (x ^ n - 1) = 1 + padicValNat l n := by
    rw [← vInt_eq_emult l hne] at hlte
    exact_mod_cast hlte
  have hxa : x ^ a ≠ 0 := pow_ne_zero _ (fun h => hx (by rw [h]; exact dvd_zero _))
  have hfac : x ^ b - x ^ a = x ^ a * (x ^ n - 1) := by
    have : b = a + n := by omega
    rw [this, pow_add]; ring
  rw [hfac, padicValInt.mul hxa hne, hv,
    padicValInt.eq_zero_of_not_dvd (fun h => hx (hpi.dvd_of_dvd_pow h))]
  ring
end Formalism.NG
