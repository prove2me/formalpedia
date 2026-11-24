-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_pp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:20.543746+00:00
-- url     : https://prove2.me/submissions/c682fe59-0753-4136-8c2f-f8d740b1dff1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_odd
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
theorem _root_.solution (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (p k : ℕ) (hp : p.Prime) :
    Rep q d (p ^ k) := by
  have := Fact.mk hp
  have key : ∀ c : ℕ, (∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1) →
      ∃ α β : ZMod (p ^ k), α ^ 2 + (c : ZMod (p ^ k)) * β ^ 2 = -1 := by
    rintro c ⟨x, y, h⟩
    refine ⟨PadicInt.toZModPow k x, PadicInt.toZModPow k y, ?_⟩
    simpa using congrArg (PadicInt.toZModPow (p := p) k) h
  rcases eq_or_ne p q with hpq | hpq
  · have hp2 : p ≠ 2 := by
      rintro rfl; rw [← hpq] at hq8; norm_num at hq8
    have hpd : ¬ p ∣ d := fun h =>
      hqd ((Nat.prime_dvd_prime_iff_eq hq hd).1 (by rwa [← hpq]))
    obtain ⟨γ, δ, h⟩ := key d (rep_odd p hp2 d hpd)
    exact ⟨1, 0, γ, δ, by simp [h]⟩
  · rcases eq_or_ne p 2 with hp2 | hp2
    · subst hp2
      obtain ⟨α, β, h⟩ := key q (rep_two q hq8)
      exact ⟨α, β, 1, 0, by simp [h]⟩
    · have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
      obtain ⟨α, β, h⟩ := key q (rep_odd p hp2 q hpq')
      exact ⟨α, β, 1, 0, by simp [h]⟩
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
