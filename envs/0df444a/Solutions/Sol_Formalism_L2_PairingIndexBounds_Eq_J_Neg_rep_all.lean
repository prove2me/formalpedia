-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:44.692797+00:00
-- url     : https://prove2.me/submissions/c7c37f45-14ad-48e9-9013-527864754c88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_pp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
private theorem rep_mul_of_coprime {q d a b : ℕ} (hab : Nat.Coprime a b)
    (ha : Rep q d a) (hb : Rep q d b) :
    Rep q d (a * b) := by
  obtain ⟨α₁, β₁, γ₁, δ₁, h₁⟩ := ha
  obtain ⟨α₂, β₂, γ₂, δ₂, h₂⟩ := hb
  let e := ZMod.chineseRemainder hab
  refine ⟨e.symm (α₁, α₂), e.symm (β₁, β₂), e.symm (γ₁, γ₂), e.symm (δ₁, δ₂), e.injective ?_⟩
  simp only [map_mul, map_add, map_pow, map_natCast, map_neg, map_one,
    RingEquiv.apply_symm_apply]
  ext <;> simp [h₁, h₂]
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
end

set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
theorem _root_.solution (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) :
    0 < m → Rep q d m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact fun _ => rep_pp q d hq hd hq8 hqd p n hp
  | zero => exact fun h => absurd h (lt_irrefl 0)
  | one =>
    intro _
    simpa using rep_pp q d hq hd hq8 hqd 2 0 Nat.prime_two
  | coprime a b ha1 hb1 hab ha hb =>
    exact fun _ => rep_mul_of_coprime hab (ha (by omega)) (hb (by omega))
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
