-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.frob_pow_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:37:19.876102+00:00
-- url     : https://prove2.me/submissions/e3dd798c-1d7f-4f51-9623-6106a25e5198

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution {M : Type} [Field M] [NumberField M] (p : ℕ)
    (Q : Ideal (𝓞 M)) [Q.LiesOver (span {(p : ℤ)})] (F : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (k : ℕ) (x : 𝓞 M) :
    Ideal.Quotient.mk Q ((F ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (p ^ k) := by
  have hn : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ),
      Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have key : ∀ y : 𝓞 M, Ideal.Quotient.mk Q (F • y) = Ideal.Quotient.mk Q y ^ p := by
    intro y
    rw [← map_pow, Ideal.Quotient.eq, ← hn]
    exact hF y
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ' F k, mul_smul, key, ih, ← pow_mul, ← pow_succ p k]
end Formalism.FrobeniusOrbits.Decomp
