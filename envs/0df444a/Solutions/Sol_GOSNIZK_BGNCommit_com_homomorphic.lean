-- Prove2me | solution 1 for GOSNIZK.BGNCommit.com_homomorphic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:51.563687+00:00
-- url     : https://prove2.me/submissions/3f3176ec-52f0-4e06-be5e-8fe83f6a479e

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

set_option autoImplicit false
open GOSNIZK.BGNCommit

theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x)
    (m₁ r₁ m₂ r₂ : ZMod S.n) :
    S.com h (m₁ + m₂) (r₁ + r₂) = S.com h m₁ r₁ * S.com h m₂ r₂ := by
  have key : ∀ x : G, ∀ a b : ZMod S.n, x ^ (a + b).val = x ^ a.val * x ^ b.val := by
    intro x a b
    rw [ZMod.val_add, ← pow_add]
    have : x ^ S.n = 1 := by
      show x ^ (S.p * S.q) = 1
      rw [← S.card_G]; exact pow_card_eq_one
    exact (pow_eq_pow_mod _ this).symm
  unfold BGNSetup.com
  rw [key S.g, key h]
  exact mul_mul_mul_comm _ _ _ _
