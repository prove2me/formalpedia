-- Prove2me | solution 1 for Formalism.L2.NCov.val_prime_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:14.390143+00:00
-- url     : https://prove2.me/submissions/f08859b8-6193-4389-b2e6-b88d2a4e454a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverVal
import Theorems.Thm_Formalism_L2_NCov_nonneg_of_isIntegral
import Theorems.Thm_Formalism_L2_NCov_withTop_add_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Polynomial
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
namespace Formalism.L2.NCov
theorem _root_.solution {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : p ≠ l) (hvl : 0 < v (l : F)) :
    v (p : F) = 0 := by
  have hI : ∀ a : ℤ, 0 ≤ v (a : F) := fun a =>
    nonneg_of_isIntegral v (by simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := a)))
  have hp0 : 0 ≤ v (p : F) := by simpa using hI p

  have hcop : IsCoprime (p : ℤ) (l : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hl).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have hF : (a : F) * (p : F) + (b : F) * (l : F) = 1 := by
    have := congrArg (fun z : ℤ => (z : F)) hab
    push_cast at this
    exact this
  by_contra hne0
  have hpos : 0 < v (p : F) := lt_of_le_of_ne hp0 (Ne.symm hne0)
  have h1 : 0 < v ((a : F) * (p : F)) := by
    rw [AddValuation.map_mul]; exact withTop_add_pos (hI a) hpos
  have h2 : 0 < v ((b : F) * (l : F)) := by
    rw [AddValuation.map_mul]; exact withTop_add_pos (hI b) hvl
  have h3 := lt_of_lt_of_le (lt_min h1 h2) (v.map_add _ _)
  rw [hF, AddValuation.map_one] at h3
  exact lt_irrefl _ h3
end Formalism.L2.NCov
