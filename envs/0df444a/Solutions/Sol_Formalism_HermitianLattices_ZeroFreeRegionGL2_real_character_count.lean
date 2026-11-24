-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.real_character_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:46.062822+00:00
-- url     : https://prove2.me/submissions/c6ffd53a-ada8-4595-9462-3462ccb43467

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterEstimateOfHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
private lemma gl2b2_twoTors (e : ℕ) (he : 1 ≤ e) :
    (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0)).card = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hn : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  have hpos : 0 < 2 ^ k := by positivity
  have hlt : 2 ^ k < 2 ^ (k + 1) := by omega
  have hne : (0 : ZMod (2 ^ (k + 1))) ≠ ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
    intro h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at h2
    omega
  have hset : Finset.univ.filter (fun c : ZMod (2 ^ (k + 1)) => c + c = 0) =
      {0, ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hv := congrArg ZMod.val hc
      rw [ZMod.val_add, ZMod.val_zero] at hv
      have hcl := ZMod.val_lt c
      rw [← ZMod.natCast_zmod_val c]
      rcases Nat.lt_or_ge (c.val + c.val) (2 ^ (k + 1)) with h1 | h1
      · rw [Nat.mod_eq_of_lt h1] at hv
        left
        have : c.val = 0 := by omega
        rw [this, Nat.cast_zero]
      · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hv
        right
        have : c.val = 2 ^ k := by omega
        rw [this]
    · rintro (rfl | rfl)
      · simp
      · rw [← Nat.cast_add, ← hn, ZMod.natCast_self]
  rw [hset, Finset.card_pair hne]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.RealCharCount := by
  intro e he
  have : (Finset.univ.filter (fun g : ZMod 2 × ZMod 2 × ZMod (2 ^ e) => g + g = 0)) =
      (Finset.univ : Finset (ZMod 2)) ×ˢ ((Finset.univ : Finset (ZMod 2)) ×ˢ
        (Finset.univ.filter (fun c : ZMod (2 ^ e) => c + c = 0))) := by
    ext ⟨a, b, c⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, Prod.mk_add_mk, Prod.mk_eq_zero]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero b, h⟩
  rw [this, Finset.card_product, Finset.card_product, gl2b2_twoTors e he]
  simp
end Formalism.HermitianLattices.ZeroFreeRegionGL2
