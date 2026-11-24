-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.card_residues_le_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:39.575517+00:00
-- url     : https://prove2.me/submissions/644f06d0-084d-4413-85d1-4f4b2fa0bc3e

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution (n D : ℕ) [NeZero n] (hD : 0 < D) :
    ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{u : (ZMod n)ˣ | u ^ D = 1} := by
  classical
  have step1 : ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{y : ZMod n | y ^ D = 1} := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ => (x : ZMod n))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      have := (ZMod.natCast_eq_natCast_iff (x ^ D) 1 n).2 hx.2
      push_cast at this
      exact this
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx hy
      have h := congrArg ZMod.val hxy
      simp only [ZMod.val_natCast] at h
      rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  refine step1.trans ?_
  have hsub : ({y : ZMod n | y ^ D = 1} : Finset (ZMod n)) ⊆
      Finset.image (fun u : (ZMod n)ˣ => (u : ZMod n))
        (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ D = 1)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : y * y ^ (D - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hD, hy]
    refine ⟨⟨y, y ^ (D - 1), h1, by rw [mul_comm]; exact h1⟩, ?_, rfl⟩
    ext; simpa using hy
  exact (Finset.card_le_card hsub).trans Finset.card_image_le
end Formalism.GaloisIrreducibility
