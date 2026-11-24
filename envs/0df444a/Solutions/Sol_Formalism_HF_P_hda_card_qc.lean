-- Prove2me | solution 1 for Formalism.HF.P.hda_card_qc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:00.071752+00:00
-- url     : https://prove2.me/submissions/9387e282-0d54-4650-b3c3-f97f38c31bbf

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (e : ℤ) (he : e = 1 ∨ e = -1) :
    2 * (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = e)).card = p - 1 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have key : ∀ y : ZMod p, quadraticChar (ZMod p) y = 0 ∨ quadraticChar (ZMod p) y = 1 ∨
      quadraticChar (ZMod p) y = -1 := by
    intro y
    by_cases hy : y = 0
    · left; rw [hy]; exact MulChar.map_zero _
    · right; exact quadraticChar_dichotomy hy
  have hsum : ((univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card : ℤ) -
      (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = 0 := by
    have h0 := quadraticChar_sum_zero hF
    have : ∀ y : ZMod p, quadraticChar (ZMod p) y =
        (if quadraticChar (ZMod p) y = 1 then 1 else 0) -
          (if quadraticChar (ZMod p) y = -1 then 1 else 0) := by
      intro y; rcases key y with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_sub_distrib] at h0
    rw [Finset.card_filter, Finset.card_filter]; push_cast; exact h0
  have htot : (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = 1)).card +
      (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = -1)).card = p - 1 := by
    have : ∀ y : ZMod p, ((if quadraticChar (ZMod p) y = 1 then 1 else 0) +
        (if quadraticChar (ZMod p) y = -1 then 1 else 0) : ℕ) = (if y ≠ 0 then 1 else 0 : ℕ) := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      · rcases quadraticChar_dichotomy hy with h | h <;> simp [h, hy]
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun y _ => this y), ← Finset.card_filter, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rcases he with rfl | rfl <;> omega
end Formalism.HF.P
