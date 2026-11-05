-- Prove2me | solution 1 for Eight.Level.Presents.presentsP8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:21.724778+00:00
-- url     : https://prove2.me/submissions/a745cb6d-aa57-488c-b553-f23863e718b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Presents
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Presents
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_S
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c_le
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_lab
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_sized
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_sideWP_runs
import Theorems.Thm_Groundwork_Prog_side_size_W
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_SingleBitPieces_Level_Presents_W_eq
import Theorems.Thm_SingleBitPieces_Level_Presents_f_eq
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self
import Theorems.Thm_SingleBitPieces_Level_Presents_nParts_self
import Theorems.Thm_SingleBitPieces_Level_Presents_size_f
import Theorems.Thm_SingleBitPieces_Level_Presents_time_W
import Theorems.Thm_SingleBitPieces_Level_Presents_time_f
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped SingleBitPieces.Level.Presents
open Eight.Level.Presents
namespace Eight.Level.Presents
theorem _root_.solution (P : PiecesF) (hm : P.m = 1) (hbits : ∀ ℓ, P.bits 0 ℓ ≤ 2 * ℓ) (g : ℕ) (tr : Bool) {C : Type} [HasSize C] (lam : C → ℕ)
    (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {A : ℕ → Pieces.Four (lam c)}
    (hcuts : CutsOK P [] 0 (lam c) A) (hl : 1 ≤ lam c) (ht : 1 ≤ t) (hy : y < (lam c + 1) ^ nRect g) (hR : ServesInst R c (lam c) B t S Rm) :
    (netP8 P g tr lam R).Presents (c, y) (gridN P [] g g tr 0 (lam c) y Rm) (sideA g * (B + lam c) ^ sideA g * t)
      (S + sideA g * (size c + B + lam c) ^ sideA g) := by
  have hB : BoundedInst (lam c) B Rm := fun v θ h1 h2 => (hR v θ h1 h2).2
  have hlen : ∀ z : List Bool, z.length = nMemb g g tr * (g * g) * lam c → z.length = g ^ 3 * lam c := by
    intro z hz
    rw [hz, nMemb_self]
    ring
  refine ⟨fun a => gridN_S _ _ _ _ _ _ _ _ _ a, fun a b hab => gridN_c _ _ _ _ _ _ _ _ _ hab, fun a b hab => gridN_lab _ _ _ _ _ _ _ _ _ hab,
    fun a z hz => ?_, fun a b z θ hab hz hθ => ?_⟩
  · have hz' : z.length = nMemb g g tr * (g * g) * lam c := hz
    have ha : a.val < g := lt_of_lt_of_eq a.2 (nParts_self g tr)
    rw [W_eq P tr lam Rm c y a hz']
    exact (sideWP_runs hR y ha (hlen z hz')).mono (time_W g B (lam c) hl ht) (side_size_W g B S (lam c) hl c hy ha (hlen z hz'))
  · have hz' : z.length = nMemb g g tr * (g * g) * lam c := hz
    have hθ' : θ.length = capG P g g tr 0 (lam c) y a b := hθ
    have ha : a.val < g := lt_of_lt_of_eq a.2 (nParts_self g tr)
    have hb : b.val < g := lt_of_lt_of_eq b.2 (nParts_self g tr)
    have hθl : θ.length ≤ g ^ 2 * lam c := by
      have h1 := gridN_c_le hcuts g g tr y Rm a b
      rw [gridN_c _ _ _ _ _ _ _ _ _ hab, nMemb_self, hm, Nat.one_mul] at h1
      rw [hθ']
      exact h1
    have hv : |(gridN P [] g g tr 0 (lam c) y Rm).f a b z θ| ≤ 2 ^ (g * B + g ^ 2 * (2 * lam c)) := by
      have h1 := (gridN_sized hcuts g g tr y hB).abs_f a b z θ
      rw [nMemb_self] at h1
      exact h1.trans (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hbits _)) _))
    have hrun : (ofFun fun x : (C × ℕ) × FQ => gridFf P [] g g tr 0 (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a.val, b.val), (z, θ))) 1
        (max (size ((c, y), ((a.val, b.val), (z, θ)))) (size (gridFf P [] g g tr 0 (lam c) y ((a.val, b.val), (z, θ)))) + 1)
        (gridFf P [] g g tr 0 (lam c) y ((a.val, b.val), (z, θ))) :=
      ofFun_runs (fun x : (C × ℕ) × FQ => gridFf P [] g g tr 0 (lam x.1.1) x.1.2 x.2) ((c, y), ((a.val, b.val), (z, θ)))
    rw [f_eq P tr (lam c) y Rm hab hz' hθ'] at hrun
    exact hrun.mono (time_f g B (lam c) hl ht) (size_f g B S (lam c) hl c hy ha hb (hlen z hz') hθl hv)
end Eight.Level.Presents
