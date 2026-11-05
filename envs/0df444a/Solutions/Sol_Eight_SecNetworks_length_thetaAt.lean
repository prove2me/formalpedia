-- Prove2me | solution 1 for Eight.SecNetworks.length_thetaAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:28:26.33621+00:00
-- url     : https://prove2.me/submissions/eb2e869f-85ac-4953-813e-16c3a579e8dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_lAt_eq_cut
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_eq
import Theorems.Thm_Groundwork_Prog_NetE_mem_prsF
import Theorems.Thm_Groundwork_length_cut_of_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution (Np : NetworkProcedures C) {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ} (hK0 : 0 < K) (hN : Paper.IsNetwork Np c N P B τ S)
    (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → (N.merge (grouping hK0 x) [] []).c γ γ' ≤ L) (Θ : Fin K → List Bool) {a b : Fin g}
    (hne : grouping hK0 x a ≠ grouping hK0 x b) (hΘ : (Θ (grouping hK0 x b)).length = L) : (thetaAt Np c hK0 x Θ a b).length = N.c a b := by
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  have key : ∀ (G G' : Fin K) (p : Fin g × Fin g), G ≠ G' → grouping hK0 x p.1 = G → grouping hK0 x p.2 = G' →
      (mdec K g Np c x G G' (Θ (grouping hK0 x b)) p).length = Np.cap c p.1.val p.2.val := by
    intro G G' p hG h1 h2
    change (lAt K g Np c x G G' (Θ (grouping hK0 x b)) (p.1.val, p.2.val)).length = _
    rw [lAt_eq_cut]
    refine length_cut_of_le (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] _ _ ?_ ?_
    · rw [← lbLens_eq, hΘ]
      change lbLen K g Np c x G.val G'.val ≤ L
      rw [lbLen_eq Np hK0 hN.presented x hG]
      exact hL G G' hG
    · rw [mem_prsF]
      exact ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩
  unfold thetaAt
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, if_pos h, key _ _ (a, b) hne rfl rfl]
    exact (hN.presented.c_eq a b hab).symm
  · rw [min_eq_right h.le, max_eq_left h.le, if_neg h.not_gt, key _ _ (b, a) hne.symm rfl rfl, hN.sized.c_symm a b]
    exact (hN.presented.c_eq b a hab.symm).symm
end Eight.SecNetworks
