-- Prove2me | solution 1 for Eight.ViaGrouping.levelNetP_isNetworkP_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:56.378194+00:00
-- url     : https://prove2.me/submissions/05f81270-5a01-4cc6-b10a-4f9f53e5722e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_P2M_Eight_ViaGrouping_lvlPsi_netOf__runs_ab9065b5caad
import Theorems.Thm_Eight_ViaGrouping_isNetworkP_ofNetwork
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_P2M_Eight_Level_netOf__sized_t_6d348568ee7d
import Theorems.Thm_Paper_Achievable_mono


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (hPr : StPresents) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, 1 ≤ a ∧ ∀ (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ), StPsiOK g tr psi →
    ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr psi lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * tOf (lam c) + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by
  obtain ⟨ar, har⟩ := hPr g false
  obtain ⟨ac, hac⟩ := hPr g true
  obtain ⟨a, ha⟩ : ∃ a, a = ar + ac + 1 + lvlPsiSize g := ⟨_, rfl⟩
  refine ⟨a, by omega, fun tr psi hΨ C _ lam R c B t S Rm y hl ht hy hR => ?_⟩
  have hmono : ∀ a' X : ℕ, a' ≤ a → 1 ≤ X → a' * X ^ a' ≤ a * X ^ a := fun a' X h1 h2 => Nat.mul_le_mul h1 (Nat.pow_le_pow_right h2 h1)
  have hP1 : 1 ≤ g ^ 3 * lam c := Nat.mul_pos (pow_pos hg 3) hl
  have ht1 : 1 ≤ a * (B + lam c) ^ a * t := Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos (by omega) a)) ht
  have hBd : BoundedInst (lam c) B Rm := fun v θ h1 h2 => (hR v θ h1 h2).2
  have hpres : (levelNet g tr lam R).Presents (c, y) (netOfι g tr (lam c) y Rm) (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a) := by
    cases tr
    · exact (har C lam R c B t S Rm y hl ht hy hR).mono (Nat.mul_le_mul_right _ (hmono ar _ (by omega) (by omega))) (Nat.add_le_add_left (hmono ar _ (by omega) (by omega)) _)
    · exact (hac C lam R c B t S Rm y hl ht hy hR).mono (Nat.mul_le_mul_right _ (hmono ac _ (by omega) (by omega))) (Nat.add_le_add_left (hmono ac _ (by omega) (by omega)) _)
  have hSΨ : lvlPsiSize g * (size c + B + lam c) ≤ S + a * (size c + B + lam c) ^ a :=
    le_trans (Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) _)) (Nat.le_add_left _ _)
  have h := isNetworkP_ofNetwork (Np := levelNet g tr lam R) (Pf := fun c : C × ℕ => g ^ 3 * lam c.1) (Q := ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2)
    hP1 ht1 ⟨netOfι_sized_t hl g tr y hBd, hpres⟩ rfl
    fun a b hab z hz z' hz' => (lvlPsi_netOfι_runs hΨ lam c hl hy hBd a b hab hz hz').mono ht1 hSΨ
  have hlen : (fun a : Fin (nParts g g tr) => (levelNet g tr lam R).n (c, y) a) = fun _ => g ^ 3 * lam c := by
    funext _
    change nMemb g g tr * (g * g) * lam c = g ^ 3 * lam c
    have : nMemb g g tr = g := by cases tr <;> rfl
    rw [this]
    ring
  rw [hlen] at h
  exact h
end Eight.ViaGrouping
