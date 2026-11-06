-- Prove2me | solution 1 for Eight.ViaGrouping.Correct.onFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:24:56.569375+00:00
-- url     : https://prove2.me/submissions/3de3002e-3ada-4344-b385-70a0cfc18a9b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Count
import Theorems.Thm_Eight_ViaGrouping_satNet_isNetworkP
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper
namespace Eight.ViaGrouping
namespace Correct
theorem _root_.solution {NA : NetAlg} {g K : ℕ} {ε b : ℝ} (hg : 0 < g) (k : ℕ) (h : Correct NA g K ε b) :
    ∃ C₁ : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (NA.app (satProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C₁ * (size Φ + satPf g k Φ + 1) ^ C₁) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (ε * ((wordNet g k Φ).U : ℝ) + b * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C₁ := by
  obtain ⟨C₁, hC₁⟩ := h
  refine ⟨C₁, fun Φ => ?_⟩
  obtain ⟨hN, hv, hU⟩ := satNet_isNetworkP hg k Φ
  obtain ⟨T, hrun, hT⟩ := hC₁ Fml (satProcs g k) Φ (satNet g k Φ) _ _ _ _ hN
  rw [hv] at hrun
  rw [hU, Nat.cast_one, mul_one] at hT
  exact ⟨T, hrun, hT⟩
end Correct
end Eight.ViaGrouping
