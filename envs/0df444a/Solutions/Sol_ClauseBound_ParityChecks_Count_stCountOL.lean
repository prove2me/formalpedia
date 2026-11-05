-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.stCountOL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:53:34.422619+00:00
-- url     : https://prove2.me/submissions/e31c76a6-99b1-4a6a-b05d-dfe503d2adab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_ClauseBound_ParityChecks_Count_count_core
import Theorems.Thm_ClauseBound_ParityChecks_Count_beta1_le
import Theorems.Thm_ClauseBound_ParityChecks_Count_beta0_eq_zero
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta1_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution (hE : StEvW) (hSh : StShape) (hB : StBridgeB) (hA : StBridgeA) (hF : StBridgeF) (H2 : ChoiceByPotential) : StCountOL := by
  intro Idx _ S ok hC k pad i n Δ ψ ε hok hK hW hocc hmΔ hnb hLD hH hFit
  have hnbn : nbOf n Δ ≤ n := Nat.div_le_self _ _
  by_cases hm : ψ.length ≤ nbOf n Δ
  · have e : parQ n Δ ψ.length = mkQ ψ (nbOf n Δ) 0 (i0Of n) (n + beta0 ψ.length (nbOf n Δ) + beta1 ψ.length (i0Of n) + 2) := by
      unfold parQ
      rw [if_pos hm]
      rfl
    rw [e]
    have h0 := beta0_eq_zero hm
    have h1 := beta1_le ψ.length (i0Of n)
    exact count_core hE hSh S ok hC k pad i n Δ ψ _ 0 _ _ hok hK hW hocc hmΔ hnb hLD (Nat.zero_le _) (by omega) hFit hB hA hF H2 ε (by omega) hnbn
      (Or.inl ⟨rfl, hm⟩)
  · obtain ⟨g1, g2, g3, g4⟩ := hH (not_le.1 hm)
    have e : parQ n Δ ψ.length = mkQ ψ (nbOf n Δ) (rOf n (beta0 ψ.length (nbOf n Δ))) (i0Of n)
        (n + beta0 ψ.length (nbOf n Δ) + beta1 ψ.length (i0Of n) + 2) := by
      unfold parQ
      rw [if_neg hm]
      rfl
    rw [e]
    have g2' : rOf n (beta0 ψ.length (nbOf n Δ)) ≤ 6 * n := g2
    have g3' : n + beta0 ψ.length (nbOf n Δ) + beta1 ψ.length (i0Of n) + 2 ≤ 5 * n := g3
    exact count_core hE hSh S ok hC k pad i n Δ ψ _ _ _ _ hok hK hW hocc hmΔ hnb hLD g2' (by omega) hFit hB hA hF H2 ε (by omega) hnbn (Or.inr ⟨g1, g4⟩)
end ClauseBound.ParityChecks.Count
