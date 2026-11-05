-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.stShape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:54:21.156204+00:00
-- url     : https://prove2.me/submissions/91f19eef-b7de-4439-8a39-7f6736b2bb5c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_shape_core
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution : StShape := by
  intro k n Δ q ψ Lam j e hm hnb h3 hr hn hψ hocc hj hL hT
  have hnb1 : 1 ≤ q.nb := by omega
  have h4 : q.m ≤ 2 * Δ * LD Δ * q.nb := by
    calc q.m ≤ Δ * n := h3
      _ ≤ Δ * (2 * (q.nb * LD Δ)) := Nat.mul_le_mul_left _ hn.le
      _ = 2 * Δ * LD Δ * q.nb := by ring
  obtain ⟨a, b, c⟩ := shape_core hm hnb1 h3 h4 hψ hocc hj hL hT e
  refine ⟨a, fun v => (b v).trans ?_, c⟩
  have c1 : Nat.clog 2 (16 * q.m) ≤ Nat.clog 2 (16 * Δ * n) := Nat.clog_mono_right 2 (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h3)
  have c2 : Nat.clog 2 (16 * q.r) ≤ Nat.clog 2 (96 * n) := Nat.clog_mono_right 2 (by omega)
  have c3 : 3 * q.r / (2 * q.nb) ≤ 18 * LD Δ := by
    refine Nat.div_le_of_le_mul ?_
    calc 3 * q.r ≤ 18 * n := by omega
      _ ≤ 18 * (2 * (q.nb * LD Δ)) := Nat.mul_le_mul_left _ hn.le
      _ = 2 * q.nb * (18 * LD Δ) := by ring
  have c4 : 3 * q.m / (2 * q.nb) ≤ 3 * Δ * LD Δ := by
    refine Nat.div_le_of_le_mul ?_
    calc 3 * q.m ≤ 3 * (2 * Δ * LD Δ * q.nb) := Nat.mul_le_mul_left _ h4
      _ = 2 * q.nb * (3 * Δ * LD Δ) := by ring
  unfold occOL colMax rowMax
  exact max_le_max (Nat.mul_le_mul_left _ (by omega)) (by omega)
end ClauseBound.ParityChecks.Shape
