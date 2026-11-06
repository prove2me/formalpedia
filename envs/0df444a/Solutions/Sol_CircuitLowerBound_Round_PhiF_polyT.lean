-- Prove2me | solution 1 for CircuitLowerBound.Round.PhiF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:46:41.071403+00:00
-- url     : https://prove2.me/submissions/5f74aea0-6fd7-4102-8454-fa747cad4520

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}
variable {α : Type} [Enc α]
namespace CircuitLowerBound.Round
theorem _root_.solution (h1 : StCertSched) (hG : PolyT G) (hfb : PolyT fb) {u pad : α → List Unit} (hu : PolyT u) (hp : PolyT pad) :
    PolyT fun x => PhiF G fb (u x) (pad x) := by
  obtain ⟨s1, s2, -, s4, s5, s6⟩ := h1
  have c1 : PolyT fun x => codeOf (nu (u x).length) :=
    PolyT.comp (f := fun v : List Unit => codeOf (nu v.length)) (g := u) s1 hu
  have c2 : PolyT fun x => next (u x).length := PolyT.comp (f := fun v : List Unit => next v.length) (g := u) s2 hu
  have c4 : PolyT fun x => decide (pos (u x).length < top (nu (u x).length)) :=
    PolyT.comp (f := fun v : List Unit => decide (pos v.length < top (nu v.length))) (g := u) s4 hu
  have c5 : PolyT fun x => decide (pos (u x).length = top (nu (u x).length)) :=
    PolyT.comp (f := fun v : List Unit => decide (pos v.length = top (nu v.length))) (g := u) s5 hu
  have c6 : PolyT fun x => decide (Fits (codeOf (nu (u x).length)) (u x).length (next (u x).length)) :=
    PolyT.comp (f := fun p : MCode × List Unit × ℕ => decide (Fits p.1 p.2.1.length p.2.2))
      (g := fun x => (codeOf (nu (u x).length), u x, next (u x).length)) s6 (PolyT.prodMk c1 (PolyT.prodMk hu c2))
  have c7 : PolyT fun x => G ((codeOf (nu (u x).length), u x, next (u x).length), pad x) :=
    PolyT.comp (f := G) (g := fun x => ((codeOf (nu (u x).length), u x, next (u x).length), pad x)) hG
      (PolyT.prodMk (PolyT.prodMk c1 (PolyT.prodMk hu c2)) hp)
  have c8 : PolyT fun x => fb (u x) := PolyT.comp (f := fb) (g := u) hfb hu
  unfold PhiF
  exact PolyT.cond' c4 (PolyT.cond' c6 c7 (PolyT.const [])) (PolyT.cond' c5 (PolyT.cond' c8 (PolyT.const [[]]) (PolyT.const [])) (PolyT.const []))
end CircuitLowerBound.Round
