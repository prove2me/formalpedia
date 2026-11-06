-- Prove2me | solution 1 for Eight.Width.stExtend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:44.134018+00:00
-- url     : https://prove2.me/submissions/9cc4f324-a88c-4558-91cd-14876e9ad1f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_splitAll_extend
import Theorems.Thm_Eight_Width_splitAll_unique
import Theorems.Thm_Eight_Width_holds_dedup
import Theorems.Thm_Eight_Width_holds_lift
import Theorems.Thm_Eight_Width_numFresh_lift
import Theorems.Thm_Eight_Width_length_freshFin
import Theorems.Thm_Eight_Width_nodup_freshFin
import Theorems.Thm_Eight_Width_natAdd_mem_freshFin
import Theorems.Thm_Eight_Width_castAdd_notMem_freshFin
import Theorems.Thm_Eight_Width_lift_fresh

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution : StExtend := by
  intro n φ a ha
  have ha' : Holds (Fin.append a fun _ : Fin (numFresh φ) => false) (lift (numFresh φ) φ) := by
    rw [holds_lift]
    simpa using ha
  obtain ⟨b, hb, hH⟩ := splitAll_extend _ _ _ (nodup_freshFin n (numFresh φ)) (lift_fresh _ φ) ha'
  refine ⟨b, ⟨holds_dedup.2 hH, fun i => ?_⟩, ?_⟩
  · rw [hb _ (castAdd_notMem_freshFin n _ i)]
    simp
  · rintro b' ⟨hH', hb'⟩
    have hold : ∀ i, b' (Fin.castAdd (numFresh φ) i) = b (Fin.castAdd (numFresh φ) i) := by
      intro i
      rw [hb' i, hb _ (castAdd_notMem_freshFin n _ i)]
      simp
    funext v
    refine Fin.addCases hold (fun j => ?_) v
    refine splitAll_unique b' b (lift _ φ) (freshFin n _) (by rw [length_freshFin, numFresh_lift]) ?_ (holds_dedup.1 hH') hH _
      (natAdd_mem_freshFin n _ j)
    intro C hC l hl
    simp only [lift, List.mem_map] at hC
    obtain ⟨C', _, rfl⟩ := hC
    obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
    exact hold l'.1
end Eight.Width
