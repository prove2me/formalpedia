-- Prove2me | solution 1 for Bagaria.no_extendible_below_least_berkeley
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:31:30.925629+00:00
-- url     : https://prove2.me/submissions/3cb4d742-3784-487d-8fcf-c86f1b58e11f

import Mathlib
import Definitions.Def_Bagaria_arena
import Definitions.Def_Bagaria_reinhardt
import Definitions.Def_Bagaria_berkeley
universe v

open Bagaria Bagaria.Universe

theorem solution (U : Universe.{v}) (hZF : SatisfiesZF U.mem)
    (δ0 : Ordinal.{v}) (hB : U.berkeley δ0)
    (hL : ∀ δ : Ordinal.{v}, δ < δ0 → ¬ U.berkeley δ) :
    ∀ κ : Ordinal.{v}, κ ≤ δ0 → ¬ U.isExtendible κ := by
  have hB0 : U.berkeley 0 := by
    intro M _ _ η hη
    exact (not_lt_zero hη).elim
  have hδ0 : δ0 = 0 := by
    by_contra h
    exact hL 0 ((pos_iff_ne_zero.mpr h)) hB0
  intro κ hκ hext
  have hκ0 : κ = 0 := le_antisymm (hδ0 ▸ hκ) (zero_le)
  subst hκ0
  obtain ⟨β, j, hj, ⟨h01, hne, -⟩, -⟩ := hext 1 zero_lt_one
  apply hne
  -- ord 0 has no members in U
  have hord0 : ∀ z, ¬ U.mem z (U.ord 0) := by
    intro z hz
    have := U.mem_rank z _ hz
    rw [U.rank_ord] at this
    exact not_lt_zero this
  -- in segment 1, the code of 0 has no members
  have h1 : holds (U.segmentMem 1) (fun _ => U.segOrd 1 0 h01) (.not (.ex (.mem 0 1))) := by
    simp only [holds, not_exists]
    intro x hx
    exact hord0 x.val hx
  have h2 := (hj _ _).mp h1
  simp only [holds, not_exists] at h2
  have hjm : ∀ z, ¬ U.mem z (j (U.segOrd 1 0 h01)).val := by
    intro z hz
    have hr : U.rank z < β :=
      lt_trans (U.mem_rank z _ hz) (j (U.segOrd 1 0 h01)).property
    exact h2 ⟨z, hr⟩ hz
  exact hZF.1 _ _ fun z => ⟨fun h => absurd h (hjm z), fun h => absurd h (hord0 z)⟩
