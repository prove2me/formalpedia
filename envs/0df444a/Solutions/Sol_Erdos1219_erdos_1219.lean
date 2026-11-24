-- Prove2me | solution 1 for Erdos1219.erdos_1219
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:53:28.824814+00:00
-- url     : https://prove2.me/submissions/7e5181ad-7e44-49d1-a785-6e75352ead4d

import Definitions.Def_Erdos1219_Canonization
import Definitions.Def_Erdos1219_Main
import Theorems.Thm_Erdos1219_core
import Theorems.Thm_Erdos1219_ofFinsetColouring_apply
import Theorems.Thm_Erdos1219_ofFinsetColouring_symm


set_option autoImplicit false
open Cardinal Ordinal
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) := by
  intro A hA col
  obtain ⟨c, H, hH, hom⟩ :=
    core (ofFinsetColouring col) (ofFinsetColouring_symm col) n hn hpow h0 hA
  refine ⟨c, H, hH, ?_⟩
  intro s hs hsH
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
  have hx : x ∈ H := hsH (by simp)
  have hy : y ∈ H := hsH (by simp)
  have := hom x hx y hy hxy
  rw [ofFinsetColouring_apply col hxy] at this
  exact this
end Erdos1219
