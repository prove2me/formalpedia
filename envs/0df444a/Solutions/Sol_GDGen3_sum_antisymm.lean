-- Prove2me | solution 1 for GDGen3.sum_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:47:50.279983+00:00
-- url     : https://prove2.me/submissions/39271051-0ea4-4778-b89b-4bc91b0231f4

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (F : ℕ → ℕ → ℝ) (s : Finset ℕ) :
    Finset.sum s (fun k => Finset.sum s (fun j => (F k j - F j k))) = 0 := by
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := s) (t := s)
        (f := fun a b => F b a)]
  simp
