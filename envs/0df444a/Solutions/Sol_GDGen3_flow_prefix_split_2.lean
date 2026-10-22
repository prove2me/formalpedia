-- Prove2me | solution 2 for GDGen3.flow_prefix_split
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:29:16.116047+00:00
-- url     : https://prove2.me/submissions/21529c3b-a6d1-4a78-837e-9aaef462473f

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_antisymm

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => d r ξ N k)
      = Finset.sum (Finset.range (i + 1))
          (fun k => Finset.sum (Finset.Icc (i + 1) N) (fun j => ell r ξ N k j - ell r ξ N j k)) := by
  have hsplit : ∀ k, d r ξ N k
      = Finset.sum (Finset.range (i + 1)) (fun j => ell r ξ N k j - ell r ξ N j k)
        + Finset.sum (Finset.Icc (i + 1) N) (fun j => ell r ξ N k j - ell r ξ N j k) := by
    intro k
    have hN : Finset.range (i + 1) ∪ Finset.Icc (i + 1) N = Finset.range (N + 1) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.range (i + 1)) (Finset.Icc (i + 1) N) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc] at hx'
      omega
    show Finset.sum (Finset.range (N + 1)) _ = _
    rw [← hN, Finset.sum_union hdisj]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [sum_antisymm (fun k j => ell r ξ N k j) (Finset.range (i + 1)), zero_add]
