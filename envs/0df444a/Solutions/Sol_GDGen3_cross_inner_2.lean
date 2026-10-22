-- Prove2me | solution 2 for GDGen3.cross_inner
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:30:55.421987+00:00
-- url     : https://prove2.me/submissions/d7b5804b-eb9a-4d71-9068-ee265a127b51

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_am_telescope
import Theorems.Thm_GDGen3_am_telescope2

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (ξ : ℕ → ℝ) (N i j : ℕ)
    (h0 : ξ 0 = 0) (hne : ∀ i : ℕ, i ≠ 0 → ξ i ≠ 0)
    (hij : i < j) (hjN : j ≤ N) :
    Finset.sum (Finset.range (i + 1)) (fun k => ell r ξ N k j - ell r ξ N j k)
      = (D r ξ N j + r * D r ξ N (j + 1)) * Abar ξ i
        - (D r ξ N j - D r ξ N (j + 1))
          * ((Finset.sum (Finset.range i) (fun k => Abar ξ k))
              + r * Abar ξ i
              + r * (Finset.sum (Finset.range i) (fun k => Abar ξ k))) := by
  have hterm : ∀ k ∈ Finset.range (i + 1),
      ell r ξ N k j - ell r ξ N j k
        = (Abar ξ k - Am ξ k) * (D r ξ N j + r * D r ξ N (j + 1))
          - (Am ξ k + r * Abar ξ k) * (D r ξ N j - D r ξ N (j + 1)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkj : k < j := by omega
    have hjk : ¬ (j < k) := by omega
    simp only [ell, if_pos hkj, if_neg hjk]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    am_telescope ξ i, am_telescope2 ξ h0 r i]
  ring
