-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_finite_monotone_cuts_cover_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:53:14.430838+00:00
-- url     : https://prove2.me/submissions/80f195db-12e7-4345-804c-26bcab3e6618

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The first cut crossing a real level determines its predecessor cell. -/
theorem solution {n : ℕ} (p : Fin (n + 1) → ℝ) (z : ℝ)
    (hleft : p 0 < z) (hright : z ≤ p (Fin.last n)) :
    ∃ i : Fin n, z ∈ Ioc (p i.castSucc) (p i.succ) := by
  classical
  let s : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun j => z ≤ p j)
  have hs : s.Nonempty := by
    refine ⟨Fin.last n, ?_⟩
    simp [s, hright]
  let j : Fin (n + 1) := s.min' hs
  have hj : z ≤ p j := by
    exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hmin (k : Fin (n + 1)) (hk : z ≤ p k) : j ≤ k := by
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  have hjpos : 0 < j.val := by
    by_contra h
    have hjzero : j = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    rw [hjzero] at hj
    exact (not_le_of_gt hleft) hj
  let i : Fin n := ⟨j.val - 1, by
    have hjlt := j.isLt
    omega⟩
  have hisucc : i.succ = j := by
    apply Fin.ext
    dsimp [i]
    omega
  have hcastlt : i.castSucc < j := by
    apply Fin.lt_iff_val_lt_val.mpr
    dsimp [i]
    omega
  have hlt : p i.castSucc < z := by
    by_contra h
    have hz : z ≤ p i.castSucc := le_of_not_gt h
    have hbad := hmin i.castSucc hz
    exact (not_le_of_gt hcastlt) hbad
  refine ⟨i, hlt, ?_⟩
  simpa [hisucc] using hj
