-- Prove2me | solution 1 for Erdos9796Mission.erase_failure_iff_unique_critical_radius
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-09-12T04:59:25.830407+00:00
-- url     : https://prove2.me/submissions/5535b917-d0bc-4935-8c7b-2e0cb90d2a22

import Definitions.Def_Erdos9796Mission

open Erdos9796Mission
open Classical

/-- Deleting one witness destroys richness exactly at a unique, tight radius. -/
theorem solution (n : ℕ) (A : Finset Plane) (p x : Plane)
    (hx : x ∈ A) (hp : HasNEquidistantPointsAt n A p) :
    (¬ HasNEquidistantPointsAt n (A.erase x) p) ↔
      ∃ r : ℝ, 0 < r ∧ dist p x = r ∧
        (A.filter (fun q => dist p q = r)).card = n ∧
        ∀ s : ℝ, 0 < s →
          n ≤ (A.filter (fun q => dist p q = s)).card → s = r := by
  classical
  have herase (r : ℝ) :
      (A.erase x).filter (fun q => dist p q = r) =
        (A.filter (fun q => dist p q = r)).erase x := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  constructor
  · intro hfailure
    have hsmall (s : ℝ) (hs : 0 < s) :
        ((A.erase x).filter (fun q => dist p q = s)).card < n := by
      by_contra hnot
      exact hfailure ⟨s, hs, by omega⟩
    have hthrough (s : ℝ) (hs : 0 < s)
        (hlarge : n ≤ (A.filter (fun q => dist p q = s)).card) :
        dist p x = s := by
      by_contra hdist
      have hxnot : x ∉ A.filter (fun q => dist p q = s) := by
        simp [hdist]
      have hsame : (A.erase x).filter (fun q => dist p q = s) =
          A.filter (fun q => dist p q = s) := by
        rw [herase s, Finset.erase_eq_of_notMem hxnot]
      have hlt := hsmall s hs
      rw [hsame] at hlt
      omega
    obtain ⟨r, hr, hlarge⟩ := hp
    have hxr := hthrough r hr hlarge
    have hxrow : x ∈ A.filter (fun q => dist p q = r) :=
      Finset.mem_filter.mpr ⟨hx, hxr⟩
    have hcount := Finset.card_erase_add_one hxrow
    have hlt := hsmall r hr
    rw [herase r] at hlt
    refine ⟨r, hr, hxr, by omega, ?_⟩
    intro s hs hlarge_s
    exact (hthrough s hs hlarge_s).symm.trans hxr
  · rintro ⟨r, hr, hxr, hcount, hunique⟩ ⟨s, hs, hlarge⟩
    have hsub : (A.erase x).filter (fun q => dist p q = s) ⊆
        A.filter (fun q => dist p q = s) := by
      intro q hq
      obtain ⟨hq, hdist⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hq, hdist⟩
    have hsr := hunique s hs (hlarge.trans (Finset.card_le_card hsub))
    subst s
    have hxrow : x ∈ A.filter (fun q => dist p q = r) :=
      Finset.mem_filter.mpr ⟨hx, hxr⟩
    have hcount_erase := Finset.card_erase_add_one hxrow
    rw [herase r] at hlarge
    omega
