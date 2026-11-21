-- Prove2me | solution 1 for BehrendWindows.exists_atMostTwoPerAP_of_box
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:54:09.817893+00:00
-- url     : https://prove2.me/submissions/4c7f3d86-7bcc-4cea-9ee9-5d44c3f2f26e

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP
import Theorems.Thm_BehrendWindows_atMostTwoPerAP_image_sphere

open BehrendWindows

theorem solution (S d m : ℕ) (hS : 1 ≤ S) (hd : 1 ≤ d) (hm : 3 ≤ m) :
    ∃ T : Finset ℤ, T ⊆ Finset.Ico (0 : ℤ) ((m * d) ^ S : ℕ) ∧ AtMostTwoPerAP T m ∧
      (d : ℝ) ^ S / (S * (d : ℝ) ^ 2) ≤ (T.card : ℝ) := by
  obtain ⟨k, hk⟩ := Behrend.exists_large_sphere S d
  obtain ⟨hsparse, hsub⟩ := atMostTwoPerAP_image_sphere S d m k hd hm
  refine ⟨_, hsub, hsparse, ?_⟩
  have hinj : Set.InjOn (fun x : Fin S → ℕ => (Behrend.map (m * d) x : ℤ))
      (Behrend.sphere S d k : Set (Fin S → ℕ)) := by
    intro x hx y hy hxy
    have hlt : ∀ z ∈ Behrend.sphere S d k, ∀ i, z i < m * d := fun z hz i =>
      lt_of_lt_of_le (Behrend.mem_box.1 (Behrend.sphere_subset_box hz) i)
        (Nat.le_mul_of_pos_left d (by omega))
    exact Behrend.map_injOn (hlt x hx) (hlt y hy) (Int.ofNat_inj.1 hxy)
  rw [Finset.card_image_of_injOn hinj]
  simpa using hk
