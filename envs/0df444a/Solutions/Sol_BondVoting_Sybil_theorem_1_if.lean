-- Prove2me | solution 1 for BondVoting.Sybil.theorem_1_if
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:54:46.397192+00:00
-- url     : https://prove2.me/submissions/63bb891a-ce76-4152-897d-9b9b37a209dc

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model
set_option autoImplicit false

open BondVoting.Sybil

theorem solution (π : ℝ → ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hlin : ∀ t ∈ Set.Ioc 0 T, ∃ α β : ℝ, ∀ q : ℝ, 0 ≤ q → π q t = α + β * q)
    (h0 : ∀ t : ℝ, π 0 t = 0) (hq0 : ∀ q : ℝ, π q 0 = 0) :
    SybilResistant π T := by
  -- π q t = g t * q with g t = π 1 t
  have hg : ∀ t ∈ Set.Icc 0 T, ∀ q : ℝ, 0 ≤ q → π q t = π 1 t * q := by
    intro t ht q hq
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; simp [hq0]
    · obtain ⟨α, β, hab⟩ := hlin t ⟨h, ht.2⟩
      have ha : α = 0 := by have := hab 0 le_rfl; rw [h0] at this; linarith
      rw [hab q hq, hab 1 zero_le_one, ha]; ring
  intro q hq M qs ts
  rintro ⟨⟨hqs0, hqsum, hts⟩, hall⟩
  obtain ⟨tstar, hts_mem, hmax⟩ := Finset.exists_max_image (insert (0 : ℝ) (Finset.univ.image ts))
    (fun t => π 1 t) ⟨0, Finset.mem_insert_self _ _⟩
  have htT : tstar ∈ Set.Icc 0 T := by
    rcases Finset.mem_insert.mp hts_mem with h | h
    · subst h; exact ⟨le_rfl, hT.le⟩
    · obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨(hts m).1.le, (hts m).2⟩
  have h1 := hall tstar htT
  unfold attackPayoff at h1
  have hterm : ∀ m, π (qs m) (ts m) = π 1 (ts m) * qs m := fun m =>
    hg (ts m) ⟨(hts m).1.le, (hts m).2⟩ (qs m) (hqs0 m)
  have h0le : π 1 0 ≤ π 1 tstar := hmax 0 (Finset.mem_insert_self _ _)
  rw [hq0] at h0le
  have hsum : ∑ m, π (qs m) (ts m) ≤ π 1 tstar * q := by
    calc ∑ m, π (qs m) (ts m) = ∑ m, π 1 (ts m) * qs m := Finset.sum_congr rfl (fun m _ => hterm m)
      _ ≤ ∑ m, π 1 tstar * qs m := by
        apply Finset.sum_le_sum
        intro m _
        exact mul_le_mul_of_nonneg_right
          (hmax (ts m) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ m))))
          (hqs0 m)
      _ = π 1 tstar * ∑ m, qs m := by rw [Finset.mul_sum]
      _ ≤ π 1 tstar * q := mul_le_mul_of_nonneg_left hqsum h0le
  rw [hg tstar htT q hq.le] at h1
  linarith
