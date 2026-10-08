-- Prove2me | solution 1 for Erdos3.szemeredi_positive_upper_density
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:25:32.456978+00:00
-- url     : https://prove2.me/submissions/65de041c-6e0f-4dbc-954e-76d2bb695bbc

import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos142_erdos_139_szemeredi
import Mathlib

open Erdos142

theorem solution (A : Set ℕ)
    (hA : ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N : ℕ in Filter.atTop, δ * N ≤ ((A ∩ Set.Iio N).ncard : ℝ)) :
    ∀ k : ℕ, ∃ S ⊆ A, IsAPOfLength S k := by
  classical
  obtain ⟨δ, hδ, hfreq⟩ := hA
  intro k
  by_contra hno
  push Not at hno
  -- A is nonempty, since it has positive upper density.
  have hne : A.Nonempty := by
    obtain ⟨N, hN, hNpos⟩ := (hfreq.and_eventually (Filter.eventually_gt_atTop 0)).exists
    have hpos : (0 : ℝ) < δ * N := by
      have : (0 : ℝ) < N := by exact_mod_cast hNpos
      positivity
    have hcard : (A ∩ Set.Iio N).ncard ≠ 0 := by
      intro h0
      rw [h0] at hN
      simp at hN
      linarith
    obtain ⟨a, ha, -⟩ := Set.nonempty_of_ncard_ne_zero hcard
    exact ⟨a, ha⟩
  -- Lengths 0 and 1 are trivial.
  have hk : 2 ≤ k := by
    by_contra hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · exact hno ∅ (Set.empty_subset _) ⟨0, 0, by simp [ENat.card], by simp⟩
    · obtain ⟨a, ha⟩ := hne
      refine hno {a} (by simpa using ha) ⟨a, 0, ?_, ?_⟩
      · simp
      · ext x
        simp
  -- Szemerédi: r_k(N) = o(N).
  have hlim := erdos_139_szemeredi k (by omega)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (r k N : ℝ) / N < δ / 2 :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN, hrN, hNM⟩ :=
    (hfreq.and_eventually (hev.and (Filter.eventually_ge_atTop (⌈2 / δ⌉₊ + 1)))).exists
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  -- Counting: |A ∩ [0, N)| ≤ 1 + r_k(N).
  set T : Finset ℕ := (Finset.Icc 1 N).filter (· ∈ A) with hT
  have hTfree : IsAPOfLengthFree (T : Set ℕ) k := by
    intro t ht hap
    exact absurd hap (hno t (fun x hx => (Finset.mem_filter.mp (Finset.mem_coe.mp (ht hx))).2))
  have hTcard : T.card ≤ r k N := le_r (Finset.filter_subset _ _) hTfree
  have hsub : A ∩ Set.Iio N ⊆ insert 0 (T : Set ℕ) := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      simp only [hT, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨⟨Nat.pos_of_ne_zero hx0, (Set.mem_Iio.mp hx.2).le⟩, hx.1⟩
  have hncard : (A ∩ Set.Iio N).ncard ≤ T.card + 1 := by
    calc (A ∩ Set.Iio N).ncard ≤ (insert 0 (T : Set ℕ)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (T : Set ℕ).ncard + 1 := Set.ncard_insert_le _ _
      _ = T.card + 1 := by rw [Set.ncard_coe_finset]
  have h1 : δ * N ≤ (r k N : ℝ) + 1 := by
    have : ((A ∩ Set.Iio N).ncard : ℝ) ≤ (r k N : ℝ) + 1 := by exact_mod_cast hncard.trans (by omega)
    linarith
  have h2 : (r k N : ℝ) < δ / 2 * N := (div_lt_iff₀ hNpos).mp hrN
  have h3 : (N : ℝ) < 2 / δ := by
    rw [lt_div_iff₀ hδ]
    nlinarith
  have h4 : 2 / δ ≤ ⌈2 / δ⌉₊ := Nat.le_ceil _
  have h5 : ((⌈2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNM
  push_cast at h5
  linarith
