-- Prove2me | solution 1 for CommitteeVoting.ExpConv.honest_of_separation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:07:52.213138+00:00
-- url     : https://prove2.me/submissions/77e381d9-8d12-4d88-a102-fd71d0de4bd4

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee

set_option autoImplicit false
open CommitteeVoting.ExpConv

theorem solution {m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Mal H : Finset (Fin m)) (hdisj : Disjoint H Mal) (hcard : (1 - p) * (k : ℝ) ≤ (H.card : ℝ))
    (s : Fin m → ℕ) (hsep : ∀ jh ∈ H, ∀ jm ∈ Mal, s jm < s jh) :
    IsHonestOutcome k p Malᶜ s := by
  intro T hT
  obtain ⟨hTk, hTa⟩ := hT
  by_cases hex : ∃ a ∈ T, a ∈ Mal
  · obtain ⟨a, haT, haM⟩ := hex
    -- every honest candidate is in T
    have hHT : H ⊆ T := by
      intro h hh
      by_contra hnT
      have := hTa a haT h hnT
      have := hsep h hh a haM
      omega
    have hHsub : H ⊆ T ∩ (Malᶜ : Finset (Fin m)) := by
      intro h hh
      refine Finset.mem_inter.2 ⟨hHT hh, ?_⟩
      rw [Finset.mem_compl]
      exact Finset.disjoint_left.1 hdisj hh
    have h1 : H.card ≤ (T ∩ (Malᶜ : Finset (Fin m))).card := Finset.card_le_card hHsub
    have h2 : (⌈(1 - p) * (k : ℝ)⌉ : ℤ) ≤ (H.card : ℤ) := by
      rw [Int.ceil_le]; exact_mod_cast hcard
    have h3 : ((H.card : ℕ) : ℤ) ≤ (((T ∩ (Malᶜ : Finset (Fin m))).card : ℕ) : ℤ) := by exact_mod_cast h1
    omega
  · push_neg at hex
    have hsub : T ⊆ (Malᶜ : Finset (Fin m)) := by
      intro a ha
      rw [Finset.mem_compl]; exact hex a ha
    have : T ∩ (Malᶜ : Finset (Fin m)) = T := Finset.inter_eq_left.2 hsub
    rw [this, hTk]
    have : (⌈(1 - p) * (k : ℝ)⌉ : ℤ) ≤ (k : ℤ) := by
      rw [Int.ceil_le]
      have : (0:ℝ) ≤ p * k := by positivity
      push_cast; nlinarith
    exact this
