-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_finite_subsets_liminf_encard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:14:28.084208+00:00
-- url     : https://prove2.me/submissions/d965aa28-a5ee-4fb7-89b1-d51382b28078

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

/-- Eventual counting of every finite selection bounds the full extended
cardinality by the limit inferior of the approximating counts. -/
theorem solution {α : Type*}
    (S : Set α) (g : ℕ → ℕ)
    (h : ∀ F : Finset α, (F : Set α) ⊆ S →
      ∀ᶠ n : ℕ in atTop, F.card ≤ g n) :
    S.encard ≤ Filter.liminf (fun n : ℕ => (g n : ℕ∞)) atTop := by
  classical
  have hk : ∀ k : ℕ, (k : ℕ∞) ≤ S.encard →
      (k : ℕ∞) ≤ Filter.liminf (fun n : ℕ => (g n : ℕ∞)) atTop := by
    intro k hks
    obtain ⟨t, htS, htCard⟩ := Set.exists_subset_encard_eq hks
    have htFinite : t.Finite := Set.finite_of_encard_eq_coe htCard
    let F : Finset α := htFinite.toFinset
    have hFS : (F : Set α) ⊆ S := by
      simpa [F] using htS
    have hFenc : (F : Set α).encard = (k : ℕ∞) := by
      simpa [F] using htCard
    have hcardCast : (F.card : ℕ∞) = (k : ℕ∞) := by
      simpa using hFenc
    have hcard : F.card = k := by exact_mod_cast hcardCast
    have he : ∀ᶠ n : ℕ in atTop, (k : ℕ∞) ≤ (g n : ℕ∞) :=
      (h F hFS).mono (fun n hn => by exact_mod_cast (hcard ▸ hn))
    rw [Filter.liminf_eq_iSup_iInf]
    refine le_iSup_of_le {n : ℕ | (k : ℕ∞) ≤ (g n : ℕ∞)} ?_
    refine le_iSup_of_le he ?_
    exact le_iInf fun n => le_iInf fun hn => hn
  by_cases htop : S.encard = ⊤
  · rw [htop]
    have htop_le : (⨆ k : ℕ, (k : ℕ∞)) ≤
        Filter.liminf (fun n : ℕ => (g n : ℕ∞)) atTop := by
      exact iSup_le fun k => hk k (by simp [htop])
    simpa only [ENat.iSup_natCast] using htop_le
  · rcases (WithTop.ne_top_iff_exists.mp htop) with ⟨k, hkS⟩
    calc
      S.encard = (k : ℕ∞) := hkS.symm
      _ ≤ Filter.liminf (fun n : ℕ => (g n : ℕ∞)) atTop :=
        hk k hkS.le
