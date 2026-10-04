-- Prove2me | solution 1 for CompetitivePaging.Combining.punish_count_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:47:44.316108+00:00
-- url     : https://prove2.me/submissions/c8337cee-11d1-4d0c-99a6-0e24218ba7aa

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Combining_punishCount

set_option autoImplicit false

namespace P9b077633

open CompetitivePaging.Combining

open Classical in
/-- Number of (step, server) pairs at which `B` moves a server bounds the cost (uniform metric). -/
theorem card_moves_le_cost {k : ℕ} {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1)
    (B : KServer.OnlineAlgorithm k M) (σ : List M) :
    ((((Finset.range σ.length) ×ˢ (Finset.univ : Finset (Fin k))).filter
      (fun p : ℕ × Fin k => B.conf (σ.take p.1) p.2 ≠ B.conf (σ.take (p.1 + 1)) p.2)).card : ℝ)
      ≤ B.cost σ := by
  rw [Finset.card_filter, Nat.cast_sum]
  unfold KServer.OnlineAlgorithm.cost KServer.moveCost
  rw [Finset.sum_product]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · simp [hM _ _ h]
  · simp

open Classical in
theorem main {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1)
    (A B : KServer.OnlineAlgorithm k M)
    (hA : ∀ l : List M, Function.Injective (A.conf l)) (σ : List M) :
    (punishCount A B σ σ.length : ℝ) ≤ B.cost σ := by
  refine le_trans ?_ (card_moves_le_cost hM B σ)
  have hcard : punishCount A B σ σ.length ≤
      (((Finset.range σ.length) ×ˢ (Finset.univ : Finset (Fin k))).filter
        (fun p : ℕ × Fin k => B.conf (σ.take p.1) p.2 ≠ B.conf (σ.take (p.1 + 1)) p.2)).card := by
    unfold punishCount
    convert Finset.card_le_card_of_forall_subsingleton
      (r := fun (t : ℕ) (p : ℕ × Fin k) => ∃ v t₁, IsVInterval A σ v t₁ t ∧ t₁ ≤ p.1 ∧ p.1 < t ∧
        B.conf (σ.take p.1) p.2 = v ∧ B.conf (σ.take (p.1 + 1)) p.2 ≠ v) ?_ ?_
    · intro t ht
      rw [Finset.mem_filter] at ht
      obtain ⟨_, v, t₁, hAI, t₁', t₂', h1, h2, h3, hBI⟩ := ht
      obtain ⟨hb1, hb2, hb3, i, _, hbs, hbe⟩ := hBI
      refine ⟨(t₂' - 1, i), ?_, v, t₁, hAI, by omega, by omega, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Finset.mem_range.2 (by omega), Finset.mem_univ _⟩, ?_⟩
        have e : t₂' - 1 + 1 = t₂' := by omega
        rw [hbs (t₂' - 1) (by omega) (by omega), e]
        exact fun h => hbe h.symm
      · exact hbs (t₂' - 1) (by omega) (by omega)
      · have e : t₂' - 1 + 1 = t₂' := by omega
        simp only [e]; exact hbe
    · intro p _ t ht u hu
      obtain ⟨_, v, t₁, ⟨_, _, _, j, _, hjs, hje⟩, h1, h2, hv, _⟩ := ht
      obtain ⟨_, w, u₁, ⟨_, _, _, j', _, hj's, hj'e⟩, h1', h2', hw, _⟩ := hu
      have hvw : v = w := hv.symm.trans hw
      subst hvw
      have hjj : j = j' := hA _ ((hjs p.1 h1 h2).trans (hj's p.1 h1' h2').symm)
      subst hjj
      rcases lt_trichotomy t u with h | h | h
      · exact absurd (hj's t (by omega) h) hje
      · exact h
      · exact absurd (hjs u (by omega) h) hj'e
  exact_mod_cast hcard

end P9b077633

open CompetitivePaging.Combining in
theorem solution {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1)
    (A B : KServer.OnlineAlgorithm k M)
    (hA : ∀ l : List M, Function.Injective (A.conf l)) (σ : List M) :
    (punishCount A B σ σ.length : ℝ) ≤ B.cost σ := by
  exact P9b077633.main hM A B hA σ
