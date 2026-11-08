-- Prove2me | solution 1 for CapacityGames.support_eq_contributors
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:30:36.361733+00:00
-- url     : https://prove2.me/submissions/13a05c77-3397-4838-a144-f510ce382860

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

open CapacityGames in
theorem solution {N Ω : Type*} [Fintype N] [DecidableEq N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid)
    (hatt : ∀ S : Finset N, SCAttained G S) (huniq : UniqueSupport G)
    (p : Choice N Ω) (hp : SCFeasible G p) (hopt : scProfit G p = scOptValue G Finset.univ) :
    support p.t = contributors G := by
  have hV : ∀ S : Finset N, ∃ q : Choice N Ω, SCFeasible G q ∧ support q.t ⊆ S ∧
      scProfit G q = scOptValue G S ∧ ∀ v ∈ scValues G S, v ≤ scOptValue G S := by
    intro S
    obtain ⟨x, hx⟩ := hatt S
    have hx' : scOptValue G S = x := hx.csSup_eq
    obtain ⟨q, ⟨hq1, hq2⟩, hqx⟩ := hx.1
    exact ⟨q, hq1, hq2, by rw [hqx, hx'], fun v hv => by rw [hx']; exact hx.2 hv⟩
  ext j
  simp only [contributors, contribSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    obtain ⟨q, hq, hqS, hqv, -⟩ := hV (Finset.univ.erase j)
    obtain ⟨-, -, -, -, hUle⟩ := hV Finset.univ
    have hle : scOptValue G (Finset.univ.erase j) ≤ scOptValue G Finset.univ := by
      rw [← hqv]
      exact hUle _ ⟨q, ⟨hq, Finset.subset_univ _⟩, rfl⟩
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hs := huniq p q hp hq hopt (by rw [hqv, h])
      have hjq : j ∈ support q.t := hs ▸ hj
      exact (Finset.mem_erase.mp (hqS hjq)).1 rfl
  · intro hlt
    by_contra hj
    have hsub : support p.t ⊆ Finset.univ.erase j := fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hx), Finset.mem_univ _⟩
    obtain ⟨-, -, -, -, hle⟩ := hV (Finset.univ.erase j)
    have := hle _ ⟨p, ⟨hp, hsub⟩, rfl⟩
    rw [hopt] at this
    linarith
