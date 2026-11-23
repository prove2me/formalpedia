-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.terminal_cardinality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T06:49:56.440416+00:00
-- url     : https://prove2.me/submissions/b562c827-544f-428c-a5f2-cc962330a1a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications
import Theorems.Thm_ChenCapacityTerminals_Exact_greedy_predecessors
import Theorems.Thm_ChenCapacityTerminals_Exact_postorder_charging

set_option autoImplicit false
set_option maxHeartbeats 800000

open ChenCapacityTerminals.Exact

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
      (c : Construction), Prepared G r → 1 ≤ d → d ≤ G.vertices.card → 0 < L → 1 ≤ t →
      LegalConstruction G r d L b t c →
      c.terminals G r ((L : ℝ) / (4 * d)) b t ⊆ G.vertices \ {r} ∧
      (c.terminals G r ((L : ℝ) / (4 * d)) b t).card ≤
        (C : ℝ) * ((G.vertices.card : ℝ) / d) * Real.log (2 + (G.arcs.length : ℝ)) +
          (mass b G.vertices : ℝ) / (t + 1 : ℕ) := by
  classical
  obtain ⟨Cg, hCg, hgreedy⟩ := greedy_predecessors
  have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Cg + 1 / Real.log 2, by positivity, ?_⟩
  intro G r d L b t c hG hd hdn hL ht hc
  obtain ⟨hsubset, hmarks, hcomponents⟩ := postorder_charging G r d L b t c hc
  refine ⟨hsubset, ?_⟩
  obtain ⟨hgcard, hgpre⟩ := hgreedy G r d L b t c hG hd hdn hL hc
  have hc' := hc
  rcases hc' with ⟨hrounds, hzero, hpart, hmerge, hcontinue, hstop, hrep,
    hjoinN, hjoin, hcomplete, hsort, hgreedyrel, hfinalN, hfinalTargets,
    hfinalWit, hret⟩
  let τ : ℝ := (L : ℝ) / (4 * d)
  let S : Parts := (newSources G τ (c.partitions (c.rounds - 1))).filter fun C => r ∉ C
  let M : Finset ℕ := c.marks G τ b t \ {r, dummy G}
  have hsourceNat : (S.image c.representative).card ≤ G.vertices.card / d := by
    calc
      (S.image c.representative).card ≤ S.card := Finset.card_image_le
      _ ≤ (newSources G τ (c.partitions (c.rounds - 1))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ G.vertices.card / d := hstop
  have hsourceNatR : ((S.image c.representative).card : ℝ) ≤
      ((G.vertices.card / d : ℕ) : ℝ) := by exact_mod_cast hsourceNat
  have hsource : ((S.image c.representative).card : ℝ) ≤
      (G.vertices.card : ℝ) / d := hsourceNatR.trans Nat.cast_div_le
  have hunionEarly : (S.image c.representative ∪ (c.greedy.toFinset \ {r})).card ≤
      (S.image c.representative).card + c.greedy.toFinset.card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left
      (Finset.card_le_card Finset.sdiff_subset) _)
  change (c.earlyProbes G r τ ∪ M).card ≤
    (Cg + 1 / Real.log 2) * ((G.vertices.card : ℝ) / d) *
      Real.log (2 + (G.arcs.length : ℝ)) +
      (mass b G.vertices : ℝ) / (t + 1 : ℕ)
  have hterminalNat : (c.earlyProbes G r τ ∪ M).card ≤
      (S.image c.representative).card + c.greedy.toFinset.card + M.card := by
    unfold Construction.earlyProbes
    change (S.image c.representative ∪ (c.greedy.toFinset \ {r}) ∪ M).card ≤ _
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right hunionEarly _)
  have hterminal : ((c.earlyProbes G r τ ∪ M).card : ℝ) ≤
      ((S.image c.representative).card : ℝ) + c.greedy.toFinset.card + M.card := by
    exact_mod_cast hterminalNat
  have hnonneg : 0 ≤ (G.vertices.card : ℝ) / d := by positivity
  have hm : (0 : ℝ) ≤ G.arcs.length := by positivity
  have hlog : Real.log 2 ≤ Real.log (2 + (G.arcs.length : ℝ)) := by
    exact Real.log_le_log (by positivity) (by linarith)
  have hscale : (G.vertices.card : ℝ) / d ≤
      (1 / Real.log 2) * ((G.vertices.card : ℝ) / d) *
        Real.log (2 + (G.arcs.length : ℝ)) := by
    calc
      _ = (1 / Real.log 2) * ((G.vertices.card : ℝ) / d) * Real.log 2 := by
        field_simp
      _ ≤ _ := by gcongr
  calc
    ((c.earlyProbes G r τ ∪ M).card : ℝ) ≤
        ((S.image c.representative).card : ℝ) + c.greedy.toFinset.card + M.card := hterminal
    _ ≤ (G.vertices.card : ℝ) / d +
        Cg * ((G.vertices.card : ℝ) / d) * Real.log (2 + (G.arcs.length : ℝ)) +
        (mass b G.vertices : ℝ) / (t + 1 : ℕ) := by gcongr
    _ ≤ (Cg + 1 / Real.log 2) * ((G.vertices.card : ℝ) / d) *
        Real.log (2 + (G.arcs.length : ℝ)) +
        (mass b G.vertices : ℝ) / (t + 1 : ℕ) := by
      nlinarith
