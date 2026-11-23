-- Prove2me | solution 1 for DistributedMWC440.UpperBound.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:26:38.472091+00:00
-- url     : https://prove2.me/submissions/0371ca79-19e8-46b7-9a58-516012dce670

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

open DistributedMWC440.UpperBound

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (hpos : ∀ u v, W.graph.Adj u v → 0 < W.length u v)
    (S R : Finset V) (hR : R ⊆ S) (hcard : 2 ≤ R.card)
    (k d : ℝ) (hk : 1/2 ≤ k) (hd : 0 < d) (δ : Shifts S)
    (hδ : ValidShifts S k d δ) (s : S) (hcapture : Captures W S R k d δ s) :
    setDist W s.val R < trunc S k d δ s - d ∧
      trunc S k d δ s - d ≤ deltaMax S k d - d := by
  classical
  have hwalk_nonneg : ∀ {u v : V} (p : W.graph.Walk u v), 0 ≤ walkWeight W p := by
    intro u v p
    induction p with
    | nil => simp [walkWeight, OAI.PlanarL1.walkLength]
    | cons h p ih =>
        exact add_nonneg (W.nonnegative _ _ h) ih
  have hdist_nonneg : ∀ u v : V, 0 ≤ dist W u v := by
    intro u v
    haveI : Nonempty (W.graph.Walk u v) := hW.preconnected u v
    apply le_csInf (Set.range_nonempty (fun q : W.graph.Walk u v => walkWeight W q))
    rintro a ⟨q, rfl⟩
    exact hwalk_nonneg q
  have hex : ∃ r ∈ R, r ≠ s.val := by
    by_contra h
    push_neg at h
    have hsub : R ⊆ {s.val} := by
      intro r hr
      exact Finset.mem_singleton.mpr (h r hr)
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  obtain ⟨r, hrR, hrs⟩ := hex
  let r' : S := ⟨r, hR hrR⟩
  have hr' : r' ≠ s := by
    intro h
    exact hrs (congrArg Subtype.val h)
  have hself : dist W r r = 0 := by
    apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        rintro a ⟨p, rfl⟩
        exact hwalk_nonneg p
      · refine ⟨SimpleGraph.Walk.nil, ?_⟩
        simp [walkWeight, OAI.PlanarL1.walkLength]
    · apply le_csInf (Set.range_nonempty (fun p : W.graph.Walk r r => walkWeight W p))
      rintro a ⟨p, rfl⟩
      exact hwalk_nonneg p
  have hsetDist : setDist W r R ≤ 0 := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro a ⟨x, hx, rfl⟩
      exact hdist_nonneg r x
    · exact ⟨r, hrR, hself.symm⟩
  have hcap := hcapture r' hr'
  have hnonneg : 0 ≤ trunc S k d δ r' := hδ r'
  constructor
  · dsimp [r'] at hcap hnonneg
    linarith
  · have hle : trunc S k d δ s ≤ deltaMax S k d := min_le_right _ _
    linarith
