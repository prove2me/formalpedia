-- Prove2me | solution 1 for CommitteeVoting.ExpConv.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:45:05.858383+00:00
-- url     : https://prove2.me/submissions/93a8ba38-6d8a-4bc1-96e5-96c755c7cffb

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb
import Theorems.Thm_CommitteeVoting_ExpConv_eq_83
import Theorems.Thm_CommitteeVoting_ExpConv_honest_of_separation

open MeasureTheory ProbabilityTheory CommitteeVoting.ExpConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (Mal H : Finset (Fin m)) (hdisj : Disjoint H Mal)
    (hcard : (1 - p) * (k : ℝ) ≤ (H.card : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i i' : Fin n, ∀ jh ∈ H, ∀ jm ∈ Mal,
      voteProb P ballot i' jm + δ ≤ voteProb P ballot i jh) :
    1 - 2 * (m : ℝ) ^ 2 * Real.exp (-(δ ^ 2 * n / 2))
      ≤ P.real {ω | IsHonestOutcome k p Malᶜ (score (fun i => ballot i ω))} := by
  refine (eq_83 P ballot hmeas hind Mal H hdisj hδ hgap).trans (measureReal_mono ?_)
  intro ω hω
  exact honest_of_separation hkm hp0 hp1 Mal H hdisj hcard _ hω
