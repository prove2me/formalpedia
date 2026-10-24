-- Prove2me | solution 1 for CommitteeVoting.ExpConv.eq_83
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:45:04.930669+00:00
-- url     : https://prove2.me/submissions/28cba52d-1d98-4487-b467-fbf91207fcb7

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb
import Theorems.Thm_CommitteeVoting_ExpConv_eq_82

open MeasureTheory ProbabilityTheory CommitteeVoting.ExpConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (Mal H : Finset (Fin m)) (hdisj : Disjoint H Mal)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i i' : Fin n, ∀ jh ∈ H, ∀ jm ∈ Mal,
      voteProb P ballot i' jm + δ ≤ voteProb P ballot i jh) :
    1 - 2 * (m : ℝ) ^ 2 * Real.exp (-(δ ^ 2 * n / 2))
      ≤ P.real {ω | ∀ jh ∈ H, ∀ jm ∈ Mal,
          score (fun i => ballot i ω) jm < score (fun i => ballot i ω) jh} := by
  set G := {ω | ∀ jh ∈ H, ∀ jm ∈ Mal,
          score (fun i => ballot i ω) jm < score (fun i => ballot i ω) jh} with hG
  set f : Fin m × Fin m → Set Ω := fun q =>
    {ω | score (fun i => ballot i ω) q.1 ≤ score (fun i => ballot i ω) q.2} with hf
  have hcover : (Set.univ : Set Ω) ⊆ G ∪ ⋃ q ∈ H ×ˢ Mal, f q := by
    intro ω _
    by_cases hω : ω ∈ G
    · exact Or.inl hω
    · right
      simp only [hG, Set.mem_setOf_eq, not_forall, not_lt] at hω
      obtain ⟨jh, hjh, jm, hjm, hle⟩ := hω
      simp only [Set.mem_iUnion]
      exact ⟨(jh, jm), Finset.mem_product.2 ⟨hjh, hjm⟩, hle⟩
  have hbad : P.real (⋃ q ∈ H ×ˢ Mal, f q) ≤ (H ×ˢ Mal).card * (2 * Real.exp (-(δ ^ 2 * n / 2))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have : ∀ q ∈ H ×ˢ Mal, P.real (f q) ≤ 2 * Real.exp (-(δ ^ 2 * n / 2)) := by
      intro q hq
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
      exact eq_82 P ballot hmeas hind q.1 q.2 hδ (fun i i' => hgap i i' q.1 h1 q.2 h2)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hcard : ((H ×ˢ Mal).card : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [Finset.card_product]
    have h1 : H.card ≤ m := by simpa using Finset.card_le_univ H
    have h2 : Mal.card ≤ m := by simpa using Finset.card_le_univ Mal
    have : H.card * Mal.card ≤ m ^ 2 := by rw [sq]; exact Nat.mul_le_mul h1 h2
    exact_mod_cast this
  have hone : (1 : ℝ) ≤ P.real G + P.real (⋃ q ∈ H ×ˢ Mal, f q) := by
    have := (measureReal_mono (μ := P) hcover).trans (measureReal_union_le _ _)
    simpa using this
  have hE : 0 ≤ 2 * Real.exp (-(δ ^ 2 * n / 2)) := by positivity
  have := mul_le_mul_of_nonneg_right hcard hE
  nlinarith
