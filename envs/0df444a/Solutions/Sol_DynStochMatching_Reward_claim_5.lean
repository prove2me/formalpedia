-- Prove2me | solution 1 for DynStochMatching.Reward.claim_5
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:18:23.272723+00:00
-- url     : https://prove2.me/submissions/c874b15c-b049-47ed-9678-3c079715af96

import Definitions.Def_DynStochMatching_Reward_Algorithm

open MeasureTheory Filter
open scoped ENNReal Classical
open DynStochMatching.Reward

noncomputable def instClaim5 : Instance 1 where
  arrivalRate _ := 1
  positive _ := zero_lt_one
  lifetime _ := Lifetime.exponential 1 zero_lt_one
  reward _ _ := 0
  symmetric _ _ := rfl

noncomputable def flowClaim5 : Flow 1 where
  edge _ _ := 0
  abandon _ := 1
  unused _ := 0

private lemma source_instClaim5 : sourceDomain instClaim5 :=
  Or.inl (fun _ => ⟨1, zero_lt_one, rfl⟩)

private lemma qbFeasible_flowClaim5 : qbFeasible instClaim5 flowClaim5 := by
  refine ⟨fun _ _ => le_rfl, fun _ => ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
  · intro i
    simp [incoming, outgoing, flowClaim5, instClaim5]
  · intro i j
    simp [rateConstraint, instClaim5, flowClaim5, passiveRate]

private lemma pairReward_instClaim5 (ω : RandomSeeds) (e : ℕ × ℕ) :
    pairReward instClaim5 ω e = 0 := by
  unfold pairReward
  cases arrivalType instClaim5.toMarkedPoissonData ω e.1 <;>
    cases arrivalType instClaim5.toMarkedPoissonData ω e.2 <;>
    rfl

private lemma accumulatedRewardPart_instClaim5 (π : MatchingPolicy) (pos : Bool) (t : ℝ)
    (ω : RandomSeeds) :
    accumulatedRewardPart instClaim5 π pos t ω = 0 := by
  unfold accumulatedRewardPart
  simp [pairReward_instClaim5]

private lemma expectedReward_instClaim5 (π : MatchingPolicy) (t : ℝ) :
    expectedReward instClaim5 π t = 0 := by
  unfold expectedReward
  simp [accumulatedRewardPart_instClaim5]

private lemma averageReward_instClaim5 (π : MatchingPolicy) :
    averageReward instClaim5 π = 0 := by
  unfold averageReward
  simp only [expectedReward_instClaim5, mul_zero]
  exact liminf_const (0 : EReal)

private lemma optimalReward_instClaim5_nonpos :
    optimalReward instClaim5 ≤ 0 := by
  unfold optimalReward
  refine iSup_le ?_
  intro π
  rw [averageReward_instClaim5]

private lemma flowGuarantees_flowClaim5 : flowGuarantees instClaim5 flowClaim5 := by
  have hrew : (flowReward instClaim5 flowClaim5 : EReal) = 0 := by
    unfold flowReward
    simp [flowClaim5]
  have hopt := optimalReward_instClaim5_nonpos
  have h14 : ((1 / 4 : ℝ) : EReal) * optimalReward instClaim5 ≤ 0 := by
    calc ((1 / 4 : ℝ) : EReal) * optimalReward instClaim5
      _ ≤ ((1 / 4 : ℝ) : EReal) * 0 :=
          mul_le_mul_of_nonneg_left hopt (EReal.coe_nonneg.mpr (by norm_num))
      _ = 0 := mul_zero _
  have h12 : ((1 / 2 : ℝ) : EReal) * optimalReward instClaim5 ≤ 0 := by
    calc ((1 / 2 : ℝ) : EReal) * optimalReward instClaim5
      _ ≤ ((1 / 2 : ℝ) : EReal) * 0 :=
          mul_le_mul_of_nonneg_left hopt (EReal.coe_nonneg.mpr (by norm_num))
      _ = 0 := mul_zero _
  refine ⟨?_, fun _ => ?_, fun _ => ?_⟩ <;> rw [hrew]
  · exact h14
  · exact h12
  · exact hopt

theorem solution : ¬ (∀ {n : ℕ} (D : Instance n) (x : Flow n)
    (hsource : sourceDomain D) (hfeasible : qbFeasible D x) (hperformance : flowGuarantees D x)
    (i : Fin n),
    (∀ l : Fin (support x i).length,
      0 ≤ decomposition D x i l.val ∧
      x.edge i ((support x i)[l.val]) =
        ∑ q ∈ Finset.Ico l.val (support x i).length,
          passiveRate x ((support x i)[l.val]) / decompositionDenominator D x i q *
            decomposition D x i q) ∧
    x.abandon i = ∑ l ∈ Finset.range (support x i).length,
      finiteDeathRate (D.lifetime i) / decompositionDenominator D x i l *
        decomposition D x i l) := by
  intro h
  have hab := (h instClaim5 flowClaim5 source_instClaim5 qbFeasible_flowClaim5
    flowGuarantees_flowClaim5 0).2
  have hsup : support flowClaim5 0 = [] := by
    unfold support
    have hfilt : (List.finRange 1).filter (fun j => decide (0 < flowClaim5.edge 0 j)) = [] := by
      simp [flowClaim5]
    rw [hfilt]
    exact List.mergeSort_nil
  rw [hsup] at hab
  simp [flowClaim5] at hab
