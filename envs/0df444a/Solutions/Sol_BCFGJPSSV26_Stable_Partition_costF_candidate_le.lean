-- Prove2me | solution 1 for BCFGJPSSV26.Stable.Partition.costF_candidate_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:06:07.626654+00:00
-- url     : https://prove2.me/submissions/be77663a-9c42-449b-bc75-59e71f651442

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
import all Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

/-- **The mixed bound** ([BCFGJPSSV26b, Lemma 5.4]). -/
theorem mixed_bd (H : Hyp X) :
    (1 - 1 / Real.exp 1) * X.I.costF ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP) +
        1 / Real.exp 1 * costMix X.I (LS' \ Q.Zstar) (Λ₁ ++ Λ₂) ≤ Q.PsiT + 40 * X.ε * X.opt ∧
      costMix X.I (LS' \ Q.Zstar) (Λ₁ ++ Λ₂) ≤ 6 * X.opt := by
  classical
  have hv := H.valid
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  obtain ⟨hcov, -⟩ := Q.cover H
  have hSO : X.OSall w₁.OL ⊆ X.O := by
    rw [← hcov]
    exact subset_union_left.trans (subset_union_left.trans subset_union_left)
  have hsplit : ∀ F : Fin X.I.m → ℝ, ∑ c ∈ X.O, F c =
      ∑ c ∈ X.O \ X.OSall w₁.OL, F c + ∑ c ∈ X.OSall w₁.OL, F c :=
    fun F ↦ (sum_sdiff hSO).symm
  have hM : X.I.costF ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP) = ∑ c ∈ X.O, Q.SM c :=
    Instance.sum_clusters H.O_nonempty _
  have hA : costMix X.I (LS' \ Q.Zstar) (Λ₁ ++ Λ₂) = ∑ c ∈ X.O, Q.SA c :=
    Instance.sum_clusters H.O_nonempty _
  -- the clusters outside `O_S`
  have hrow : ∀ c ∈ X.O \ X.OSall w₁.OL,
      (1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c ≤
        Q.rowT c + X.ε * (59 / 10 * ((X.C c).card * X.per c) + 3 / 4 * X.costS (X.C c)) ∧
      Q.SA c ≤ X.costO c + 3 * ((X.C c).card * X.per c) + 2 * X.ε * X.costS (X.C c) := by
    intro c hc
    obtain ⟨hcO, hcS⟩ := mem_sdiff.1 hc
    have hcases : c ∈ Q.OLam ∨ c ∈ Q.OP ∨ c ∈ Q.OR := by
      rw [← hcov] at hcO
      simp only [mem_union] at hcO
      tauto
    rcases hcases with h | h | h
    · exact Q.row_mixed_L H hcS h
    · exact Q.row_mixed_P H hcS h
    · exact Q.row_mixed_R H hcS h
  -- the clusters of `O_S`
  have hS : ∀ c ∈ X.OSall w₁.OL, (1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c ≤
      ∑ j ∈ X.C c, X.dist j (X.σ₀ c) ∧ Q.SA c ≤ ∑ j ∈ X.C c, X.dist j (X.σ₀ c) := by
    intro c hc
    obtain ⟨h1, h2⟩ := Q.row_mixed_S H hc
    have hie0 : 0 ≤ 1 / Real.exp 1 := by positivity
    have hie1 : 1 / Real.exp 1 ≤ 1 := inv_exp_le.trans (by norm_num)
    have e1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - 1 / Real.exp 1)
    have e2 := mul_le_mul_of_nonneg_left h2 hie0
    exact ⟨by linarith, h2⟩
  -- the totals
  have hOS := Q.cost_OS
  have hPsi : Q.PsiT = ∑ c ∈ X.O \ X.OSall w₁.OL, Q.rowT c +
      (1 + eta) * ∑ c ∈ X.OSall w₁.OL, X.costO c := by
    unfold PsiT
    rw [hsplit, mul_sum]
    congr 1
    refine sum_congr rfl fun c hc ↦ ?_
    unfold rowT
    rw [if_pos hc]
  have hCO : ∀ c, 0 ≤ X.costO c := fun c ↦ sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _
  have hopt' : ∑ c ∈ X.O \ X.OSall w₁.OL, X.costO c + ∑ c ∈ X.OSall w₁.OL, X.costO c =
      X.opt := by
    rw [← hsplit, H.opt_eq_sum]
  have hOS0 : 0 ≤ ∑ c ∈ X.OSall w₁.OL, X.costO c := sum_nonneg fun c _ ↦ hCO c
  have hP : ∑ c ∈ X.O \ X.OSall w₁.OL, ((X.C c).card : ℝ) * X.per c ≤
      (1 + 2 * X.ε) * X.opt := by
    calc ∑ c ∈ X.O \ X.OSall w₁.OL, ((X.C c).card : ℝ) * X.per c
        ≤ ∑ c ∈ X.O \ X.OSall w₁.OL, (1 + 2 * X.ε) * X.costO c :=
          sum_le_sum fun c _ ↦ card_mul_per_le H c
      _ = (1 + 2 * X.ε) * ∑ c ∈ X.O \ X.OSall w₁.OL, X.costO c := (mul_sum _ _ _).symm
      _ ≤ (1 + 2 * X.ε) * X.opt := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hSc : ∑ c ∈ X.O \ X.OSall w₁.OL, X.costS (X.C c) ≤ 4 * X.opt := by
    refine le_trans ?_ (costF_le_four_opt hv H.k_le_m X.P.hN H.alo)
    unfold Instance.costF
    rw [Instance.sum_clusters H.O_nonempty]
    refine sum_le_sum_of_subset_of_nonneg sdiff_subset fun c _ _ ↦ ?_
    exact sum_nonneg fun j _ ↦ Instance.dSet_nonneg hv _ _
  have hP0 : 0 ≤ ∑ c ∈ X.O \ X.OSall w₁.OL, ((X.C c).card : ℝ) * X.per c :=
    sum_nonneg fun c _ ↦ P_nonneg H c
  have hSc0 : 0 ≤ ∑ c ∈ X.O \ X.OSall w₁.OL, X.costS (X.C c) :=
    sum_nonneg fun c _ ↦ Instance.costOn_nonneg hv _ _
  rw [hM, hA]
  constructor
  · have e1 : (1 - 1 / Real.exp 1) * ∑ c ∈ X.O, Q.SM c + 1 / Real.exp 1 * ∑ c ∈ X.O, Q.SA c =
        ∑ c ∈ X.O \ X.OSall w₁.OL, ((1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c) +
          ∑ c ∈ X.OSall w₁.OL, ((1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib, hsplit]
    have e2 := sum_le_sum fun c hc ↦ (hrow c hc).1
    have e3 := sum_le_sum fun c hc ↦ (hS c hc).1
    have e2' : ∑ c ∈ X.O \ X.OSall w₁.OL,
        (Q.rowT c + X.ε * (59 / 10 * ((X.C c).card * X.per c) + 3 / 4 * X.costS (X.C c))) =
        ∑ c ∈ X.O \ X.OSall w₁.OL, Q.rowT c +
          X.ε * (59 / 10 * ∑ c ∈ X.O \ X.OSall w₁.OL, ((X.C c).card : ℝ) * X.per c +
            3 / 4 * ∑ c ∈ X.O \ X.OSall w₁.OL, X.costS (X.C c)) := by
      rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    have e5 : X.ε * (59 / 10 * ∑ c ∈ X.O \ X.OSall w₁.OL, ((X.C c).card : ℝ) * X.per c +
        3 / 4 * ∑ c ∈ X.O \ X.OSall w₁.OL, X.costS (X.C c)) ≤ X.ε * (10 * X.opt) := by
      refine mul_le_mul_of_nonneg_left ?_ hε.le
      have := mul_le_mul_of_nonneg_right hε'.le hopt
      nlinarith
    rw [e1, hPsi]
    linarith
  · have e2 := sum_le_sum fun c hc ↦ (hrow c hc).2
    have e3 := sum_le_sum fun c hc ↦ (hS c hc).2
    have e2' : ∑ c ∈ X.O \ X.OSall w₁.OL,
        (X.costO c + 3 * ((X.C c).card * X.per c) + 2 * X.ε * X.costS (X.C c)) =
        ∑ c ∈ X.O \ X.OSall w₁.OL, X.costO c +
          3 * ∑ c ∈ X.O \ X.OSall w₁.OL, ((X.C c).card : ℝ) * X.per c +
            2 * X.ε * ∑ c ∈ X.O \ X.OSall w₁.OL, X.costS (X.C c) := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
    have hη : (1 : ℝ) + eta ≤ 2 := by unfold eta; norm_num
    have e6 := mul_le_mul_of_nonneg_right hη hOS0
    have e7 := mul_le_mul_of_nonneg_left hSc (by linarith : (0 : ℝ) ≤ 2 * X.ε)
    have e8 := mul_le_mul_of_nonneg_right hε'.le hopt
    have hR0 : 0 ≤ ∑ c ∈ X.O \ X.OSall w₁.OL, X.costO c := sum_nonneg fun c _ ↦ hCO c
    rw [hsplit]
    linarith

/-- **The candidate of the guess `|O_P|`** costs at most `Ψ_T + 60 ε opt` ([BCFGJPSSV26b,
Theorem 3.4]). -/
theorem costF_candidate_le (H : Hyp X) {red blue : Finset (Fin X.I.m)} (hred : red ⊆ LS')
    (hblue : blue = LS' \ red) (hcol : Q.ColorEvent red blue) {Y Zh : Finset (Fin X.I.m)}
    (hY : ∀ l ∈ Λ₁ ++ Λ₂, ∃ i ∈ Y, i ∈ l.ball) (hZ : Zh ⊆ red) (hZc : Zh.card = Q.z)
    (hZs : ∑ c ∈ Zh, hcl X.I LS' (Λ₁ ++ Λ₂) blue c Y = g₂ X.I LS' (Λ₁ ++ Λ₂) red blue Q.z Y)
    (hG : GreedyGuarantee X.I X.P.N (gfun X.I LS' (Λ₁ ++ Λ₂) red blue Q.z) (Λ₁ ++ Λ₂)
      Q.OP.card Y) :
    X.I.costF ((LS' \ Zh) ∪ Y) ≤ Q.PsiT + 60 * X.ε * X.opt := by
  set g := gfun X.I LS' (Λ₁ ++ Λ₂) red blue Q.z
  set A := costMix X.I (LS' \ Q.Zstar) (Λ₁ ++ Λ₂)
  set M := X.I.costF ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP)
  have h5 := costF_le_gfun H.valid hred hblue hY hZ hZc hZs
  obtain ⟨o, ho, hoim⟩ := Q.exists_ball_choice H
  have hg := hG o ho Q.OP rfl
  rw [hoim] at hg
  obtain ⟨h6a, h6b⟩ := Q.g_bounds H hred hblue hcol
  obtain ⟨h7, hA6⟩ := Q.mixed_bd H
  have hT := X.P.N_pos
  have hc1 := pow_le_one_add_div_exp hT
  have hc2 := exp_inv_le_pow hT
  set c := ((X.P.N : ℝ) / (X.P.N + 1)) ^ X.P.N
  have hM : 0 ≤ M := Instance.costF_nonneg H.valid _
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hε := H.eps_pos
  have hε1 : X.ε ≤ 1 := by have := H.eps_lt; linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hNε : 1 / (X.P.N : ℝ) = X.ε := rfl
  -- `g(Ŷ) ≤ c g(∅) + (1 - c) g(O_Λ ∪ O_P)`
  have hgY : g Y ≤ c * g ∅ + (1 - c) * g (Q.OLam ∪ Q.OP) := by nlinarith
  have hc0 : 0 ≤ c := by positivity
  have hc1' : c ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith
  -- `c ∈ [1/e, (1 + ε)/e]`
  have hcε : c - 1 / Real.exp 1 ≤ X.ε / Real.exp 1 := by
    rw [hNε] at hc1
    have : (1 + X.ε) / Real.exp 1 = 1 / Real.exp 1 + X.ε / Real.exp 1 := by ring
    linarith
  have hεe : X.ε / Real.exp 1 ≤ X.ε := div_le_self hε.le (by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith)
  have hε3 : X.ε ^ 3 ≤ X.ε := by
    calc X.ε ^ 3 ≤ X.ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
      _ = X.ε := pow_one _
  have hA0 : 0 ≤ A := by
    change 0 ≤ ∑ j ∈ univ, dMix X.I (.inl j) (LS' \ Q.Zstar) (Λ₁ ++ Λ₂)
    exact sum_nonneg fun _ _ ↦ dMix_nonneg H.valid (Q.radius_nonneg H) _ _
  have key : c * A + (1 - c) * M ≤ 1 / Real.exp 1 * A + (1 - 1 / Real.exp 1) * M +
      X.ε / Real.exp 1 * A := by nlinarith
  nlinarith

end Partition

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.Partition.costF_candidate_le := @BCFGJPSSV26.Stable.Partition.costF_candidate_le
