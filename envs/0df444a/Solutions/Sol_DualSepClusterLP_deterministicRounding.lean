-- Prove2me | solution 1 for DualSepClusterLP.deterministicRounding
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T07:56:11.501+00:00
-- url     : https://prove2.me/submissions/137f93da-eb7c-47d0-b56a-4cdff2603502

import Theorems.Thm_DualSepClusterLP_conditionalExpectationRoundingTraces
import Theorems.Thm_DualSepClusterLP_positiveTriangleEndpointCertificate

set_option autoImplicit false

namespace DualSepClusterLP

private theorem pairMass_le_one {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z)
    (i j : Fin n) : pairMass z i j ≤ 1 := by
  rw [← hz.2 i]
  unfold pairMass
  apply Finset.sum_le_sum
  intro S _
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj, hz.1 S]

/-- Vertex equalities count the weight crossing a positive edge twice. -/
private theorem boundaryMass {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z)
    (i j : Fin n) :
    (∑ S : Finset (Fin n),
        (if decide (i ∈ S) != decide (j ∈ S) then (1:ℝ)/2 else 0) * z S) =
        1 - pairMass z i j := by
  have term (S : Finset (Fin n)) :
      (if decide (i ∈ S) != decide (j ∈ S) then (1:ℝ)/2 else 0) * z S =
        ((if i ∈ S then z S else 0) + (if j ∈ S then z S else 0))/2 -
        (if i ∈ S ∧ j ∈ S then z S else 0) := by
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi,hj] <;> ring
  simp_rw [term]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hz.2 i, hz.2 j]
  unfold pairMass
  ring

theorem primalValue_eq_pairBudgets {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) : primalValue G z = budgetTotal G z edgeLPCost := by
  classical
  unfold primalValue subsetCost budgetTotal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · simp only [h, if_true]
    cases hp : G i j
    · simp [edgeLPCost, pairMass, ite_mul]
    · simpa [edgeLPCost] using boundaryMass z hz i j
  · simp [h]

private theorem budget_identity (pos : Bool) (y : ℝ) (hy : y ≤ 1) :
    (2773/4000) * clusterEdgeBudget pos y +
      (1-2773/4000) * pivotEdgeBudget pos y = (2773/2000) * edgeLPCost pos y := by
  have hn : 2-y ≠ 0 := by linarith
  cases pos <;> simp [clusterEdgeBudget, pivotEdgeBudget, edgeLPCost] <;> field_simp <;> ring

private theorem total_identity {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) :
    (2773/4000) * budgetTotal G z clusterEdgeBudget +
      (1-2773/4000) * budgetTotal G z pivotEdgeBudget = (2773/2000) * primalValue G z := by
  rw [primalValue_eq_pairBudgets G z hz]
  unfold budgetTotal
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j
  · simpa [h] using budget_identity (G i j) (pairMass z i j) (pairMass_le_one z hz i j)
  · simp [h]

/-- Take the cheaper of the outputs of the two deterministic procedures. -/
theorem cheaper_le_primal {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) (C P : Clustering n)
    (hC : (disagreements G C : ℝ) ≤ budgetTotal G z clusterEdgeBudget)
    (hP : (disagreements G P : ℝ) ≤ budgetTotal G z pivotEdgeBudget) :
    (min (disagreements G C) (disagreements G P) : ℝ) ≤ (2773/2000) * primalValue G z := by
  have h := total_identity G z hz
  have h₁ := (min_le_left (disagreements G C : ℝ) (disagreements G P : ℝ)).trans hC
  have h₂ := (min_le_right (disagreements G C : ℝ) (disagreements G P : ℝ)).trans hP
  linarith only [h,h₁,h₂]

end DualSepClusterLP

namespace DualSepClusterLP

private theorem clockPairExpectation {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) (i j : Fin n) :
    (∑ S : Finset (Fin n), z S * clockPairSlack G z S i j) = 0 := by
  let y := pairMass z i j
  let B := clusterEdgeBudget (G i j) y
  let a : ℝ := B - (if G i j then 1 else 0)
  let b : ℝ := (if G i j then 2 else -1) - B
  have hterm (S : Finset (Fin n)) :
      z S * clockPairSlack G z S i j =
        a * (if i ∈ S then z S else 0) + a * (if j ∈ S then z S else 0) +
        b * (if i ∈ S ∧ j ∈ S then z S else 0) := by
    cases hs : G i j <;> by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [clockPairSlack, a, b, B, y, hs, hi, hj] <;> ring
  have hy : y ≤ 1 := by
    rw [← hz.2 i]
    unfold y pairMass
    apply Finset.sum_le_sum
    intro S _
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi,hj,hz.1 S]
  have hden : 2 - y ≠ 0 := by linarith
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, hz.2, mul_one]
  change a + a + b * y = 0
  cases hs : G i j <;> simp [a,b,B,clusterEdgeBudget,hs] <;> field_simp [hden] <;> ring

/-- An active positive-weight LP column exists whose selection leaves the cluster potential
nonincreasing. The certificate follows by averaging separately on each live pair. -/
theorem clockStepOK_of_primalFeasible {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) : ClockStepOK G z := by
  classical
  intro W hW
  let slack (S : Finset (Fin n)) : ℝ :=
    ∑ i ∈ W, ∑ j ∈ W, if i < j then clockPairSlack G z S i j else 0
  have hsum : (∑ S : Finset (Fin n), z S * slack S) = 0 := by
    simp only [slack, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : i < j
    · simpa only [hij, if_true] using clockPairExpectation G z hz i j
    · simp [hij]
  have hinactive (S : Finset (Fin n)) (hS : ¬ (W ∩ S).Nonempty) : slack S = 0 := by
    have hnot (i : Fin n) (hi : i ∈ W) : i ∉ S := fun h => hS ⟨i, Finset.mem_inter.mpr ⟨hi,h⟩⟩
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    simp [clockPairSlack,hnot i hi,hnot j hj]
  obtain ⟨v,hv⟩ := hW
  have hm : (∑ S : Finset (Fin n), if v ∈ S then z S else 0) ≠ 0 := by rw [hz.2 v]; norm_num
  obtain ⟨T,_,hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hvT : v ∈ T := by by_contra h; simp [h] at hT
  have hzT : 0 < z T := lt_of_le_of_ne (hz.1 T) (Ne.symm (by simpa [hvT] using hT))
  have haT : (W ∩ T).Nonempty := ⟨v,Finset.mem_inter.mpr ⟨hv,hvT⟩⟩
  by_contra hn
  have hbad (S : Finset (Fin n)) (hs : 0 < z S) (ha : (W ∩ S).Nonempty) : slack S < 0 :=
    lt_of_not_ge fun h => hn ⟨S,hs,ha,h⟩
  have hp (S : Finset (Fin n)) : z S * slack S ≤ 0 := by
    by_cases hs : 0 < z S
    · by_cases ha : (W ∩ S).Nonempty
      · exact (mul_neg_of_pos_of_neg hs (hbad S hs ha)).le
      · simp [hinactive S ha]
    · rw [le_antisymm (le_of_not_gt hs) (hz.1 S), zero_mul]
  have hnSum := Finset.sum_neg' (s := (Finset.univ : Finset (Finset (Fin n))))
    (f := fun S => z S * slack S) (fun S _ => hp S)
    ⟨T,Finset.mem_univ T,mul_neg_of_pos_of_neg hzT (hbad T hzT haT)⟩
  linarith

end DualSepClusterLP

namespace DualSepClusterLP

/-- Every unordered pair contributes once, including a disagreeing positive edge whose two
labels have distinct emission times. Empty rounds and the empty graph are allowed. -/
theorem disagreements_le_of_roundTraceOK {n : ℕ} (G : Graph n) (C : Clustering n)
    (z : Finset (Fin n) → ℝ) (budget : Bool → ℝ → ℝ) (h : RoundTraceOK G C z budget) :
    (disagreements G C : ℝ) ≤ budgetTotal G z budget := by
  have hsum : ∑ r, roundTraceMargin G C z budget r =
      budgetTotal G z budget - (disagreements G C : ℝ) := by
    unfold roundTraceMargin budgetTotal disagreements
    push_cast
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij, eq_comm]
    · simp [hij]
  have hn := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin n))) (fun r _ => h r)
  linarith

end DualSepClusterLP

namespace DualSepClusterLP

private def pivotLaw {n : ℕ} (z : Finset (Fin n) → ℝ) (u : Fin n) (S : Finset (Fin n)) : ℝ :=
  if u ∈ S then z S else 0

private def mark {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

private theorem pivot_mean {n : ℕ} (z : Finset (Fin n) → ℝ) (u v : Fin n) :
    ∑ S, pivotLaw z u S * mark S v = pairMass z u v := by
  unfold pairMass
  apply Finset.sum_congr rfl
  intro S _
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [pivotLaw,mark,hu,hv]

private theorem pivot_joint {n : ℕ} (z : Finset (Fin n) → ℝ) (u v w : Fin n) :
    ∑ S, pivotLaw z u S * mark S v * mark S w = tripleMass z u v w := by
  unfold tripleMass
  apply Finset.sum_congr rfl
  intro S _
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;>
    simp [pivotLaw,mark,hu,hv,hw]

private theorem pivot_cov {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z) (u v w : Fin n) :
    ∑ S, pivotLaw z u S * (mark S v - pairMass z u v) * (mark S w - pairMass z u w) =
      tripleMass z u v w - pairMass z u v * pairMass z u w := by
  have he (S : Finset (Fin n)) :
      pivotLaw z u S * (mark S v - pairMass z u v) * (mark S w - pairMass z u w) =
        pivotLaw z u S * mark S v * mark S w -
        (pivotLaw z u S * mark S v) * pairMass z u w -
        (pivotLaw z u S * mark S w) * pairMass z u v +
        pivotLaw z u S * (pairMass z u v * pairMass z u w) := by ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,
    pivot_joint,pivot_mean]
  rw [show ∑ S, pivotLaw z u S = 1 from hz.2 u]
  ring

/-- For any weights on the vertices, the conditional covariance matrix of membership in
a primal column containing the pivot is positive semidefinite. Set unused weights to zero. -/
theorem pivot_covariance_psd {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z)
    (u : Fin n) (T : Finset (Fin n)) (a : Fin n → ℝ) :
    0 ≤ ∑ v ∈ T, ∑ w ∈ T,
      a v * a w * (tripleMass z u v w - pairMass z u v * pairMass z u w) := by
  have h (S : Finset (Fin n)) :
      pivotLaw z u S * (∑ v ∈ T, a v * (mark S v - pairMass z u v)) ^ 2 =
        ∑ v ∈ T, ∑ w ∈ T, a v * a w *
          (pivotLaw z u S * (mark S v - pairMass z u v) * (mark S w - pairMass z u w)) := by
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hnon : 0 ≤ ∑ S, pivotLaw z u S * (∑ v ∈ T, a v * (mark S v - pairMass z u v)) ^ 2 := by
    apply Finset.sum_nonneg
    intro S _
    apply mul_nonneg _ (sq_nonneg _)
    simp only [pivotLaw]; split <;> first | exact hz.1 S | exact le_rfl
  convert hnon using 1
  symm
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.mul_sum,pivot_cov z hz u v w]

/-- The Fréchet bounds for the two membership indicators of a column sampled at u. -/
theorem pivot_frechet {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z) (u v w : Fin n) :
    max 0 (pairMass z u v + pairMass z u w - 1) ≤ tripleMass z u v w ∧
    tripleMass z u v w ≤ min (pairMass z u v) (pairMass z u w) := by
  classical
  rw [max_le_iff,le_min_iff]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · unfold tripleMass
    refine Finset.sum_nonneg fun S _ => ?_
    split <;> first | exact hz.1 S | exact le_rfl
  · rw [← hz.2 u]
    unfold pairMass tripleMass
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro S _
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;>
      simp [hu,hv,hw,hz.1 S]
  all_goals
    unfold pairMass tripleMass
    apply Finset.sum_le_sum
    intro S _
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;>
      simp [hu,hv,hw,hz.1 S]


theorem pairMass_bounds {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z) (u v : Fin n) :
    pairMass z u v ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · unfold pairMass
    refine Finset.sum_nonneg fun S _ => ?_
    split <;> first | exact hz.1 S | exact le_rfl
  · rw [← hz.2 u]
    unfold pairMass
    apply Finset.sum_le_sum
    intro S _
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu,hv,hz.1 S]

theorem pairMass_swap {n : ℕ} (z : Finset (Fin n) → ℝ) (u v : Fin n) :
    pairMass z u v = pairMass z v u := by
  simp only [pairMass, and_comm]

theorem tripleMass_swap_left {n : ℕ} (z : Finset (Fin n) → ℝ) (u v w : Fin n) :
    tripleMass z u v w = tripleMass z v u w := by
  simp only [tripleMass, and_left_comm]

theorem tripleMass_swap_right {n : ℕ} (z : Finset (Fin n) → ℝ) (u v w : Fin n) :
    tripleMass z u v w = tripleMass z u w v := by
  simp only [tripleMass, and_comm]

theorem tripleMass_diagonal {n : ℕ} (z : Finset (Fin n) → ℝ) (u v : Fin n) :
    tripleMass z u v v = pairMass z u v := by
  simp only [tripleMass, pairMass,and_self]

/-- Equation (46), summed over pivots and expanded as an ordered triple sum. -/
theorem covarianceTotal_nonnegative {n : ℕ} (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z)
    (W : Finset (Fin n)) (θ : Fin n → Fin n → ℝ) :
    0 ≤ ∑ u ∈ W, ∑ v ∈ W, ∑ w ∈ W, θ u v * θ u w *
      (tripleMass z u v w - pairMass z u v * pairMass z u w) :=
  Finset.sum_nonneg fun u _ => pivot_covariance_psd z hz u W (θ u)

end DualSepClusterLP

namespace DualSepClusterLP

/-- Twice the weighted variance of a membership indicator, the pair contribution of (45). -/
private noncomputable def pivotIncidentVariance (positive : Bool) (y : ℝ) : ℝ :=
  if positive then 2*(1012/25)*y^3*(1-y)^5 else 0

/-- The residual after removing one factor 1-y and the positive denominator 2-y. -/
private noncomputable def incidentResidual (y q : ℝ) : ℝ :=
  2*(2773/1227)*(1-y) - (2-y)*(1-q+(1012/25)*y^3*(1-y)^4)

private theorem lowResidual (y : ℝ) (hl : 0 ≤ y) (hr : y ≤ 1/2) :
    0 ≤ incidentResidual y (0) := by
  let u := 2*y
  let v := 1-2*y
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he : incidentResidual y (0) =
      (1/1963200)*(4947200*v^8 +
      36122400*u*v^7 +
      114335200*u^2*v^6 +
      184616416*u^3*v^5 +
      170736144*u^4*v^4 +
      96508448*u^5*v^3 +
      33677576*u^6*v^2 +
      6699132*u^7*v +
      560707*u^8) := by
    dsimp [incidentResidual, u, v]
    ring
  rw [he]
  positivity

private theorem middleResidual (y : ℝ) (hl : 1/2 ≤ y) (hr : y ≤ 25/26) :
    0 ≤ incidentResidual y ((13/6)*(y-1/2)) := by
  let u := 26*y-13
  let v := 25-26*y
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he : incidentResidual y ((13/6)*(y-1/2)) =
      (1/688590984326433944371200)*(457385925379747*v^8 +
      4394543193257672*u*v^7 +
      18942015709394596*u^2*v^6 +
      44590249882602008*u^3*v^5 +
      59509911158010274*u^4*v^4 +
      44818551623191736*u^5*v^3 +
      18647052254392900*u^6*v^2 +
      3897812357402600*u^7*v +
      278271657147475*u^8) := by
    dsimp [incidentResidual, u, v]
    ring
  rw [he]
  positivity

private theorem highResidual (y : ℝ) (hl : 25/26 ≤ y) (hr : y ≤ 1) :
    0 ≤ incidentResidual y (1) := by
  let u := 26*y-25
  let v := 26-26*y
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have he : incidentResidual y (1) =
      (1/1601442551467200)*(278271657147475*v^8 +
      1948283624181700*u*v^7 +
      5845636604449200*u^2*v^6 +
      9743535182099888*u^3*v^5 +
      9743949848379344*u^4*v^4 +
      5846455024737600*u^5*v^3 +
      1948818341579200*u^6*v^2 +
      278402620225600*u^7*v) := by
    dsimp [incidentResidual, u, v]
    ring
  rw [he]
  positivity

/-- Endpoint-pair half of the local variance certificate of Lemma 7.3. -/
theorem pivotIncidentPairCertificate (positive : Bool) (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    pivotIncidentVariance positive y ≤ 2*(pivotEdgeBudget positive y - pivotIncidentPay positive y) := by
  obtain ⟨h0,h1⟩ := hy
  have hd : 0 < 2-y := by linarith
  cases positive with
  | false =>
    have hBudget : (3/2)*y ≤ (2773/1227)*y*(3-2*y)/(2-y) := by
      apply (le_div_iff₀ hd).2
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    have hMarginal := min_le_left ((3/2)*y) (2*y-y^2)
    simp only [pivotIncidentVariance, pivotIncidentPay, pivotMean, pivotEdgeBudget,
      Bool.false_eq_true, ↓reduceIte]
    linarith
  | true =>
    have hres : 0 ≤ incidentResidual y (pivotRescue y) := by
      rcases le_or_gt y (1/2) with hy | hy
      · have hq : (13/6)*(y-1/2) ≤ 0 := by linarith
        have hmin : min 1 ((13/6)*(y-1/2)) ≤ 0 := (min_le_right _ _).trans hq
        rw [pivotRescue, max_eq_left hmin]
        exact lowResidual y h0 hy
      · rcases le_or_gt y (25/26) with hm | hh
        · have hq₀ : 0 ≤ (13/6)*(y-1/2) := by linarith
          have hq₁ : (13/6)*(y-1/2) ≤ 1 := by linarith
          rw [pivotRescue, min_eq_right hq₁, max_eq_right hq₀]
          exact middleResidual y hy.le hm
        · have hq : 1 ≤ (13/6)*(y-1/2) := by linarith
          rw [pivotRescue, min_eq_left hq, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
          exact highResidual y hh.le h1
    have hp := mul_nonneg (sub_nonneg.mpr h1) hres
    unfold incidentResidual at hp
    have hb : (1012/25)*y^3*(1-y)^5 + (1-(y+(1-y)*pivotRescue y)) ≤
        2*(2773/1227)*(1-y)^2/(2-y) := by
      apply (le_div_iff₀ hd).2
      linarith only [hp]
    simp only [pivotIncidentVariance, pivotIncidentPay, pivotMean, pivotEdgeBudget, ↓reduceIte]
    linarith only [hb]

/-- The full inequality for a signed pair with the variance weights of Lemma 7.3. -/
theorem incidentPairVarianceShape (positive : Bool) (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    2*(1012/25)*(varianceShape positive y)^2*y*(1-y) ≤
      2*(pivotEdgeBudget positive y - pivotIncidentPay positive y) := by
  have h := pivotIncidentPairCertificate positive y hy
  have heq : 2*(1012/25)*(varianceShape positive y)^2*y*(1-y) =
      pivotIncidentVariance positive y := by
    cases positive <;> simp [varianceShape, pivotIncidentVariance]
    ring
  rwa [heq]

end DualSepClusterLP

namespace DualSepClusterLP

private def sum3 {α : Type*} (W : Finset α) (f : α → α → α → ℝ) : ℝ :=
  ∑ u ∈ W, ∑ v ∈ W, ∑ w ∈ W, f u v w

private def sum2 {α : Type*} (W : Finset α) (f : α → α → ℝ) : ℝ :=
  ∑ u ∈ W, ∑ v ∈ W, f u v

private theorem sum3_rotate {α : Type*} (W : Finset α) (f : α → α → α → ℝ) :
    sum3 W (fun u v w => f v w u) = sum3 W f := by
  unfold sum3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem sum3_add {α : Type*} (W : Finset α) (f g : α → α → α → ℝ) :
    sum3 W (fun u v w => f u v w + g u v w) = sum3 W f + sum3 W g := by
  simp [sum3, Finset.sum_add_distrib]

private theorem sum3_smul {α : Type*} (W : Finset α) (a : ℝ) (f : α → α → α → ℝ) :
    sum3 W (fun u v w => a * f u v w) = a * sum3 W f := by
  simp only [sum3,Finset.mul_sum]

private theorem sum3_cyclic {α : Type*} (W : Finset α) (f : α → α → α → ℝ) :
    sum3 W (fun u v w => f u v w + f v w u + f w u v) = 3 * sum3 W f := by
  rw [sum3_add, sum3_add, sum3_rotate W f, sum3_rotate W (fun u v w => f v w u),
    sum3_rotate W f]
  ring

private theorem unorderedSign_swap {n : ℕ} (G : Graph n) (u v : Fin n) :
    unorderedSign G u v = unorderedSign G v u := by simp [unorderedSign,min_comm,max_comm]

private noncomputable def pivotTheta {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v : Fin n) : ℝ :=
  if u=v then 0 else varianceShape (unorderedSign G u v) (pairMass z u v)

private noncomputable def covEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v w : Fin n) : ℝ :=
  pivotTheta G z u v * pivotTheta G z u w * (tripleMass z u v w - pairMass z u v * pairMass z u w)

private noncomputable def residualEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v w : Fin n) : ℝ :=
  pivotEntry G z u v w - (1012/25) * covEntry G z u v w

private theorem residual_self₁ {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v : Fin n) : residualEntry G z u u v = 0 := by
  simp [residualEntry,pivotEntry,covEntry,pivotTheta]

private theorem residual_self₂ {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v : Fin n) : residualEntry G z u v u = 0 := by
  simp [residualEntry,pivotEntry,covEntry,pivotTheta]

private theorem residual_diag {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (hz : PrimalFeasible z) (u v : Fin n) : 0 ≤ residualEntry G z u v v := by
  by_cases h : u=v
  · subst v; rw [residual_self₁]
  have hh := incidentPairVarianceShape (unorderedSign G u v) (pairMass z u v) (pairMass_bounds z hz u v)
  simp only [residualEntry,pivotEntry,covEntry,pivotTheta,h,false_or,if_false,if_true,tripleMass_diagonal]
  linarith only [hh]

private theorem residual_distinct {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v w : Fin n) (h : u ≠ v) (h' : u ≠ w) (h'' : v ≠ w) :
    residualEntry G z u v w = triangleSurplus (unorderedSign G u v) (unorderedSign G u w)
      (unorderedSign G v w) (pairMass z u v) (pairMass z u w) (pairMass z v w) (tripleMass z u v w)/2 := by
  simp only [residualEntry,pivotEntry,covEntry,pivotTheta,triangleSurplus,h,h',h'',false_or,if_false]
  ring

private theorem triangle_cyclic {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (H : TriangleCertificate) (hz : PrimalFeasible z) (u v w : Fin n) :
    0 ≤ residualEntry G z u v w + residualEntry G z v w u + residualEntry G z w u v := by
  by_cases huv : u=v
  · subst v; simpa only [residual_self₁,residual_self₂,zero_add] using (show
      0 ≤ 0+0+residualEntry G z w u u by simpa using residual_diag G z hz w u)
  by_cases hvw : v=w
  · subst w; simpa only [residual_self₁,residual_self₂,add_zero] using residual_diag G z hz u v
  by_cases hwu : w=u
  · subst w; simpa only [residual_self₁,residual_self₂,zero_add,add_zero] using residual_diag G z hz v u
  rw [residual_distinct G z u v w huv (Ne.symm hwu) hvw,
    residual_distinct G z v w u hvw (Ne.symm huv) hwu,
    residual_distinct G z w u v hwu (Ne.symm hvw) huv]
  have hv : tripleMass z v w u = tripleMass z u v w :=
    (tripleMass_swap_right z v w u).trans (tripleMass_swap_left z v u w)
  have hw : tripleMass z w u v = tripleMass z u v w :=
    (tripleMass_swap_left z w u v).trans (tripleMass_swap_right z u w v)
  have h₀ := pivot_frechet z hz u v w
  have h₁ := pivot_frechet z hz v w u
  have h₂ := pivot_frechet z hz w u v
  simp only [hv,hw,pairMass_swap z v u,pairMass_swap z u w,pairMass_swap z w v,
    max_le_iff,le_min_iff] at h₀ h₁ h₂
  have h := H (unorderedSign G u v) (unorderedSign G v w) (unorderedSign G w u)
    (pairMass z u v) (pairMass z v w) (pairMass z w u) (tripleMass z u v w)
    (pairMass_bounds z hz u v) (pairMass_bounds z hz v w) (pairMass_bounds z hz w u)
    h₀.1.1 (by linarith only [h₁.1.2]) (by linarith only [h₂.1.2])
    (by linarith only [h₀.1.2]) h₀.2.1 h₁.2.1 h₂.2.1
  simp only [hv,hw,pairMass_swap z v u,pairMass_swap z u w,pairMass_swap z w v,
    unorderedSign_swap G v u,unorderedSign_swap G u w,unorderedSign_swap G w v]
  linarith only [h]

theorem pivotStepOK_of_triangle (H : TriangleCertificate) {n : ℕ} (G : Graph n)
    (z : Finset (Fin n) → ℝ) (hz : PrimalFeasible z) : PivotStepOK G z := by
  intro W
  let f := residualEntry G z
  have hc : 0 ≤ sum3 W (fun u v w => f u v w + f v w u + f w u v) :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ =>
      triangle_cyclic G z H hz u v w
  rw [sum3_cyclic] at hc
  have hcov : 0 ≤ sum3 W (covEntry G z) := covarianceTotal_nonnegative z hz W (pivotTheta G z)
  have hadd : sum3 W f + (1012/25)*sum3 W (covEntry G z) = sum3 W (pivotEntry G z) := by
    rw [← sum3_smul, ← sum3_add]
    congr 1
    funext u v w
    simp [f,residualEntry]
  change 0 ≤ sum3 W (pivotEntry G z)
  linarith only [hc,hcov,hadd]

end DualSepClusterLP

namespace DualSepClusterLP

private theorem negativeMeanBounds (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ pivotMean false y ∧ pivotMean false y ≤ 1 ∧
      pivotMean false y ≤ pivotEdgeBudget false y := by
  obtain ⟨h0,h1⟩ := hy
  change 0 ≤ min ((3/2)*y) (2*y-y^2) ∧ min ((3/2)*y) (2*y-y^2) ≤ 1 ∧
    min ((3/2)*y) (2*y-y^2) ≤ (2773/1227)*y*(3-2*y)/(2-y)
  refine ⟨le_min (by positivity) ?_, (min_le_right _ _).trans ?_, (min_le_left _ _).trans ?_⟩
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  · nlinarith [sq_nonneg (1-y)]
  · have hd : 0 < 2-y := by linarith
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

private theorem negativeRelease (a b c B : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hc : 0 ≤ c) (hB : c ≤ B) :
    (a+b)/2*c ≤ (a+b-a*b)*B := by
  obtain ⟨ha,ha'⟩ := ha
  obtain ⟨hb,hb'⟩ := hb
  have hu : (a+b)/2 ≤ a+b-a*b := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hb'), mul_nonneg hb (sub_nonneg.mpr ha')]
  have hu' : 0 ≤ a+b-a*b := le_trans (by positivity) hu
  exact (mul_le_mul_of_nonneg_right hu hc).trans (mul_le_mul_of_nonneg_left hB hu')

/-- The complete all-negative sign pattern of the triangle variance certificate.
Its bound needs only that the three pair masses lie in the unit interval. -/
theorem allNegativeTriangleCertificate (x y z h : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ triangleSurplus false false false x z y h +
      triangleSurplus false false false y x z h + triangleSurplus false false false z y x h := by
  obtain ⟨ax,bx,cx⟩ := negativeMeanBounds x hx
  obtain ⟨ay,by',cy⟩ := negativeMeanBounds y hy
  obtain ⟨az,bz,cz⟩ := negativeMeanBounds z hz
  have h₁ := negativeRelease _ _ _ _ ⟨ax,bx⟩ ⟨az,bz⟩ ay cy
  have h₂ := negativeRelease _ _ _ _ ⟨ay,by'⟩ ⟨ax,bx⟩ az cz
  have h₃ := negativeRelease _ _ _ _ ⟨az,bz⟩ ⟨ay,by'⟩ ax cx
  simp only [triangleSurplus, oppositeSlack, pivotGamma, varianceShape, Bool.false_eq_true,
    ↓reduceIte, zero_mul, mul_zero, add_zero, sub_zero]
  linarith only [h₁,h₂,h₃]

end DualSepClusterLP

namespace DualSepClusterLP

private theorem negativeBudgetTwiceMean (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    2*pivotMean false y ≤ pivotEdgeBudget false y := by
  obtain ⟨h0,h1⟩ := hy
  change 2*min ((3/2)*y) (2*y-y^2) ≤ (2773/1227)*y*(3-2*y)/(2-y)
  have hd : 0 < 2-y := by linarith
  have hw : 9/4*(3-2*y) ≤ (2773/1227)*(3-2*y) := by linarith
  rcases le_or_gt y (1/2) with hy | hy
  · apply le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num : (0:ℝ) ≤ 2))
    apply (le_div_iff₀ hd).2
    have e : 3*(2-y) ≤ (2773/1227)*(3-2*y) := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left e h0]
  · apply le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num : (0:ℝ) ≤ 2))
    apply (le_div_iff₀ hd).2
    have e : 2*(2-y)^2 ≤ (2773/1227)*(3-2*y) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy.le)
        (show (0:ℝ) ≤ 5/2 - 2*y by linarith)]
    nlinarith only [mul_le_mul_of_nonneg_left e h0]

private theorem positiveMeanBounds (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    pivotMean true y ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨h0,h1⟩ := hy
  have hq : 0 ≤ pivotRescue y := le_max_left _ _
  have hq' : pivotRescue y ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  change _ ≤ y+(1-y)*pivotRescue y ∧ y+(1-y)*pivotRescue y ≤ _
  constructor
  · exact add_nonneg h0 (mul_nonneg (sub_nonneg.mpr h1) hq)
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hq')]

private theorem unionMean_nonneg {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) : 0 ≤ a+b-a*b := by
  obtain ⟨ha,_⟩ := ha
  obtain ⟨hb,hb'⟩ := hb
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hb')]

/-- Every triangle with exactly one positive sign passes with zero covariance correction.
The representative has its positive sign on the x-edge. -/
theorem onePositiveTriangleCertificate (x y z h : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ triangleSurplus true false false x z y h +
      triangleSurplus false true false y x z h + triangleSurplus false false true z y x h := by
  let a := pivotMean true x
  let b := pivotMean false y
  let c := pivotMean false z
  have ha : a ∈ Set.Icc (0:ℝ) 1 := positiveMeanBounds x hx
  obtain ⟨yb,yb',_⟩ := negativeMeanBounds y hy
  obtain ⟨zc,zc',_⟩ := negativeMeanBounds z hz
  have hb : b ∈ Set.Icc (0:ℝ) 1 := ⟨yb,yb'⟩
  have hc : c ∈ Set.Icc (0:ℝ) 1 := ⟨zc,zc'⟩
  have hB₁ : 1-a ≤ pivotEdgeBudget true x := by
    have hp := incidentPairVarianceShape true x hx
    have hv : 0 ≤ 2*(1012/25)*(varianceShape true x)^2*x*(1-x) :=
      mul_nonneg (mul_nonneg (by positivity) hx.1) (sub_nonneg.mpr hx.2)
    change 2*(1012/25)*(varianceShape true x)^2*x*(1-x) ≤ 2*(pivotEdgeBudget true x-(1-a)) at hp
    linarith
  have hB₂ : 2*b ≤ pivotEdgeBudget false y := negativeBudgetTwiceMean y hy
  have hB₃ : 2*c ≤ pivotEdgeBudget false z := negativeBudgetTwiceMean z hz
  have h₁ := mul_le_mul_of_nonneg_left hB₂ (unionMean_nonneg ha hc)
  have h₂ := mul_le_mul_of_nonneg_left hB₃ (unionMean_nonneg hb ha)
  have h₃ := mul_le_mul_of_nonneg_left hB₁ (unionMean_nonneg hc hb)
  have hrem : 0 ≤ (5-3*a)*b*c :=
    mul_nonneg (mul_nonneg (by linarith [ha.2]) hb.1) hc.1
  simp only [triangleSurplus, oppositeSlack, pivotGamma, varianceShape, Bool.false_eq_true,
    ↓reduceIte, zero_mul, mul_zero, add_zero, sub_zero]
  change 0 ≤ ((a+c-a*c)*pivotEdgeBudget false y-a*c) +
    ((b+a-b*a)*pivotEdgeBudget false z-b*a) +
    ((c+b-c*b)*pivotEdgeBudget true x-(c+b-2*(c*b)))
  linarith only [h₁,h₂,h₃,hrem]

end DualSepClusterLP

namespace DualSepClusterLP

theorem noMoreThanOnePositiveTriangle (s₁ s₂ s₃ : Bool) (x y z h : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (few : ¬ ((s₁ = true ∧ s₂ = true) ∨
      (s₂ = true ∧ s₃ = true) ∨ (s₃ = true ∧ s₁ = true))) :
    0 ≤ triangleSurplus s₁ s₃ s₂ x z y h + triangleSurplus s₂ s₁ s₃ y x z h +
      triangleSurplus s₃ s₂ s₁ z y x h := by
  cases s₁ <;> cases s₂ <;> cases s₃ <;> simp at few
  · exact allNegativeTriangleCertificate x y z h hx hy hz
  · simpa only [add_assoc, add_left_comm, add_comm] using onePositiveTriangleCertificate z x y h hz hx hy
  · simpa only [add_assoc, add_left_comm, add_comm] using onePositiveTriangleCertificate y z x h hy hz hx
  · exact onePositiveTriangleCertificate x y z h hx hy hz

end DualSepClusterLP

namespace DualSepClusterLP

private theorem triangle_between_endpoints (s₁ s₂ s₃ : Bool) (x y z h : ℝ)
    (hh₀ : tripleLower x y z ≤ h) (hh₁ : h ≤ tripleUpper x y z)
    (hends : 0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z (tripleLower x y z) ∧
      0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z (tripleUpper x y z)) :
    0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z h := by
  let F := signedTriangleSurplus s₁ s₂ s₃ x y z
  have affine (t : ℝ) : F t = F 0 + t * (F 1 - F 0) := by
    dsimp only [F, signedTriangleSurplus, triangleSurplus, oppositeSlack]
    split_ifs <;> ring
  change 0 ≤ F h
  change 0 ≤ F _ ∧ 0 ≤ F _ at hends
  by_cases hs : 0 ≤ F 1 - F 0
  · have hm := mul_le_mul_of_nonneg_right hh₀ hs
    linarith only [hm, affine h, affine (tripleLower x y z), hends.1]
  · have hm := mul_le_mul_of_nonpos_right hh₁ (le_of_not_ge hs)
    linarith only [hm, affine h, affine (tripleUpper x y z), hends.2]

end DualSepClusterLP

namespace DualSepClusterLP

private theorem triangleCertificateFromEndpoints : TriangleCertificate := by
  intro s₁ s₂ s₃ x y z h hx hy hz h0 hxy hyz hzx hxu hyu hzu
  by_cases hs : (s₁ = true ∧ s₂ = true) ∨
      (s₂ = true ∧ s₃ = true) ∨ (s₃ = true ∧ s₁ = true)
  · have hl : tripleLower x y z ≤ h := by simp only [tripleLower, max_le_iff]; exact ⟨h0,hxy,hyz,hzx⟩
    have hu : h ≤ tripleUpper x y z := by simp only [tripleUpper, le_min_iff]; exact ⟨hxu,hyu,hzu⟩
    exact triangle_between_endpoints s₁ s₂ s₃ x y z h hl hu
      (positiveTriangleEndpointCertificate s₁ s₂ s₃ hs x y z hx hy hz (hl.trans hu))
  · exact noMoreThanOnePositiveTriangle s₁ s₂ s₃ x y z h hx hy hz hs

end DualSepClusterLP

open DualSepClusterLP

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (n : ℕ) (G : Graph n) (L : SparseWeights n), ValidSupport L →
        ∃ C : Clustering n,
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((roundingInput G L).map M.inputAlphabet.symm)
            (some ((partitionOutput C).map M.outputAlphabet.symm))
            (A * ((roundingInput G L).length + 1)^b)) ∧
          (disagreements G C : ℝ) ≤ (2773 / 2000 : ℝ) *
            primalValue G (fun S => (weightAt L S : ℝ))  := by
  obtain ⟨M, A, b, finiteAlphabets, execute⟩ := conditionalExpectationRoundingTraces
  refine ⟨M, A, b, finiteAlphabets, ?_⟩
  intro n G L valid
  let z := fun S => (weightAt L S : ℝ)
  have hz : PrimalFeasible z := valid.2.2
  obtain ⟨C, P, hc, hp, runs⟩ := execute n G L valid
    (clockStepOK_of_primalFeasible G z hz)
    (pivotStepOK_of_triangle triangleCertificateFromEndpoints G z hz)
  refine ⟨if disagreements G C ≤ disagreements G P then C else P, runs, ?_⟩
  have both := cheaper_le_primal G z hz C P
    (disagreements_le_of_roundTraceOK G C z clusterEdgeBudget hc)
    (disagreements_le_of_roundTraceOK G P z pivotEdgeBudget hp)
  split_ifs with h
  · simpa only [min_eq_left (Nat.cast_le.mpr h : (disagreements G C : ℝ) ≤ disagreements G P)] using both
  · simpa only [min_eq_right (Nat.cast_le.mpr (le_of_not_ge h) : (disagreements G P : ℝ) ≤ disagreements G C)] using both
