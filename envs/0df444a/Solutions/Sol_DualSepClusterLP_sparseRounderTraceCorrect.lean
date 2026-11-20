-- Prove2me | solution 1 for DualSepClusterLP.sparseRounderTraceCorrect
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T13:32:25.395168+00:00
-- url     : https://prove2.me/submissions/cd57b159-a87e-4016-945e-b496db914154

import Definitions.Def_DualSepClusterLP_SparseRounder

namespace DualSepClusterLP.SparsePivot

@[simp] theorem mass_cast {n : ℕ} (L : SparseWeights n) (i j : Fin n) :
    (mass L i j : ℝ) = pairMass (fun S => (weightAt L S : ℝ)) i j := by
  induction L with
  | nil => simp [mass,pairMass,weightAt]
  | cons e L ih =>
    rcases e with ⟨T,t⟩
    simp only [mass,List.map_cons,List.sum_cons,Rat.cast_add] at ih ⊢
    convert congrArg ((if i ∈ T ∧ j ∈ T then (t:ℝ) else 0) + ·) ih using 1
    · split_ifs <;> simp
    · unfold pairMass
      have addform (S : Finset (Fin n)) :
          (if i ∈ S ∧ j ∈ S then (weightAt ((T,t)::L) S : ℝ) else 0) =
            (if S=T then (if i ∈ T ∧ j ∈ T then (t:ℝ) else 0) else 0) +
            (if i ∈ S ∧ j ∈ S then (weightAt L S : ℝ) else 0) := by
        by_cases hs : S=T
        · subst S; by_cases h : i ∈ T ∧ j ∈ T <;> simp [h,weightAt]
        · by_cases h : i ∈ S ∧ j ∈ S <;> simp [h,hs,Ne.symm hs,weightAt]
      simp_rw [addform, Finset.sum_add_distrib, Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem column_mem {n : ℕ} (L : SparseWeights n) (S : Finset (Fin n))
    (h : 0 < weightAt L S) : S ∈ L.map Prod.fst := by
  by_contra hno
  have z : weightAt L S = 0 := by
    unfold weightAt
    rw [List.sum_eq_zero]
    intro a ha
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    split_ifs with heq
    · exact (hno (heq ▸ List.mem_map_of_mem he)).elim
    · rfl
  linarith
end DualSepClusterLP.SparsePivot

namespace DualSepClusterLP.Coins

variable {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Conditional expectation with h fixed and all remaining indicators independently sampled. -/
def multilinearInEach {n : ℕ} (Q : (Fin n → F) → F) : Prop :=
  ∀ x i, Q x = (1 - x i) * Q (Function.update x i 0) + x i * Q (Function.update x i 1)

/-- Fix one Bernoulli outcome, respecting already deterministic probabilities. -/
def chooseBit {n : ℕ} (Q : (Fin n → F) → F) (x : Fin n → F) (i : Fin n) : F :=
  if x i = 0 then 0 else if x i = 1 then 1 else
  if Q (Function.update x i 0) ≤ Q (Function.update x i 1) then 0 else 1

/-- At most two evaluations of the conditional expectation per vertex. -/
def fixCoins {n : ℕ} (Q : (Fin n → F) → F) :
    List (Fin n) → (Fin n → F) → (Fin n → F)
  | [], x => x
  | i::is, x => fixCoins Q is (Function.update x i (chooseBit Q x i))

private theorem chooseBit_bool {n : ℕ} (Q : (Fin n → F) → F) (x : Fin n → F) (i : Fin n) :
    chooseBit Q x i = 0 ∨ chooseBit Q x i = 1 := by
  unfold chooseBit
  split_ifs <;> simp

private theorem chooseBit_le {n : ℕ} (Q : (Fin n → F) → F) (hQ : multilinearInEach Q)
    (x : Fin n → F) (i : Fin n) (h0 : 0 ≤ x i) (h1 : x i ≤ 1) :
    Q (Function.update x i (chooseBit Q x i)) ≤ Q x := by
  have h := hQ x i
  generalize hL : Q (Function.update x i 0) = L at h
  generalize hR : Q (Function.update x i 1) = R at h
  unfold chooseBit
  split_ifs with hzero hone hle
  · simp only [hL, hzero, sub_zero, one_mul, zero_mul, add_zero] at h ⊢
    linarith
  · simp only [hR, hone, sub_self, one_mul, zero_mul, zero_add] at h ⊢
    linarith
  · rw [hL,h] at *
    rw [hL,hR] at hle
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hle)]
  · rw [hL,hR] at hle
    rw [hR,h]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (le_of_not_ge hle))]

theorem fixCoins_spec {n : ℕ} (Q : (Fin n → F) → F) (hQ : multilinearInEach Q)
    (is : List (Fin n)) (x : Fin n → F) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    Q (fixCoins Q is x) ≤ Q x ∧
    (∀ i ∈ is, fixCoins Q is x i = 0 ∨ fixCoins Q is x i = 1) ∧
    (∀ i, x i = 0 ∨ x i = 1 → fixCoins Q is x i = x i) := by
  induction is generalizing x with
  | nil => simp [fixCoins]
  | cons i is ih =>
    let y := Function.update x i (chooseBit Q x i)
    have hyi : y i = 0 ∨ y i = 1 := by simpa [y] using chooseBit_bool Q x i
    have hy (j) : 0 ≤ y j ∧ y j ≤ 1 := by
      by_cases hji : j = i
      · subst j; rcases hyi with he | he <;> rw [he] <;> norm_num
      · simpa [y,Function.update_of_ne hji] using hx j
    obtain ⟨hcost,hbool,hfixed⟩ := ih y hy
    change Q (fixCoins Q is y) ≤ Q x ∧ _
    refine ⟨hcost.trans (chooseBit_le Q hQ x i (hx i).1 (hx i).2), ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with hj | h
      · subst j
        change fixCoins Q is y i = 0 ∨ fixCoins Q is y i = 1
        rw [hfixed i hyi]
        exact hyi
      · exact hbool j h
    · intro j hj
      have he : y j = x j := by
        by_cases hji : j = i
        · subst j; rcases hj with hv | hv <;> simp [y,chooseBit,hv]
        · simp [y,hji]
      exact (hfixed j (he.symm ▸ hj)).trans he

end DualSepClusterLP.Coins

namespace DualSepClusterLP.Coins

variable {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem multilinearConst {n : ℕ} (c : F) :
    multilinearInEach (fun _ : Fin n → F => c) := by intro x i; ring

private theorem multilinearAdd {n : ℕ} {p q : (Fin n → F) → F} (hp : multilinearInEach p)
    (hq : multilinearInEach q) : multilinearInEach (fun x => p x + q x) := by
  intro x i
  linear_combination hp x i + hq x i

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem multilinearSum {n : ℕ} {p : Fin n → (Fin n → F) → F}
    (hp : ∀ k, multilinearInEach (p k)) :
    multilinearInEach (fun x => ∑ k, p k x) := by
  intro x i
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact hp j x i

def pairwiseExpectation {n : ℕ} (c : F) (lin : Fin n → F)
    (quad : Fin n → Fin n → F) (x : Fin n → F) : F :=
  c + ∑ i, (lin i * x i + ∑ j, if i < j then quad i j * x i * x j else 0)

theorem multilinearPairwise {n : ℕ} (c : F) (lin : Fin n → F)
    (quad : Fin n → Fin n → F) : multilinearInEach (pairwiseExpectation c lin quad) := by
  apply multilinearAdd (multilinearConst c)
  apply multilinearSum
  intro i
  apply multilinearAdd
  · intro x k
    by_cases hi : i = k
    · subst i; simp; ring
    · simp [Function.update_of_ne hi]; ring
  · apply multilinearSum
    intro j
    by_cases hij : i < j
    · simp only [hij, if_true]
      intro x k
      by_cases hi : i = k
      · subst i
        simp [Function.update_of_ne (Ne.symm (ne_of_lt hij))]; ring
      · by_cases hj : j = k
        · subst j; simp [Function.update_of_ne hi]; ring
        · simp [Function.update_of_ne hi,Function.update_of_ne hj]; ring
    · simpa [hij] using (multilinearConst (n:=n) (0 : F))

/-- A computable choice of a 0–1 assignment with no larger pairwise conditional
expectation. Coordinates initially forced to zero or one retain their values. -/
theorem deterministicCoinFixing {n : ℕ} (c : F) (lin : Fin n → F)
    (quad : Fin n → Fin n → F) (x : Fin n → F) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    let Q := pairwiseExpectation c lin quad
    let y := fixCoins Q (List.finRange n) x
    Q y ≤ Q x ∧ (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i, x i = 0 ∨ x i = 1 → y i = x i) := by
  dsimp only
  obtain ⟨h,hbool,hfixed⟩ := fixCoins_spec _ (multilinearPairwise c lin quad) (List.finRange n) x hx
  exact ⟨h,fun i => hbool i (List.mem_finRange i),hfixed⟩

end DualSepClusterLP.Coins

namespace DualSepClusterLP

noncomputable def pivotAverage {n : ℕ} (z : Finset (Fin n) → ℝ) (u : Fin n)
    (F : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), (if u ∈ S then z S else 0) * F S

private theorem pivotAvgConst {n : ℕ} {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (u : Fin n) (c : ℝ) : pivotAverage z u (fun _ => c) = c := by
  simp only [pivotAverage, ← Finset.sum_mul, hz.2, one_mul]

private theorem pivotAvgAdd {n : ℕ} (z : Finset (Fin n) → ℝ) (u : Fin n)
    (f g : Finset (Fin n) → ℝ) : pivotAverage z u (fun S => f S + g S) =
    pivotAverage z u f + pivotAverage z u g := by simp [pivotAverage,mul_add,Finset.sum_add_distrib]

private theorem pivotAvgScale {n : ℕ} (z : Finset (Fin n) → ℝ) (u : Fin n)
    (c : ℝ) (f : Finset (Fin n) → ℝ) : pivotAverage z u (fun S => c * f S) =
    c * pivotAverage z u f := by
  simp only [pivotAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def membershipBit {n : ℕ} (v : Fin n) (S : Finset (Fin n)) : ℝ := if v ∈ S then 1 else 0

private theorem pivotAvgBit {n : ℕ} (z : Finset (Fin n) → ℝ) (u v : Fin n) :
    pivotAverage z u (membershipBit v) = pairMass z u v := by
  apply Finset.sum_congr rfl
  intro S _
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [membershipBit,hu,hv]

private theorem pivotAvgBits {n : ℕ} (z : Finset (Fin n) → ℝ) (u v w : Fin n) :
    pivotAverage z u (fun S => membershipBit v S * membershipBit w S) = tripleMass z u v w := by
  apply Finset.sum_congr rfl
  intro S _
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;> simp [membershipBit,hu,hv,hw]

/-- After fixing a distinct pivot and the sampled column, the conditional probability that
v joins is affine in its membership indicator (equation 32). -/
noncomputable def conditionalChance {n : ℕ} (z : Finset (Fin n) → ℝ) (s : Bool)
    (u v : Fin n) (S : Finset (Fin n)) : ℝ :=
  pivotMean s (pairMass z u v) +
    pivotGamma s (pairMass z u v) * (membershipBit v S - pairMass z u v)

theorem avg_conditionalChance {n : ℕ} {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (u v : Fin n) (s : Bool) :
    pivotAverage z u (conditionalChance z s u v) = pivotMean s (pairMass z u v) := by
  let x := pairMass z u v
  let m := pivotMean s x
  let g := pivotGamma s x
  have h : conditionalChance z s u v = fun S => (m-g*x) + g * membershipBit v S := by
    funext S
    unfold conditionalChance m g x; ring
  rw [h,pivotAvgAdd,pivotAvgConst hz,pivotAvgScale,pivotAvgBit]
  change (m-g*x)+g*x=m
  ring

/-- Distinct join coins are independent after selecting the LP column. Averaging their product
over that selection yields the exact pair plus triple mass covariance of equation (38). -/
theorem avg_conditionalChance_product {n : ℕ} {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (u v w : Fin n) (sv sw : Bool) :
    pivotAverage z u (fun S => conditionalChance z sv u v S * conditionalChance z sw u w S) =
    pivotMean sv (pairMass z u v) * pivotMean sw (pairMass z u w) +
      pivotGamma sv (pairMass z u v) * pivotGamma sw (pairMass z u w) *
        (tripleMass z u v w - pairMass z u v * pairMass z u w) := by
  let x := pairMass z u v
  let y := pairMass z u w
  let m := pivotMean sv x
  let m' := pivotMean sw y
  let g := pivotGamma sv x
  let g' := pivotGamma sw y
  let B := m - g*x
  let B' := m' - g'*y
  have h (S) : conditionalChance z sv u v S * conditionalChance z sw u w S =
      ((B*B' + (B'*g)*membershipBit v S) + (B*g') * membershipBit w S) +
         (g*g') * (membershipBit v S * membershipBit w S) := by
    unfold conditionalChance B B' m m' g g' x y; ring
  simp_rw [h]
  rw [pivotAvgAdd,pivotAvgAdd,pivotAvgAdd,pivotAvgConst hz,
      pivotAvgScale,pivotAvgScale,pivotAvgScale,pivotAvgBit,pivotAvgBit,pivotAvgBits]
  dsimp only [B, B', m, m', g, g', x, y]
  ring

/-- Expected edge credit less immediate cost for a pair of conditionally independent join coins;
argument j is their conditional joint probability. -/
noncomputable def conditionalEdgeSlack (positive : Bool) (b x y j : ℝ) : ℝ :=
  b * (x+y-j) - (if positive then x+y-2*j else j)

theorem avg_oppositeSlack {n : ℕ} {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (u v w : Fin n) (sv sw so : Bool) :
    pivotAverage z u (fun S =>
      let x := conditionalChance z sv u v S
      let y := conditionalChance z sw u w S
      conditionalEdgeSlack so (pivotEdgeBudget so (pairMass z v w)) x y (x*y)) =
      oppositeSlack sv sw so (pairMass z u v) (pairMass z u w) (pairMass z v w) (tripleMass z u v w) := by
  let b := pivotEdgeBudget so (pairMass z v w)
  let a : ℝ := b - (if so then 1 else 0)
  let c : ℝ := (if so then 2 else -1) - b
  have h (x y : ℝ) : conditionalEdgeSlack so b x y (x*y) = (a*x+a*y)+c*(x*y) := by
    cases so <;> simp [a,c,conditionalEdgeSlack] <;> ring
  change pivotAverage z u (fun S => conditionalEdgeSlack so b _ _ _) = _
  simp_rw [h]
  rw [pivotAvgAdd,pivotAvgAdd,pivotAvgScale,pivotAvgScale,pivotAvgScale,
      avg_conditionalChance hz, avg_conditionalChance hz, avg_conditionalChance_product hz]
  cases so <;> simp [oppositeSlack,a,b,c] <;> ring

end DualSepClusterLP

namespace DualSepClusterLP

private theorem pivotAvgSum {n : ℕ} (z : Finset (Fin n) → ℝ) (u : Fin n) (W : Finset (Fin n))
    (F : Fin n → Finset (Fin n) → ℝ) :
    pivotAverage z u (fun S => ∑ v ∈ W, F v S) = ∑ v ∈ W, pivotAverage z u (F v) := by
  simp only [pivotAverage, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- With the pivot and LP column fixed, the remaining randomized choices are independent
Bernoulli joins. The function below accepts arbitrary values for those probabilities. -/
noncomputable def pivotCoinEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v w : Fin n) (x : Fin n → ℝ) : ℝ :=
  if u=v ∨ u=w then 0 else if v=w then
    pivotEdgeBudget (unorderedSign G u v) (pairMass z u v) -
      (if unorderedSign G u v then 1 - x v else x v)
  else conditionalEdgeSlack (unorderedSign G v w) (pivotEdgeBudget (unorderedSign G v w) (pairMass z v w))
      (x v) (x w) (x v*x w) / 2

noncomputable def pivotCoinGain {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ) (W : Finset (Fin n))
    (u : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ v ∈ W, ∑ w ∈ W, pivotCoinEntry G z u v w x

noncomputable def sampledChances {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u : Fin n) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun v => if v = u then 1 else conditionalChance z (unorderedSign G u v) u v S

theorem avg_pivotCoinEntry {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (u v w : Fin n) :
    pivotAverage z u (fun S => pivotCoinEntry G z u v w (sampledChances G z u S)) =
    pivotEntry G z u v w := by
  by_cases hp : u=v ∨ u=w
  · simp only [pivotCoinEntry,pivotEntry,hp,if_true]
    apply pivotAvgConst hz
  have hne := not_or.mp hp
  simp only [pivotCoinEntry,pivotEntry,hp,if_false,sampledChances,Ne.symm hne.1,Ne.symm hne.2]
  by_cases heq : v = w
  · subst w
    simp only [if_true]
    let b := pivotEdgeBudget (unorderedSign G u v) (pairMass z u v)
    let s := unorderedSign G u v
    let c : ℝ := if s then b-1 else b
    let a : ℝ := if s then 1 else -1
    have h (x : ℝ) : (b - (if s then 1-x else x)) = c+a*x := by
      cases hs : s <;> simp [a,c,hs] <;> ring
    change pivotAverage z u (fun S => b - (if s then 1-conditionalChance z s u v S else conditionalChance z s u v S)) = _
    simp_rw [h]
    rw [pivotAvgAdd,pivotAvgConst hz,pivotAvgScale,avg_conditionalChance hz]
    change c + a * pivotMean s (pairMass z u v) = b - pivotIncidentPay s (pairMass z u v)
    cases hs : s <;> simp [a,c,hs,pivotIncidentPay] <;> ring
  · simp only [heq, if_false]
    have h := avg_oppositeSlack hz u v w (unorderedSign G u v) (unorderedSign G u w) (unorderedSign G v w)
    convert congrArg (fun a : ℝ => a/2) h using 1
    unfold pivotAverage
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S _
    ring

theorem avg_pivotCoinGain {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (W : Finset (Fin n)) (u : Fin n) :
    pivotAverage z u (fun S => pivotCoinGain G z W u (sampledChances G z u S)) =
      ∑ v ∈ W, ∑ w ∈ W, pivotEntry G z u v w := by
  unfold pivotCoinGain
  rw [pivotAvgSum]
  apply Finset.sum_congr rfl
  intro v _
  rw [pivotAvgSum]
  exact Finset.sum_congr rfl fun w _ => avg_pivotCoinEntry G hz u v w

/-- An actual pivot and positive-mass support column achieve at least the pivot
procedure's required zero margin; both can be selected by enumeration. -/
theorem eligiblePivotAndColumn {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (hstep : PivotStepOK G z) (W : Finset (Fin n)) (hne : W.Nonempty) :
    ∃ u ∈ W, ∃ S : Finset (Fin n), u ∈ S ∧ 0 < z S ∧
      0 ≤ pivotCoinGain G z W u (sampledChances G z u S) := by
  have hava := hstep W
  obtain ⟨u,hu,hU⟩ : ∃ u ∈ W, 0 ≤ ∑ v ∈ W, ∑ w ∈ W, pivotEntry G z u v w := by
    by_contra! hn
    exact (not_lt_of_ge hava) (Finset.sum_neg hn hne)
  refine ⟨u,hu,?_⟩
  by_contra! hn
  have hm : (∑ S : Finset (Fin n), if u ∈ S then z S else 0) ≠ 0 := by rw [hz.2 u]; norm_num
  obtain ⟨T,_,hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have huT : u ∈ T := by by_contra h; simp [h] at hT
  have hzT : 0 < z T := lt_of_le_of_ne (hz.1 T) (Ne.symm (by simpa [huT] using hT))
  rw [← avg_pivotCoinGain G hz] at hU
  apply not_lt_of_ge hU
  unfold pivotAverage
  apply Finset.sum_neg'
  · intro S _
    by_cases huS : u ∈ S
    · rw [if_pos huS]
      by_cases hpos : 0 < z S
      · exact (mul_neg_of_pos_of_neg hpos (hn S huS hpos)).le
      · rw [le_antisymm (le_of_not_gt hpos) (hz.1 S),zero_mul]
    · simp [huS]
  · exact ⟨T,Finset.mem_univ T,by simpa [huT] using mul_neg_of_pos_of_neg hzT (hn T huT hzT)⟩

end DualSepClusterLP

namespace DualSepClusterLP

private theorem pivotMassBounds {n : ℕ} {z : Finset (Fin n) → ℝ} (hz : PrimalFeasible z)
    (i j : Fin n) : 0 ≤ pairMass z i j ∧ pairMass z i j ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro S _
    split_ifs <;> simp [hz.1 S]
  · rw [← hz.2 i]
    apply Finset.sum_le_sum
    intro S _
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi,hj,hz.1 S]

theorem sampledChances_bounds {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (u : Fin n) (S : Finset (Fin n)) (v : Fin n) :
    0 ≤ sampledChances G z u S v ∧ sampledChances G z u S v ≤ 1 := by
  by_cases hv : v = u
  · simp [sampledChances,hv]
  rw [sampledChances,if_neg hv,conditionalChance]
  obtain ⟨hyL,hyU⟩ := pivotMassBounds hz u v
  let y := pairMass z u v
  change 0 ≤ y at hyL
  change y ≤ 1 at hyU
  have hres : 0 ≤ pivotRescue y ∧ pivotRescue y ≤ 1 := by
    unfold pivotRescue
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  cases hs : unorderedSign G u v
  · change 0 ≤ pivotMean false y + pivotGamma false y * _ ∧ _ ≤ 1
    simp only [pivotMean,pivotGamma,Bool.false_eq_true,if_false,zero_mul,add_zero]
    change 0 ≤ min ((3/2)*y) (2*y-y^2) ∧ min ((3/2)*y) (2*y-y^2) ≤ 1
    refine ⟨le_min (by positivity) ?_,(min_le_right _ _).trans ?_⟩
    · nlinarith [mul_nonneg hyL (sub_nonneg.mpr hyU)]
    · nlinarith [sq_nonneg (1-y)]
  · change 0 ≤ pivotMean true y + pivotGamma true y * (membershipBit v S-y) ∧ _ ≤ 1
    simp only [pivotMean,pivotGamma,if_true]
    by_cases hvS : v∈S
    · simp only [membershipBit,if_pos hvS]; constructor <;> nlinarith
    · simp only [membershipBit,if_neg hvS,zero_sub]; constructor <;> nlinarith [hres.1,hres.2]

private theorem multiCoinEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (u v w : Fin n) : Coins.multilinearInEach (pivotCoinEntry G z u v w) := by
  intro x i
  by_cases hp : u=v ∨ u=w
  · simp [pivotCoinEntry,hp]
  by_cases hd : v=w
  · subst w
    have huv := (not_or.mp hp).1
    by_cases hi : v=i
    · subst i
      cases hs : unorderedSign G u v <;> simp [pivotCoinEntry,huv,hs] <;> ring
    · cases hs : unorderedSign G u v <;> simp [pivotCoinEntry,huv,hi,hs] <;> ring
  by_cases hv : v=i
  · subst i
    cases hs : unorderedSign G v w <;> simp [pivotCoinEntry,hp,hd,Ne.symm hd,hs,conditionalEdgeSlack] <;> ring
  · by_cases hw : w=i
    · subst i
      cases hs : unorderedSign G v w <;> simp [pivotCoinEntry,hp,hv,hs,conditionalEdgeSlack] <;> ring
    · cases hs : unorderedSign G v w <;> simp [pivotCoinEntry,hp,hv,hw,hs,hd,conditionalEdgeSlack] <;> ring

private theorem multiCoinGain {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (W : Finset (Fin n)) (u : Fin n) : Coins.multilinearInEach (fun x => -pivotCoinGain G z W u x) := by
  intro x i
  have h : pivotCoinGain G z W u x = (1-x i)*pivotCoinGain G z W u (Function.update x i 0) +
      x i * pivotCoinGain G z W u (Function.update x i 1) := by
    unfold pivotCoinGain
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    exact multiCoinEntry G z u v w x i
  linarith

/-- A live pivot and a positive-weight LP column, followed by at most two conditional
gain evaluations per live coin, yield a definite nonempty cluster with nonnegative gain. -/
theorem deterministicPivotStep {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (hstep : PivotStepOK G z) (W : Finset (Fin n)) (hne : W.Nonempty) :
    ∃ u ∈ W, ∃ S : Finset (Fin n), u ∈ S ∧ 0 < z S ∧
      let y := Coins.fixCoins (fun x => -pivotCoinGain G z W u x)
        (List.finRange n) (sampledChances G z u S)
      (∀ v, y v = 0 ∨ y v = 1) ∧ y u = 1 ∧ 0 ≤ pivotCoinGain G z W u y := by
  obtain ⟨u,hu,S,huS,hzS,hgain⟩ := eligiblePivotAndColumn G hz hstep W hne
  refine ⟨u,hu,S,huS,hzS,?_⟩
  dsimp only
  obtain ⟨hs,hb,hf⟩ := Coins.fixCoins_spec _ (multiCoinGain G z W u) (List.finRange n)
    (sampledChances G z u S) (sampledChances_bounds G hz u S)
  refine ⟨fun v => hb v (List.mem_finRange v),?_,?_⟩
  · have h : sampledChances G z u S u = 1 := by simp [sampledChances]
    exact (hf u (Or.inr h)).trans h
  · linarith

end DualSepClusterLP

namespace DualSepClusterLP
private theorem sparsePairMass_symm {n : ℕ} (z : Finset (Fin n) → ℝ) (i j : Fin n) :
    pairMass z i j = pairMass z j i := by simp [pairMass, and_comm]

noncomputable def realizedEdgeSlack {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (K : Finset (Fin n)) (v w : Fin n) : ℝ :=
  (if v ∈ K ∨ w ∈ K then pivotEdgeBudget (unorderedSign G v w) (pairMass z v w) else 0) -
    (if unorderedSign G v w then (if decide (v ∈ K) != decide (w ∈ K) then 1 else 0)
     else (if v ∈ K ∧ w ∈ K then 1 else 0))

private theorem realizedEdgeSlack_symm {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (K : Finset (Fin n)) (v w : Fin n) : realizedEdgeSlack G z K v w = realizedEdgeSlack G z K w v := by
  have hs : unorderedSign G v w = unorderedSign G w v := by simp [unorderedSign,min_comm,max_comm]
  unfold realizedEdgeSlack
  rw [hs, sparsePairMass_symm z v w]
  by_cases hv : v∈K <;> by_cases hw : w∈K <;> simp [hv,hw]

private theorem realizedEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (W : Finset (Fin n)) (u v w : Fin n) (hu : u∈W) (hv : v∈W) (hw : w∈W)
    (x : Fin n → ℝ) (hbits : ∀ v, x v=0 ∨ x v=1) (hxu : x u=1) :
    let K := W.filter (fun v => x v=1)
    pivotCoinEntry G z u v w x =
      if u=v ∨ u=w then 0 else if v=w then realizedEdgeSlack G z K u v
      else realizedEdgeSlack G z K v w / 2 := by
  dsimp only
  by_cases hp : u=v ∨ u=w
  · simp [pivotCoinEntry,hp]
  simp only [pivotCoinEntry,hp,if_false]
  by_cases h : v=w
  · subst w
    cases hs : unorderedSign G u v <;> rcases hbits v with hb | hb <;>
      simp [realizedEdgeSlack,hxu,hu,hv,hs,hb]
  · simp only [h,if_false]
    cases hs : unorderedSign G v w <;> rcases hbits v with hb | hb <;>
      rcases hbits w with hc | hc <;> norm_num [realizedEdgeSlack,conditionalEdgeSlack,hb,hc,hv,hw,hs]

private theorem pivotSum_eq_unordered {n : ℕ} (R : Finset (Fin n)) (u : Fin n) (hu : u ∉ R)
    (f : Fin n → Fin n → ℝ) (hsymm : ∀ i j, f i j = f j i) :
    (∑ v ∈ insert u R, ∑ w ∈ insert u R,
      if u=v ∨ u=w then 0 else if v=w then f u v else f v w/2) =
      ∑ v ∈ insert u R, ∑ w ∈ insert u R, if v<w then f v w else 0 := by
  let o (v w : Fin n) : ℝ := if v<w then f v w else 0
  have ho (v w : Fin n) (h : v≠w) : o v w + o w v = f v w := by
    rcases lt_or_gt_of_ne h with h | h
    · simp [o,h,not_lt.mpr h.le]
    · simp [o,h,not_lt.mpr h.le,hsymm w v]
  let e (v w : Fin n) : ℝ := if u=v ∨ u=w then 0 else if v=w then f u v else f v w/2
  change (∑ v ∈ insert u R, ∑ w ∈ insert u R, e v w) = ∑ v ∈ insert u R, ∑ w ∈ insert u R, o v w
  have hpoint (v) (hv : v∈R) (w) (hw : w∈R) :
      e v w = (if w=v then f u v else 0) + (o v w + o w v)/2 := by
    have huv : u≠v := fun eq => hu (eq ▸ hv)
    have huw : u≠w := fun eq => hu (eq ▸ hw)
    by_cases eq : v=w
    · subst w; simp [e,huv,o]
    · simp [e,huv,huw,eq,Ne.symm eq,ho v w eq]
  have hinner (v) (hv : v∈R) :
      ∑ w ∈ R, e v w = f u v + ((∑ w ∈ R, o v w)+(∑ w ∈ R, o w v))/2 := by
    rw [Finset.sum_congr rfl (hpoint v hv),Finset.sum_add_distrib,←Finset.sum_div,Finset.sum_add_distrib]
    simp [hv]
  have hleft : (∑ v ∈ insert u R, ∑ w ∈ insert u R, e v w) =
      (∑ v ∈ R, f u v) + ∑ v ∈ R, ∑ w ∈ R, o v w := by
    rw [Finset.sum_insert hu]
    simp only [show (∑ w ∈ insert u R, e u w) = 0 by simp [e],zero_add,Finset.sum_insert hu]
    simp only [show ∀ v, e v u = 0 by simp [e],zero_add]
    rw [Finset.sum_congr rfl hinner,Finset.sum_add_distrib,←Finset.sum_div,Finset.sum_add_distrib]
    rw [show (∑ v ∈ R, ∑ w ∈ R, o w v) = ∑ v ∈ R, ∑ w ∈ R, o v w from Finset.sum_comm]
    ring
  rw [hleft,Finset.sum_insert hu]
  simp only [Finset.sum_insert hu,show o u u=0 by simp [o],zero_add,Finset.sum_add_distrib]
  have hs : (∑ w ∈ R, o u w) + (∑ w ∈ R, o w u) = ∑ w ∈ R, f u w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w hw => ho u w (fun eq => hu (eq ▸ hw))
  linarith

/-- After the join bits are fixed, the signed total of the conditional procedure
is exactly the realized one-round budget less cost on unordered live pairs. -/
theorem pivotCoinGain_eq_realized {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (W : Finset (Fin n)) (u : Fin n) (hu : u∈W) (x : Fin n → ℝ)
    (hb : ∀ v, x v=0 ∨ x v=1) (hx : x u=1) :
    let K := W.filter (fun v => x v=1)
    pivotCoinGain G z W u x = ∑ v ∈ W, ∑ w ∈ W, if v<w then realizedEdgeSlack G z K v w else 0 := by
  dsimp only
  unfold pivotCoinGain
  let K := W.filter (fun v => x v=1)
  calc
    _ = ∑ v ∈ W, ∑ w ∈ W,
        if u=v ∨ u=w then 0 else if v=w then realizedEdgeSlack G z K u v
          else realizedEdgeSlack G z K v w / 2 := by
      exact Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw =>
        realizedEntry G z W u v w hu hv hw x hb hx
    _ = _ := by
      simpa only [Finset.insert_erase hu] using pivotSum_eq_unordered (W.erase u) u
        (Finset.notMem_erase u W) (realizedEdgeSlack G z K) (realizedEdgeSlack_symm G z K)

theorem nonemptyPivotStep_of_primalFeasible {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) (hstep : PivotStepOK G z) (W : Finset (Fin n)) (hne : W.Nonempty) :
    ∃ K ⊆ W, K.Nonempty ∧ (W \ K).card < W.card ∧
      0 ≤ ∑ v ∈ W, ∑ w ∈ W, if v<w then realizedEdgeSlack G z K v w else 0 := by
  obtain ⟨u,hu,S,_,_,hb,hxu,hgain⟩ := deterministicPivotStep G hz hstep W hne
  let x := Coins.fixCoins (fun x => -pivotCoinGain G z W u x) (List.finRange n) (sampledChances G z u S)
  let K := W.filter (fun v => x v=1)
  have huk : u∈K := Finset.mem_filter.mpr ⟨hu,hxu⟩
  have hneq : W \ K ≠ W := by
    intro eq
    have hm : u ∈ W \ K := by simpa only [eq] using hu
    exact (Finset.mem_sdiff.mp hm).2 huk
  refine ⟨K,Finset.filter_subset _ _,⟨u,huk⟩,?_,?_⟩
  · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,hneq⟩)
  · exact (pivotCoinGain_eq_realized G z W u hu x hb hxu) ▸ hgain

end DualSepClusterLP

namespace DualSepClusterLP.SparsePivot

private abbrev weights {n : ℕ} (L : SparseWeights n) := fun S => (weightAt L S : ℝ)
private abbrev liftQ {n : ℕ} (x : Fin n → ℚ) := fun v => (x v : ℝ)

private theorem cast_budget (s : Bool) (y : ℚ) :
    (budget s y : ℝ) = pivotEdgeBudget s y := by
  cases s <;> simp [budget,pivotEdgeBudget]

private theorem cast_rescue (y : ℚ) : (rescue y : ℝ) = pivotRescue y := by
  simp [rescue,pivotRescue]

private theorem cast_initial {n : ℕ} (G : Graph n) (L : SparseWeights n) (u : Fin n)
    (S : Finset (Fin n)) : liftQ (initial G L u S) = sampledChances G (weights L) u S := by
  funext v
  by_cases h : v=u
  · simp [h,liftQ,initial,sampledChances]
  · cases q : unorderedSign G u v <;> by_cases hk : v∈S <;>
      simp [liftQ,initial,sampledChances,h,conditionalChance,chance,pivotMean,pivotGamma,
        q,hk,cast_rescue,membershipBit,weights]

private theorem cast_entry {n : ℕ} (G : Graph n) (L : SparseWeights n) (u v w : Fin n)
    (x : Fin n → ℚ) :
    (entry G L u v w x : ℝ) = pivotCoinEntry G (weights L) u v w (liftQ x) := by
  unfold entry pivotCoinEntry
  by_cases h : u=v ∨ u=w
  · simp [h]
  · by_cases k : v=w
    · simp only [if_neg h,if_pos k]
      cases q : unorderedSign G u v <;> simp [cast_budget,q,liftQ,weights]
    · cases q : unorderedSign G v w <;> simp [h,k,cast_budget,q,liftQ,weights,conditionalEdgeSlack]

private theorem cast_gain {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (x : Fin n → ℚ) :
    (gain G L W u x : ℝ) = pivotCoinGain G (weights L) W u (liftQ x) := by
  simp only [gain,pivotCoinGain,Rat.cast_sum,cast_entry]

private theorem cast_update {n : ℕ} (x : Fin n → ℚ) (i : Fin n) (b : ℚ) :
    liftQ (Function.update x i b) = Function.update (liftQ x) i (b:ℝ) := by
  funext j
  by_cases h : j=i <;> simp [h,liftQ,Function.update_of_ne]

private theorem cast_fix {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (is : List (Fin n)) (x : Fin n → ℚ) :
    liftQ (fix (gain G L W u) is x) =
      Coins.fixCoins (fun y => -pivotCoinGain G (weights L) W u y) is (liftQ x) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    rw [fix,Coins.fixCoins,ih,cast_update]
    congr 2
    unfold Coins.chooseBit
    by_cases h0 : x i = 0
    · simp [liftQ,h0]
    by_cases h1 : x i = 1
    · simp [liftQ,h0,h1]
    have h0' : (x i : ℝ) ≠ 0 := by exact_mod_cast h0
    have h1' : (x i : ℝ) ≠ 1 := by exact_mod_cast h1
    change _ = (if (x i : ℝ)=0 then 0 else if (x i : ℝ)=1 then 1 else _)
    simp only [h0,h1,h0',h1',if_false,neg_le_neg_iff]
    have e (b : ℚ) := cast_gain G L W u (Function.update x i b)
    simp only [cast_update] at e
    have e0 := e 0
    have e1 := e 1
    norm_num only [Rat.cast_zero,Rat.cast_one] at e0 e1
    rw [← e1,← e0]
    simp only [Rat.cast_le]
    split <;> norm_num

theorem cast_margin {n : ℕ} (G : Graph n) (L : SparseWeights n) (W K : Finset (Fin n)) :
    (margin G L W K : ℝ) =
      ∑ v ∈ W, ∑ w ∈ W, if v<w then realizedEdgeSlack G (weights L) K v w else 0 := by
  unfold margin
  simp only [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : v<w <;> by_cases a : v∈K <;> by_cases b : w∈K <;>
    cases q : unorderedSign G v w <;> simp [h,a,b,q,realizedEdgeSlack,cast_budget,weights]

private theorem candidate_subset {n : ℕ} (G : Graph n) (L : SparseWeights n) (W K : Finset (Fin n))
    (h : K ∈ candidates G L W) : K ⊆ W := by
  simp only [candidates,List.mem_flatMap] at h
  obtain ⟨u,_,hu⟩ := h
  split at hu
  · obtain ⟨e,he,heq⟩ := List.mem_filterMap.mp hu
    split at heq
    · simp only [Option.some.injEq] at heq
      rw [←heq]
      exact Finset.filter_subset _ _
    · contradiction
  · simpa using hu

private theorem success {n : ℕ} (G : Graph n) (L : SparseWeights n) (hL : ValidSupport L)
    (hp : PivotStepOK G (weights L)) (W : Finset (Fin n)) (hW : W.Nonempty) :
    ∃ K ∈ candidates G L W, K.Nonempty ∧ 0 ≤ margin G L W K := by
  obtain ⟨u,hu,S,huS,hS,hbits,hfixed,hg⟩ := deterministicPivotStep G hL.2.2 hp W hW
  let r := fix (gain G L W u) (List.finRange n) (initial G L u S)
  let K := cluster G L W u S
  have eqR := cast_fix G L W u (List.finRange n) (initial G L u S)
  rw [cast_initial] at eqR
  change liftQ r = _ at eqR
  rw [←eqR] at hbits hfixed hg
  have eqK : K = W.filter (fun v => liftQ r v = 1) := by
    dsimp only [K,cluster,r,liftQ]
    congr 1
    funext v
    apply propext
    exact_mod_cast Iff.rfl
  have hgood := pivotCoinGain_eq_realized G (weights L) W u hu (liftQ r) hbits hfixed
  rw [←eqK] at hgood
  rw [hgood,←cast_margin] at hg
  refine ⟨K,?_,⟨u,?_⟩,by exact_mod_cast hg⟩
  · have hcol := column_mem L S (by exact_mod_cast hS)
    obtain ⟨e,he,heS⟩ := List.mem_map.mp hcol
    apply List.mem_flatMap.mpr
    refine ⟨u,List.mem_finRange u,?_⟩
    simp only [if_pos hu]
    apply List.mem_filterMap.mpr
    exact ⟨e,he,by simp [heS,huS,K]⟩
  · rw [eqK]
    exact Finset.mem_filter.mpr ⟨hu,hfixed⟩

theorem step_spec {n : ℕ} (G : Graph n) (L : SparseWeights n) (hL : ValidSupport L)
    (hp : PivotStepOK G (fun S => (weightAt L S : ℝ))) (W : Finset (Fin n)) (hW : W.Nonempty) :
    let K := step G L W
    K ⊆ W ∧ K.Nonempty ∧
      0 ≤ ∑ v ∈ W, ∑ w ∈ W, if v<w then realizedEdgeSlack G (fun S => (weightAt L S : ℝ)) K v w else 0 := by
  obtain ⟨K,hm,hN,hg⟩ := success G L hL hp W hW
  dsimp only [step]
  generalize e : List.find? _ (candidates G L W) = o
  cases o with
  | none =>
    have bad := List.find?_eq_none.mp e K hm
    simp [hN,hg] at bad
  | some k =>
    have hb := List.find?_some e
    have h : k.Nonempty ∧ 0 ≤ margin G L W k := of_decide_eq_true hb
    exact ⟨candidate_subset G L W k (List.mem_of_find?_eq_some e),h.1, by
      change 0 ≤ ∑ v ∈ W, ∑ w ∈ W, if v<w then realizedEdgeSlack G (weights L) k v w else 0
      rw [←cast_margin]
      exact_mod_cast h.2⟩

end DualSepClusterLP.SparsePivot

namespace DualSepClusterLP.SparseClock

theorem budget_cast (p : Bool) (y : ℚ) :
    (budget p y : ℝ) = clusterEdgeBudget p (y : ℝ) := by
  cases p <;> simp [budget,clusterEdgeBudget]

theorem pairGain_cast {n : ℕ} (G : Graph n) (L : SparseWeights n) (S : Finset (Fin n))
    (i j : Fin n) :
    (pairGain G L S i j : ℝ) = clockPairSlack G (fun S => (weightAt L S : ℝ)) S i j := by
  simp only [pairGain,clockPairSlack,Rat.cast_sub,apply_ite (fun x : ℚ => (x:ℝ)),
    Rat.cast_zero,Rat.cast_one,budget_cast,SparsePivot.mass_cast]

theorem margin_cast {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) :
    (margin G L W S : ℝ) =
    ∑ i ∈ W, ∑ j ∈ W, if i < j then clockPairSlack G (fun S => (weightAt L S : ℝ)) S i j else 0 := by
  simp only [margin,Rat.cast_sum,apply_ite (fun x : ℚ => (x : ℝ)),pairGain_cast,Rat.cast_zero]

theorem step_spec {n : ℕ} (G : Graph n) (L : SparseWeights n)
    (h : ClockStepOK G (fun S => (weightAt L S : ℝ)))
    (W : Finset (Fin n)) (hn : W.Nonempty) :
    (W ∩ step G L W).Nonempty ∧
    0 ≤ ∑ i ∈ W, ∑ j ∈ W, if i < j then
       clockPairSlack G (fun S => (weightAt L S : ℝ)) (step G L W) i j else 0 := by
  obtain ⟨S,hpos,hi,hg⟩ := h W hn
  rw [←margin_cast] at hg ⊢
  change 0 < (weightAt L S : ℝ) at hpos
  have hw : 0 < weightAt L S := by exact_mod_cast hpos
  have hm := SparsePivot.column_mem L S hw
  let test (K : Finset (Fin n)) := decide ((W ∩ K).Nonempty ∧ 0 ≤ margin G L W K)
  have ht : test S = true := decide_eq_true ⟨hi,by exact_mod_cast hg⟩
  change (W ∩ (((L.map Prod.fst).find? test).getD ∅)).Nonempty ∧ _
  cases he : (L.map Prod.fst).find? test with
  | none => exact False.elim ((List.find?_eq_none.mp he S hm) ht)
  | some K =>
    obtain ⟨hn,hv⟩ := of_decide_eq_true (List.find?_some he : test K = true)
    have eq : step G L W = K := by unfold step; change ((L.map Prod.fst).find? test).getD ∅ = K; rw [he]; rfl
    exact ⟨hn,by rw [eq]; exact_mod_cast hv⟩

end DualSepClusterLP.SparseClock

namespace DualSepClusterLP.RoundFold

theorem remaining_lt {n : ℕ} {pick : Finset (Fin n) → Finset (Fin n)} (hp : Progress pick)
    (W : Finset (Fin n)) (hne : W.Nonempty) : (W \ pick W).card < W.card := by
  obtain ⟨u,hu⟩ := hp W hne
  obtain ⟨huW,hup⟩ := Finset.mem_inter.mp hu
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
  intro eq
  have : u ∈ W \ pick W := eq.symm ▸ huW
  exact (Finset.mem_sdiff.mp this).2 hup

theorem labelAux_lt {n : ℕ} {pick : Finset (Fin n) → Finset (Fin n)} (hp : Progress pick)
    (f : ℕ) (W : Finset (Fin n)) (hf : W.card ≤ f) (i : Fin n) (hi : i ∈ W) :
    labelAux pick f W i < f := by
  induction f generalizing W with
  | zero => obtain rfl := Finset.card_eq_zero.mp (by omega : W.card=0); simp at hi
  | succ f ih =>
    by_cases h : i ∈ pick W
    · simp [labelAux,h]
    · have hdec := remaining_lt hp W ⟨i,hi⟩
      have hr := ih (W \ pick W) (by omega) (Finset.mem_sdiff.mpr ⟨hi,h⟩)
      simpa [labelAux,h] using hr

def clustering {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) (hp : Progress pick) : Clustering n :=
  fun i => ⟨labelAux pick n Finset.univ i,
    labelAux_lt hp n Finset.univ (by simp) i (Finset.mem_univ _)⟩

theorem run_eq_clustering {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) (hp : Progress pick) :
    run pick = clustering pick hp := by
  funext i
  have h := labelAux_lt hp n Finset.univ (by simp) i (Finset.mem_univ _)
  simp [run, clustering, h]

private theorem label_zero {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (f : ℕ) (W : Finset (Fin n)) :
    labelMargin G z B W (labelAux pick (f+1) W) 0 = stepMargin G z B W (pick W) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i ∈ pick W <;> by_cases hj : j ∈ pick W <;>
    simp [labelEntry, stepEntry, labelAux, hi, hj]

private theorem label_succ {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (f : ℕ) (W : Finset (Fin n)) (r : ℕ) :
    labelMargin G z B W (labelAux pick (f+1) W) (r+1) =
      labelMargin G z B (W \ pick W) (labelAux pick f (W \ pick W)) r := by
  let K := pick W
  let R := W \ K
  let l := labelAux pick f R
  let l' := labelAux pick (f+1) W
  have point (i j : Fin n) :
      labelEntry G z B l' (r+1) i j =
        if i ∉ K ∧ j ∉ K then labelEntry G z B l r i j else 0 := by
    by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;>
      simp [l',l,R,K,labelEntry,labelAux,show pick W = K from rfl,hi,hj]
  have eq : R = W.filter (fun i => i ∉ K) := by ext i; simp [R]
  change (∑ i ∈ W, ∑ j ∈ W, labelEntry G z B l' (r+1) i j) = ∑ i ∈ R, ∑ j ∈ R, labelEntry G z B l r i j
  rw [eq]
  simp only [Finset.sum_filter,point]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i ∈ K <;> simp [h]

theorem labelAux_margin {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (hp : Progress pick) (hg : ∀ W, W.Nonempty → 0 ≤ stepMargin G z B W (pick W))
    (f : ℕ) (W : Finset (Fin n)) (hf : W.card ≤ f) (r : ℕ) :
    0 ≤ labelMargin G z B W (labelAux pick f W) r := by
  induction f generalizing W r with
  | zero => obtain rfl := Finset.card_eq_zero.mp (by omega : W.card=0); simp [labelMargin]
  | succ f ih =>
    rcases W.eq_empty_or_nonempty with rfl | hne
    · simp [labelMargin]
    cases r with
    | zero => simpa only [label_zero] using hg W hne
    | succ r =>
      rw [label_succ]
      have hlt := remaining_lt hp W hne
      exact ih (W \ pick W) (by omega) r

theorem clustering_trace {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (pick : Finset (Fin n) → Finset (Fin n))
    (hp : Progress pick) (hg : ∀ W, W.Nonempty → 0 ≤ stepMargin G z B W (pick W)) :
    RoundTraceOK G (clustering pick hp) z B := by
  intro r
  have h := labelAux_margin G z B pick hp hg n Finset.univ (by simp) r.val
  simpa [roundTraceMargin, labelMargin, labelEntry, clustering, ← Fin.val_eq_val] using h

theorem run_trace {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ) (B : Bool → ℝ → ℝ)
    (pick : Finset (Fin n) → Finset (Fin n)) (hp : Progress pick)
    (hg : ∀ W, W.Nonempty → 0 ≤ stepMargin G z B W (pick W)) :
    RoundTraceOK G (run pick) z B := by
  rw [run_eq_clustering pick hp]
  exact clustering_trace G z B pick hp hg

theorem stepMargin_clock {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (W K : Finset (Fin n)) :
    stepMargin G z clusterEdgeBudget W K =
      ∑ i ∈ W, ∑ j ∈ W, if i < j then clockPairSlack G z K i j else 0 := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j <;> by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;>
    cases hg : G i j <;> simp [stepEntry,clockPairSlack,h,hi,hj,hg]

end DualSepClusterLP.RoundFold

namespace DualSepClusterLP.RoundFold

theorem stepMargin_pivot {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (W K : Finset (Fin n)) :
    stepMargin G z pivotEdgeBudget W K =
      ∑ i ∈ W, ∑ j ∈ W, if i < j then realizedEdgeSlack G z K i j else 0 := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j
  · have sign : unorderedSign G i j = G i j := by
      simp [unorderedSign, min_eq_left h.le, max_eq_right h.le]
    by_cases hi : i ∈ K <;> by_cases hj : j ∈ K <;> cases hg : G i j <;>
      simp [stepEntry,realizedEdgeSlack,sign,h,hi,hj,hg]
  · simp [stepEntry,h]

end DualSepClusterLP.RoundFold

namespace DualSepClusterLP.SparseRound

def clockPartition {n : ℕ} (G : Graph n) (L : SparseWeights n) : Clustering n :=
  RoundFold.run (SparseClock.step G L)

def pivotPartition {n : ℕ} (G : Graph n) (L : SparseWeights n) : Clustering n :=
  RoundFold.run (SparsePivot.step G L)

def best {n : ℕ} (G : Graph n) (L : SparseWeights n) : Clustering n :=
  let C := clockPartition G L
  let P := pivotPartition G L
  if disagreements G C ≤ disagreements G P then C else P

theorem traces {n : ℕ} (G : Graph n) (L : SparseWeights n) (hL : ValidSupport L)
    (hclock : ClockStepOK G (fun S => (weightAt L S : ℝ)))
    (hpivot : PivotStepOK G (fun S => (weightAt L S : ℝ))) :
    RoundTraceOK G (clockPartition G L) (fun S => (weightAt L S : ℝ)) clusterEdgeBudget ∧
    RoundTraceOK G (pivotPartition G L) (fun S => (weightAt L S : ℝ)) pivotEdgeBudget := by
  constructor
  · apply RoundFold.run_trace
    · exact fun W hW => (SparseClock.step_spec G L hclock W hW).1
    · intro W hW
      rw [RoundFold.stepMargin_clock]
      exact (SparseClock.step_spec G L hclock W hW).2
  · apply RoundFold.run_trace
    · intro W hW
      obtain ⟨hs,⟨i,hi⟩,_⟩ := SparsePivot.step_spec G L hL hpivot W hW
      exact ⟨i, Finset.mem_inter.mpr ⟨hs hi,hi⟩⟩
    · intro W hW
      rw [RoundFold.stepMargin_pivot]
      exact (SparsePivot.step_spec G L hL hpivot W hW).2.2

theorem best_cost {n : ℕ} (G : Graph n) (L : SparseWeights n) :
    disagreements G (best G L) =
      min (disagreements G (clockPartition G L)) (disagreements G (pivotPartition G L)) := by
  by_cases h : disagreements G (clockPartition G L) ≤ disagreements G (pivotPartition G L)
  · simp only [best, h, if_true, min_eq_left h]
  · simp only [best, h, if_false, min_eq_right (le_of_not_ge h)]

end DualSepClusterLP.SparseRound


namespace DualSepClusterLP.RoundWire

private theorem unary_code (n : ℕ) (s : List Bool) :
    unary (List.replicate n true ++ false :: s) = (n,s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, unary, ih]

private theorem fold_bits (a : ℕ) : a.bits.foldr Nat.bit 0 = a := by
  induction a using Nat.binaryRec' with
  | zero => rfl
  | bit b a h ih => simpa [Nat.bits_append_bit a b h] using congrArg (Nat.bit b) ih

private theorem natField_code (n : ℕ) (s : List Bool) :
    natField (lengthPrefixedNat n ++ s) = (n,s) := by
  simp [natField,lengthPrefixedNat,List.append_assoc,unary_code,fold_bits]

private theorem priceField_code (q : ℚ) (s : List Bool) :
    priceField (priceBits q ++ s) = (q,s) := by
  have signCorrect (a : ℤ) : (if a < 0 then -(a.natAbs:ℤ) else a.natAbs) = a := by
    cases a <;> simp
    omega
  simp only [priceField, priceBits, List.cons_append, List.tail_cons, List.append_assoc, natField_code,
    List.headD_cons, decide_eq_true_eq, signCorrect, Rat.mkRat_self]

private theorem rows_code {n : ℕ} (rows : List (List Bool))
    (h : ∀ r∈rows, r.length = n) (s : List Bool) :
    readRows n rows.length (rows.flatten ++ s) = (rows,s) := by
  induction rows with
  | nil => rfl
  | cons r t ih =>
    have hl := h r List.mem_cons_self
    have ht : ∀ a∈t, a.length=n := fun a ha => h a (List.mem_cons_of_mem _ ha)
    simp [readRows,List.append_assoc,← hl] at *
    rw [ih ht]; simp

private theorem row_get {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.finRange n).map f).getD i.val d = f i := by
  simp [← List.ofFn_eq_map,List.getD_eq_getElem?_getD]

private def entry {n : ℕ} (e : Finset (Fin n) × ℚ) :=
  (List.finRange n).map (fun i => decide (i∈e.1)) ++ priceBits e.2

private theorem readEntries_code {n : ℕ} (L : SparseWeights n) (s : List Bool) :
    readEntries n L.length (L.flatMap entry ++ s) = L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rcases e with ⟨T,q⟩
    let hbits := (List.finRange n).map (fun i => decide (i∈T))
    have hlen : hbits.length = n := by simp [hbits]
    let tail := L.flatMap entry ++ s
    change readEntries n (L.length+1) ((hbits ++ priceBits q) ++ L.flatMap entry ++ s) = _
    simp only [List.append_assoc]
    have hd : (hbits ++ (priceBits q ++ tail)).drop n = priceBits q ++ tail := by
      rw [←hlen,List.drop_left]
    have hm : Finset.univ.filter (fun i : Fin n => (hbits ++ (priceBits q ++ tail)).getD i.val false) = T := by
      ext i
      have hi : i.val<hbits.length := hlen.symm ▸ i.isLt
      have eq : (hbits ++ (priceBits q ++ tail)).getD i.val false = decide (i ∈ T) := by
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hi,←List.getD_eq_getElem?_getD]
        exact row_get _ i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq, decide_eq_true_eq]
    change (Finset.univ.filter (fun i : Fin n => (hbits ++ (priceBits q ++ tail)).getD i.val false),
      (priceField ((hbits ++ (priceBits q ++ tail)).drop n)).1) ::
      readEntries n L.length (priceField ((hbits ++ (priceBits q ++ tail)).drop n)).2 = _
    rw [hd,priceField_code,hm]; exact congrArg (List.cons (T,q)) ih

private theorem count_le {n : ℕ} (L : SparseWeights n) : L.length ≤ (L.flatMap entry).length := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,entry,priceBits,List.length_map,
      List.length_finRange] at *
    omega

theorem decode_roundingInput {n : ℕ} (G : Graph n) (L : SparseWeights n) :
    decode (roundingInput G L) = ⟨n,upper G,L⟩ := by
  let rows := (List.finRange n).map (fun i => (List.finRange n).map (upper G i))
  let es := L.flatMap entry
  have hlen : rows.length=n := by simp [rows]
  have he : roundingInput G L = false :: (List.replicate n true ++ false ::
      (rows.flatten ++ (lengthPrefixedNat L.length ++ es))) := by
    simp only [roundingInput,graphInput,matrixBits,rows,es,List.append_assoc,List.flatMap_def,
      List.replicate_zero,List.nil_append,List.cons_append]
    rfl
  have hrows : readRows n n (rows.flatten ++ (lengthPrefixedNat L.length ++ es)) =
      (rows,lengthPrefixedNat L.length ++ es) := by
    have hw : ∀ r∈rows, r.length=n := by
      intro r hr; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr; simp
    simpa only [hlen] using rows_code rows hw (lengthPrefixedNat L.length ++ es)
  have hfun : (fun i j : Fin n => (rows.getD i.val []).getD j.val false) = upper G := by
    funext i j
    change (((List.finRange n).map (fun i => (List.finRange n).map (upper G i))).getD i.val []).getD j.val false = _
    rw [row_get,row_get]
  have hentry : readEntries n L.length es = L := by simpa [es] using readEntries_code L []
  rw [he]; unfold decode
  change decodeBody (unary (List.replicate n true ++ false :: _)) = _
  rw [unary_code]
  have hk : min L.length es.length = L.length := min_eq_left (count_le L)
  simp only [decodeBody,hrows,natField_code,hk,hfun,hentry]

end DualSepClusterLP.RoundWire

namespace DualSepClusterLP.RoundWire

private theorem unordered_upper {n : ℕ} (G : Graph n) {i j : Fin n} (h : i ≠ j) :
    unorderedSign (upper G) i j = unorderedSign G i j := by
  rcases lt_or_gt_of_ne h with h | h <;>
    simp [unorderedSign, upper, min_eq_left, max_eq_right, min_eq_right, max_eq_left,
      h, le_of_lt h]

theorem upper_clock {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (h : ClockStepOK G z) : ClockStepOK (upper G) z := by
  intro W hW
  obtain ⟨S,hz,hs,hm⟩ := h W hW
  refine ⟨S,hz,hs,?_⟩
  convert hm using 1
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  by_cases hij : i<j <;> simp [hij,clockPairSlack,upper]

theorem upper_pivot {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (h : PivotStepOK G z) : PivotStepOK (upper G) z := by
  intro W
  convert h W using 1
  apply Finset.sum_congr rfl; intro u hu
  apply Finset.sum_congr rfl; intro v hv
  apply Finset.sum_congr rfl; intro w hw
  by_cases huv : u=v; · simp [huv,pivotEntry]
  by_cases huw : u=w; · simp [huw,pivotEntry]
  by_cases hvw : v=w
  · simp [pivotEntry,huv,huw,hvw,unordered_upper G huw]
  · simp [pivotEntry,huv,huw,hvw,unordered_upper G huv,unordered_upper G huw,unordered_upper G hvw]

theorem of_upper_trace {n : ℕ} (G : Graph n) (C : Clustering n) (z : Finset (Fin n) → ℝ)
    (f : Bool → ℝ → ℝ) (h : RoundTraceOK (upper G) C z f) : RoundTraceOK G C z f := by
  intro r; convert h r using 1
  unfold roundTraceMargin
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  by_cases hij : i<j <;> simp [hij,upper]

theorem disagreements_upper {n : ℕ} (G : Graph n) (C : Clustering n) :
    disagreements (upper G) C = disagreements G C := by
  unfold disagreements
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  by_cases hij : i<j <;> simp [hij,upper]

end DualSepClusterLP.RoundWire

open DualSepClusterLP

theorem solution {n : ℕ} (G : Graph n) (L : SparseWeights n)
    (hL : ValidSupport L) (hc : ClockStepOK G (fun S => (weightAt L S : ℝ)))
    (hp : PivotStepOK G (fun S => (weightAt L S : ℝ))) :
    ∃ C P : Clustering n,
      RoundTraceOK G C (fun S => (weightAt L S : ℝ)) clusterEdgeBudget ∧
      RoundTraceOK G P (fun S => (weightAt L S : ℝ)) pivotEdgeBudget ∧
      RoundWire.output (roundingInput G L) =
        partitionOutput (if disagreements G C ≤ disagreements G P then C else P) := by
  let U := RoundWire.upper G
  let C := SparseRound.clockPartition U L
  let P := SparseRound.pivotPartition U L
  obtain ⟨hC,hP⟩ := SparseRound.traces U L hL
    (RoundWire.upper_clock G _ hc) (RoundWire.upper_pivot G _ hp)
  refine ⟨C,P,RoundWire.of_upper_trace G C _ _ hC,RoundWire.of_upper_trace G P _ _ hP,?_⟩
  unfold RoundWire.output
  rw [RoundWire.decode_roundingInput]
  change partitionOutput (if disagreements (RoundWire.upper G) C ≤ disagreements (RoundWire.upper G) P then C else P) = _
  rw [RoundWire.disagreements_upper,RoundWire.disagreements_upper]
