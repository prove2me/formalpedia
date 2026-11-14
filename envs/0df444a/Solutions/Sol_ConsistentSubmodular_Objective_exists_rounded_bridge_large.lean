-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_rounded_bridge_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:59.298637+00:00
-- url     : https://prove2.me/submissions/2395dee2-dc91-4e22-a66e-881f5dae1fdb

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeRounding
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_inter_zero
import Theorems.Thm_ConsistentSubmodular_Objective_two_vertex_bridge
import Theorems.Thm_ConsistentSubmodular_BridgeGrid_step
import Theorems.Thm_ConsistentSubmodular_BridgeGrid_forced_set
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_insertion_path
import Theorems.Thm_ConsistentSubmodular_physical_intersection_lower
import Theorems.Thm_ConsistentSubmodular_exists_joint_rounding
import Theorems.Thm_ConsistentSubmodular_Objective_contractOn_singleton_cap
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_chain_fin
import Theorems.Thm_ConsistentSubmodular_RoundingBudget_bridge_value_budget_exp

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

namespace Objective

variable (f : Objective n)

theorem subadditive (A B : Finset (Fin n)) :
    f.value (A ∪ B) ≤ f.value A + f.value B := by
  have h := f.union_le A B
  have h0 := f.nonnegative ∅
  linarith

end Objective

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n m : ℕ}

theorem physicalProbability_nonnegative
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) : 0 ≤ physicalProbability cores p e := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · rfl

theorem physicalProbability_le_mass
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) :
    physicalProbability cores p e ≤ ∑ i, p i := by
  exact Finset.sum_le_sum (fun i _ => by split_ifs <;> simp_all)

theorem physicalProbability_mem_unitInterval
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : IsSimplex p) (e : Fin n) :
    0 ≤ physicalProbability cores p e ∧ physicalProbability cores p e ≤ 1 := by
  exact ⟨physicalProbability_nonnegative cores p hp.1 e,
    (physicalProbability_le_mass cores p hp.1 e).trans_eq hp.2⟩

theorem physicalProbability_total
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m) :
    (∑ e, physicalProbability cores p e) = ∑ i, p i * (cores i).card := by
  unfold physicalProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

theorem physicalProbability_total_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) ≤ 1)
    {k : ℕ} (hcore : ∀ i, (cores i).card ≤ k) :
    (∑ e, physicalProbability cores p e) ≤ k := by
  rw [physicalProbability_total]
  calc
    (∑ i, p i * (cores i).card) ≤ ∑ i, p i * (k : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcore i)) (hp i))
    _ = (∑ i, p i) * k := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg k)
    _ = k := one_mul _

theorem physicalProbability_vertex
    (cores : Fin (m + 1) → Finset (Fin n)) (i : Fin (m + 1)) (e : Fin n) :
    physicalProbability cores (vertex i) e = if e ∈ cores i then 1 else 0 := by
  classical
  unfold physicalProbability vertex
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem physicalProbability_abs_difference_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m) (e : Fin n) :
    |physicalProbability cores p e - physicalProbability cores q e| ≤
      physicalProbability cores (fun i => |p i - q i|) e := by
  unfold physicalProbability
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp

/-- Expected changes along a shared-threshold transition are bounded by the
type L1 distance times core capacity, with repeated physical elements counted
only once in the actual recourse. -/
theorem physicalProbability_l1_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m)
    {k : ℕ} (hcore : ∀ i, (cores i).card ≤ k) :
    (∑ e, |physicalProbability cores p e - physicalProbability cores q e|) ≤
      (k : ℝ) * ∑ i, |p i - q i| := by
  calc
    _ ≤ ∑ e, physicalProbability cores (fun i => |p i - q i|) e :=
      Finset.sum_le_sum (fun e _ => physicalProbability_abs_difference_le cores p q e)
    _ = ∑ i, |p i - q i| * (cores i).card := physicalProbability_total _ _
    _ ≤ ∑ i, |p i - q i| * (k : ℝ) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcore i)) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_univ [Fintype ι] (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation Finset.univ p v = finiteExpectation p v := by
  simp [sampleExpectation, finiteExpectation, subsetWeight, bernoulliWeight,
    Finset.compl_eq_univ_sdiff]

theorem sampleExpectation_congr (U : Finset ι) (p : ι → ℝ) {v w : Finset ι → ℝ}
    (h : ∀ S ⊆ U, v S = w S) : sampleExpectation U p v = sampleExpectation U p w := by
  exact Finset.sum_congr rfl (fun S hS => by rw [h S (Finset.mem_powerset.mp hS)])

theorem sampleExpectation_sub (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) :
    sampleExpectation U p (fun S => v S - w S) = sampleExpectation U p v - sampleExpectation U p w := by
  simp only [sampleExpectation, mul_sub, Finset.sum_sub_distrib]

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem append_property (Q : SetOperationPath n) (hjoin)
    (good : Finset (Fin n) → Prop) (hP : ∀ i, good (P.node i))
    (hQ : ∀ i, good (Q.node i)) : ∀ i, good ((P.append Q hjoin).node i) := by
  intro i
  change good (if i ≤ P.length then P.node i else Q.node (i - P.length))
  split
  · exact hP i
  · exact hQ _

end SetOperationPath

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace BridgeGrid

variable {n : ℕ}

theorem simplex (K : ℕ) (hK : 0 < K) (j : Fin (K + 1)) : IsSimplex (point K j) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  apply (simplex_vertex _).mix (simplex_vertex _) (by positivity)
  apply (div_le_one hk).mpr
  exact_mod_cast (show j.val ≤ K by omega)

theorem total_step (K : ℕ) (hK : 0 < K) :
    (∑ j : Fin K, typeL1 (point K j.castSucc) (point K j.succ)) ≤ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => step K hK j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have he : (K : ℝ) * (2 / K) = 2 := by field_simp
  rwa [he] at h

theorem type_value (f : Objective n) (A B Q : Finset (Fin n))
    (V : ℝ) (hV : 0 ≤ V) (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B))
    (K : ℕ) (hK : 0 < K) (j : Fin (K + 1)) :
    (3 : ℝ) / 4 * V ≤ finiteExpectation (point K j) (f.onTypes ![A, B] Q).value := by
  apply (f.onTypes ![A, B] Q).two_vertex_bridge 0 1 (by decide) V hV
    (by simpa using hA) (by simpa using hB)
  · positivity
  · apply (div_le_one (show (0 : ℝ) < K by exact_mod_cast hK)).mpr
    exact_mod_cast (show j.val ≤ K by omega)

end BridgeGrid

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

theorem contractOn_le (U B S : Finset (Fin n)) :
    (f.contractOn U B).value S ≤ f.value (S ∩ U) := by
  have h := f.subadditive B (S ∩ U)
  change f.value (B ∪ (S ∩ U)) - f.value B ≤ f.value (S ∩ U)
  linarith

theorem contractOn_expectation_eq (U B : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ e ∉ U, p e = 0) :
    finiteExpectation p (f.contractOn U B).value =
      finiteExpectation p (fun S => f.value (B ∪ S)) - f.value B := by
  rw [← sampleExpectation_univ, ← sampleExpectation_univ]
  rw [sampleExpectation_inter_zero U Finset.univ p hp,
    sampleExpectation_inter_zero U Finset.univ p hp, Finset.univ_inter]
  have he : sampleExpectation U p (f.contractOn U B).value =
      sampleExpectation U p (fun S => f.value (B ∪ S) - f.value B) := by
    apply sampleExpectation_congr
    intro S hS
    simp [contractOn, Finset.inter_eq_left.mpr hS]
  rw [he, sampleExpectation_sub, sampleExpectation_const]

theorem contractOn_expectation_add_forced_lower (U D Q : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hsupport : ∀ e ∉ U, p e = 0) :
    finiteExpectation p (fun S => f.value (Q ∪ S)) - f.value (D ∪ Q) ≤
      finiteExpectation p (f.contractOn U (D ∪ Q)).value := by
  rw [f.contractOn_expectation_eq U (D ∪ Q) p hsupport]
  apply sub_le_sub_right
  exact finiteExpectation_mono p hp (fun S => f.monotone _ _
    (Finset.union_subset_union_left Finset.subset_union_right))

end ConsistentSubmodular.Objective

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace SetOperationPath

variable {n : ℕ}

theorem prepend_forced (P : SetOperationPath n) (A D U : Finset (Fin n))
    (B : ℕ) (good : Finset (Fin n) → Prop)
    (hmono : ∀ S T, S ⊆ T → good S → good T)
    (hstart : P.node 0 = D ∪ A) (hA : good A)
    (hAU : A ⊆ U) (hDU : D ⊆ U) (hcard : A.card + D.card ≤ B)
    (hP : ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i)) :
    ∃ R : SetOperationPath n,
      R.length = D.card + P.length ∧ R.node 0 = A ∧
      R.node R.length = P.node P.length ∧
      ∀ i, R.node i ⊆ U ∧ (R.node i).card ≤ B ∧ good (R.node i) := by
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path A D
  have hj : L.node L.length = P.node 0 := by rw [hLterm, hstart, Finset.union_comm]
  refine ⟨L.append P hj, by simp [hLlen], by simpa using hLinit, ?_, ?_⟩
  · exact L.append_terminal P hj
  · apply L.append_property P hj (fun S => S ⊆ U ∧ S.card ≤ B ∧ good S) _ hP
    intro i
    exact ⟨(hLnode i).2.trans (Finset.union_subset hAU hDU),
      (Finset.card_le_card (hLnode i).2).trans ((Finset.card_union_le _ _).trans hcard),
      hmono _ _ (hLnode i).1 hA⟩

theorem append_unforced (P : SetOperationPath n) (A D U : Finset (Fin n))
    (B : ℕ) (good : Finset (Fin n) → Prop)
    (hmono : ∀ S T, S ⊆ T → good S → good T)
    (hend : P.node P.length = D ∪ A) (hA : good A)
    (hAU : A ⊆ U) (hDU : D ⊆ U) (hcard : A.card + D.card ≤ B)
    (hP : ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i)) :
    ∃ R : SetOperationPath n,
      R.length = P.length + D.card ∧ R.node 0 = P.node 0 ∧
      R.node R.length = A ∧
      ∀ i, R.node i ⊆ U ∧ (R.node i).card ≤ B ∧ good (R.node i) := by
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path A D
  have hj : P.node P.length = L.reverse.node 0 := by
    rw [reverse_initial, hLterm, hend, Finset.union_comm]
  refine ⟨P.append L.reverse hj, by simp [reverse, hLlen], by simp, ?_, ?_⟩
  · simpa using (P.append_terminal L.reverse hj).trans ((reverse_terminal L).trans hLinit)
  · apply P.append_property L.reverse hj (fun S => S ⊆ U ∧ S.card ≤ B ∧ good S) hP
    intro i
    exact ⟨(hLnode _).2.trans (Finset.union_subset hAU hDU),
      (Finset.card_le_card (hLnode _).2).trans ((Finset.card_union_le _ _).trans hcard),
      hmono _ _ (hLnode _).1 hA⟩

end SetOperationPath

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular

theorem lt_two_pow_logBudget (x : ℕ) : x < 2 ^ logBudget x :=
  Nat.lt_pow_succ_log_self (by norm_num) x

theorem one_le_logBudget (x : ℕ) : 1 ≤ logBudget x := Nat.le_add_left 1 _

namespace RoundingBudget

/-- `exp (-c) ≤ 1 / B` once `B ≤ 2 ^ c`. -/
theorem exp_neg_le_inv_of_le_two_pow {B c : ℕ} (hB : 0 < B) (hc : B ≤ 2 ^ c) :
    Real.exp (-(c : ℝ)) ≤ 1 / B := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ c ≤ Real.exp c := by
    calc (2 : ℝ) ^ c ≤ Real.exp 1 ^ c := pow_le_pow_left₀ (by norm_num) h2 c
      _ = Real.exp c := by rw [← Real.exp_nat_mul, mul_one]
  have hBr : (B : ℝ) ≤ Real.exp c := (by exact_mod_cast hc : (B : ℝ) ≤ 2 ^ c).trans hpow
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast hB) hBr

/-- The cardinality tail of deviation `κ / N` fits the per-test budget once
`κ ≥ 4 N² c` and `4 B ≤ 2 ^ c`. -/
theorem size_budget_exp (B N c : ℕ) (κ : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hc : 4 * B ≤ 2 ^ c) (hκ : 4 * (N : ℝ) ^ 2 * c ≤ κ) (hκpos : 0 < κ) :
    Real.exp (-((κ / N) ^ 2) / (4 * κ)) ≤ 1 / (4 * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hexp : -((κ / N) ^ 2) / (4 * κ) = -(κ / (4 * (N : ℝ) ^ 2)) := by
    field_simp
  rw [hexp]
  have hge : (c : ℝ) ≤ κ / (4 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h := exp_neg_le_inv_of_le_two_pow (B := 4 * B) (by positivity) hc
  push_cast at h
  exact (Real.exp_le_exp.mpr (neg_le_neg hge)).trans h

/-- Common per-test budget, with one quarter reserved for total operations. -/
theorem union_budget (B d e : ℝ) (hB : 0 < B) (hd : d ≤ B) (he : e ≤ B) :
    d * (1 / (4 * B)) + e * (1 / (4 * B)) + (1 : ℝ) / 4 < 1 := by
  have hp : (0 : ℝ) ≤ 1 / (4 * B) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hd hp
  have h2 := mul_le_mul_of_nonneg_right he hp
  have hcancel : B * (1 / (4 * B)) = (1 : ℝ) / 4 := by field_simp
  rw [hcancel] at h1 h2
  linarith

end RoundingBudget

end ConsistentSubmodular

end

section

open scoped BigOperators
open ConsistentSubmodular
set_option maxHeartbeats 2000000
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (A B Q : Finset (Fin n)) (N κ : ℕ) (V : ℝ)
    (hN : 0 < N) (hκ : bridgeHeavy N ≤ κ) (hV : 0 < V)
    (hAc : A.card ≤ κ) (hBc : B.card ≤ κ) (hAv : f.value A ≤ V) (hBv : f.value B ≤ V)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧ P.length ≤ 10 * κ ∧
      ∀ j, P.node j ⊆ A ∪ B ∧ ((P.node j).card : ℝ) ≤ κ + (κ : ℝ) / N + bridgeHeavy N ∧
        ((3 : ℝ) / 4 - 2 / N) * V ≤ f.value (Q ∪ P.node j) := by
  classical
  let K := 2 * N
  let H := bridgeHeavy N
  let U := A ∪ B
  let cores : Fin 2 → Finset (Fin n) := ![A, B]
  let z := fun j : Fin (K + 1) => physicalProbability cores (BridgeGrid.point K j)
  have hK : 0 < K := by dsimp [K]; omega
  have hH : 0 < H := by
    have := one_le_logBudget (4 * (2 * N + 1))
    dsimp [H, bridgeHeavy]; positivity
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < H := by exact_mod_cast hH
  have hk : (0 : ℝ) < κ := by exact_mod_cast lt_of_lt_of_le hH hκ
  have hdim : (0 : ℝ) < K + 1 := by positivity
  have hU : f.value U ≤ 2 * V := by
    have h := f.subadditive A B
    dsimp [U]
    linarith
  obtain ⟨D, hDU, hDcard, hDcap⟩ := BridgeGrid.forced_set f U H hH V hV hU
  let g := f.contractOn U (D ∪ Q)
  have hcores (i : Fin 2) : (cores i).card ≤ κ := by fin_cases i <;> assumption
  have hcoreV (i : Fin 2) : f.value (cores i) ≤ V := by fin_cases i <;> assumption
  have hz (j : Fin (K + 1)) (e : Fin n) : 0 ≤ z j e ∧ z j e ≤ 1 :=
    physicalProbability_mem_unitInterval cores _ (BridgeGrid.simplex K hK j) e
  have hsupport (j : Fin (K + 1)) (e : Fin n) (he : e ∉ U) : z j e = 0 := by
    have heA : e ∉ A := fun h => he (Finset.mem_union_left B h)
    have heB : e ∉ B := fun h => he (Finset.mem_union_right A h)
    simp [z, cores, physicalProbability, Fin.sum_univ_two, heA, heB]
  have hmincube (j : Fin K) (e : Fin n) :
      0 ≤ min (z j.castSucc e) (z j.succ e) ∧ min (z j.castSucc e) (z j.succ e) ≤ 1 :=
    ⟨le_min (hz _ e).1 (hz _ e).1, (min_le_left _ _).trans (hz _ e).2⟩
  have hsize (j : Fin (K + 1)) : (∑ e, z j e) ≤ κ :=
    physicalProbability_total_le cores _ (BridgeGrid.simplex K hK j).1
      (BridgeGrid.simplex K hK j).2.le hcores
  have hmean (j : Fin K) :
      finiteExpectation (fun e => min (z j.castSucc e) (z j.succ e)) g.value ≤ 2 * V := by
    have hp (S : Finset (Fin n)) : g.value S ≤ 2 * V :=
      (f.contractOn_le U (D ∪ Q) S).trans ((f.monotone _ _ Finset.inter_subset_right).trans hU)
    simpa only [finiteExpectation_const] using finiteExpectation_mono _ (hmincube j) hp
  have htotal : (∑ j : Fin K, ∑ e, |z j.castSucc e - z j.succ e|) ≤ 2 * κ := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin K) _ =>
      physicalProbability_l1_le cores (BridgeGrid.point K j.castSucc)
        (BridgeGrid.point K j.succ) hcores)
    change (∑ j : Fin K, ∑ e, |z j.castSucc e - z j.succ e|) ≤
      ∑ j : Fin K, (κ : ℝ) * typeL1 (BridgeGrid.point K j.castSucc) (BridgeGrid.point K j.succ) at hs
    rw [← Finset.mul_sum] at hs
    have hb := mul_le_mul_of_nonneg_left (BridgeGrid.total_step K hK) hk.le
    nlinarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = logBudget (4 * (K + 1)) := ⟨_, rfl⟩
  have hc : 4 * (K + 1) ≤ 2 ^ c := hcdef ▸ (lt_two_pow_logBudget _).le
  have hHeq : H = 8 * N ^ 2 * c := by rw [hcdef]; rfl
  have hlarge : 4 * (N : ℝ) ^ 2 * c ≤ κ := by
    have hHκ : H ≤ κ := hκ
    have h4 : 4 * N ^ 2 * c ≤ H := by
      rw [hHeq]
      exact Nat.mul_le_mul_right c (Nat.mul_le_mul_right (N ^ 2) (by norm_num))
    exact_mod_cast h4.trans hHκ
  have hsizeBudget : Real.exp (-(((κ : ℝ) / N) ^ 2) / (4 * κ)) ≤ 1 / (4 * ((K : ℝ) + 1)) := by
    have h := RoundingBudget.size_budget_exp (K + 1) N c κ (by omega) hN hc hlarge hk
    push_cast at h
    exact h
  have hvalueBudget : Real.exp (-((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V))) ≤ 1 / (4 * ((K : ℝ) + 1)) := by
    have h := RoundingBudget.bridge_value_budget_exp (K + 1) N c H V (by omega) hN hV hH hc
      hHeq.ge
    push_cast at h
    exact h
  have hb2 : (κ : ℝ) / N ≤ 2 * κ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := div_le_self hk.le hN1
    linarith
  have hbudget : ((K + 1 : ℕ) : ℝ) * (1 / (4 * ((K : ℝ) + 1)))+
      (Fintype.card (Fin K) : ℝ) * (1 / (4 * ((K : ℝ) + 1))) + (1 : ℝ) / 4 < 1 := by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact RoundingBudget.union_budget _ _ _ hdim le_rfl (by linarith)
  obtain ⟨S, hzero, hone, hcards, hvalues, hcost, _⟩ := exists_joint_rounding z hz
    (fun _j : Fin K => g) Fin.castSucc Fin.succ Fin.castSucc Fin.succ
    (κ : ℝ) (2 * V / H) (2 * V) (V / N) ((κ : ℝ) / N) (8 * κ)
    (1 / (4 * ((K : ℝ) + 1))) (1 / (4 * ((K : ℝ) + 1))) ((1 : ℝ) / 4)
    (by positivity) (by positivity) hb2 (by positivity) (by positivity) (by positivity)
    hsize (fun _ => f.contractOn_singleton_cap U D Q (by positivity) hDcap)
    hmean hsizeBudget hvalueBudget (by nlinarith) hbudget
  have hSU (j) : S j ⊆ U := by
    intro e he
    by_contra heU
    exact hzero j e (hsupport j e heU) he
  have hS0 : S 0 = A := by
    ext e
    have heq : z 0 e = if e ∈ A then 1 else 0 := by
      change physicalProbability cores (BridgeGrid.point K 0) e = if e ∈ A then 1 else 0
      rw [BridgeGrid.initial, physicalProbability_vertex]
      rfl
    by_cases he : e ∈ A
    · exact iff_of_true (hone 0 e (by simpa [he] using heq)) he
    · exact iff_of_false (hzero 0 e (by simpa [he] using heq)) he
  have hS1 : S (Fin.last K) = B := by
    ext e
    have heq : z (Fin.last K) e = if e ∈ B then 1 else 0 := by
      change physicalProbability cores (BridgeGrid.point K (Fin.last K)) e = if e ∈ B then 1 else 0
      rw [BridgeGrid.terminal K hK, physicalProbability_vertex]
      rfl
    by_cases he : e ∈ B
    · exact iff_of_true (hone _ e (by simpa [he] using heq)) he
    · exact iff_of_false (hzero _ e (by simpa [he] using heq)) he
  let level := ((3 : ℝ) / 4 - 2 / N) * V
  let good := fun C : Finset (Fin n) => level ≤ f.value (Q ∪ C)
  have hlevel : level ≤ V := by
    dsimp [level]
    have hdiv : (0 : ℝ) ≤ 2 / N := by positivity
    nlinarith [mul_nonneg hdiv hV.le]
  have hmono : ∀ C C', C ⊆ C' → good C → good C' := by
    intro C C' hCC hgood
    exact hgood.trans (f.monotone _ _ (Finset.union_subset_union_right hCC))
  have hinter (j : Fin K) : good (D ∪ (S j.castSucc ∩ S j.succ)) := by
    have hi := physical_intersection_lower f cores Q V hV.le hcoreV
      (BridgeGrid.point K j.castSucc) (BridgeGrid.point K j.succ)
      (BridgeGrid.simplex K hK _) (BridgeGrid.simplex K hK _)
    have htype := BridgeGrid.type_value f A B Q V hV.le hA hB K hK j.castSucc
    have hstep := mul_le_mul_of_nonneg_left (BridgeGrid.step K hK j) hV.le
    have hfrac : (2 : ℝ) / K = 1 / (N : ℝ) := by dsimp [K]; push_cast; field_simp
    rw [hfrac] at hstep
    have hlower := f.contractOn_expectation_add_forced_lower U D Q
      (fun e => min (z j.castSucc e) (z j.succ e)) (hmincube j)
      (fun e he => by simp only [hsupport _ e he, min_self])
    have hval := hvalues j
    have hsint : (S j.castSucc ∩ S j.succ) ∩ U = S j.castSucc ∩ S j.succ :=
      Finset.inter_eq_left.mpr (Finset.inter_subset_left.trans (hSU _))
    change finiteExpectation (fun e => min (z j.castSucc e) (z j.succ e)) g.value - V / N ≤
      f.value ((D ∪ Q) ∪ ((S j.castSucc ∩ S j.succ) ∩ U)) - f.value (D ∪ Q) at hval
    rw [hsint] at hval
    have heq : Q ∪ (D ∪ (S j.castSucc ∩ S j.succ)) = (D ∪ Q) ∪ (S j.castSucc ∩ S j.succ) := by
      ext e; simp only [Finset.mem_union]; tauto
    change level ≤ f.value (Q ∪ (D ∪ (S j.castSucc ∩ S j.succ)))
    rw [heq]
    change _ ≤ finiteExpectation (fun e => min (z j.castSucc e) (z j.succ e)) _ at hi
    change finiteExpectation _ _ - f.value (D ∪ Q) ≤ finiteExpectation _ g.value at hlower
    change (3 : ℝ) / 4 * V ≤ finiteExpectation (BridgeGrid.point K j.castSucc)
      (f.onTypes cores Q).value at htype
    dsimp only [level]
    dsimp only [typeL1] at hstep
    simp only [div_eq_mul_inv] at hstep hval ⊢
    nlinarith only [htype, hi, hstep, hlower, hval]
  let C := ⌊(κ : ℝ) + (κ : ℝ) / N⌋₊
  have hSC (j) : (S j).card ≤ C := Nat.le_floor (hcards j)
  have hκC : κ ≤ C := Nat.le_floor (le_add_of_nonneg_right (by positivity))
  have hgood0 : good (D ∪ S 0) := by
    rw [hS0]
    exact hmono A _ Finset.subset_union_right (hlevel.trans hA)
  obtain ⟨P, hlen, hinit, hterm, hP⟩ := SetOperationPath.exists_chain_fin S C U
    (fun S => good (D ∪ S)) (fun C C' hCC hg => hmono _ _
      (Finset.union_subset_union_right hCC) hg) hgood0 (fun j => ⟨hSU j, hSC j⟩) hinter
  let R := P.withForced D
  have hR (j) : R.node j ⊆ U ∧ (R.node j).card ≤ C + H ∧ good (R.node j) := by
    exact ⟨Finset.union_subset hDU (hP j).1,
      (Finset.card_union_le _ _).trans (by have := (hP j).2.1; omega), (hP j).2.2⟩
  obtain ⟨L, hLlen, hLinit, hLterm, hL⟩ := R.prepend_forced A D U (C + H) good hmono
    (by change D ∪ P.node 0 = D ∪ A; rw [hinit, hS0]) (hlevel.trans hA)
    Finset.subset_union_left hDU (by omega) hR
  obtain ⟨T, hTlen, hTinit, hTterm, hT⟩ := L.append_unforced B D U (C + H) good hmono
    (by rw [hLterm]; change D ∪ P.node P.length = D ∪ B; rw [hterm, hS1])
    (hlevel.trans hB) Finset.subset_union_right hDU (by omega) hL
  refine ⟨T, hTinit.trans hLinit, hTterm, ?_, ?_⟩
  · have hplen : (P.length : ℝ) < 8 * κ := by
      rw [hlen, Nat.cast_sum]
      exact hcost
    have htlen : T.length = P.length + 2 * D.card := by
      rw [hTlen, hLlen]
      change D.card + P.length + D.card = P.length + 2 * D.card
      omega
    rw [htlen]
    have hplenn : P.length ≤ 8 * κ := by exact_mod_cast hplen.le
    omega
  · intro j
    refine ⟨(hT j).1, ?_, (hT j).2.2⟩
    have hh : ((T.node j).card : ℝ) ≤ (C + H : ℕ) := Nat.cast_le.mpr (hT j).2.1
    have hc : (C : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N := Nat.floor_le (by positivity)
    push_cast at hh
    dsimp [H] at hh
    linarith

end
