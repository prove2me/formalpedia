-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.capacity_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:18.288864+00:00
-- url     : https://prove2.me/submissions/a5732dfe-d614-4314-a7d8-8fccf82340a4

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

noncomputable def scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k) : Physical n k :=
  { g with u := fun e => S * g.u e }

@[simp] lemma scalePhysical_graph {n k : ℕ} (S : ℝ) (g : Physical n k) :
    (scalePhysical S g).graph = g.graph := rfl
@[simp] lemma scalePhysical_active {n k : ℕ} (S : ℝ) (g : Physical n k) :
    (scalePhysical S g).active = g.active := rfl
@[simp] lemma scalePhysical_gamma {n k : ℕ} (S : ℝ) (g : Physical n k) :
    (scalePhysical S g).gamma = g.gamma := rfl
@[simp] lemma scalePhysical_u {n k : ℕ} (S : ℝ) (g : Physical n k) (e : Fin k) :
    (scalePhysical S g).u e = S * g.u e := rfl

lemma physicalNorm_scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k) (x : Fin n → ℝ) :
    physicalNorm (scalePhysical S g) x = S * physicalNorm g x := by
  classical
  simp only [physicalNorm, scalePhysical_graph, scalePhysical_active, scalePhysical_u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

lemma cutCapacity_scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k)
    (C : Finset (Fin n)) :
    cutCapacity (scalePhysical S g) C = S * cutCapacity g C := by
  classical
  simp only [cutCapacity, scalePhysical_graph, scalePhysical_active, scalePhysical_u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hc : (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) <;> simp [hc]

@[simp] lemma cutDemand_scalePhysical {n k : ℕ} (S : ℝ) (g : Physical n k)
    (C : Finset (Fin n)) :
    cutDemand (scalePhysical S g) C = cutDemand g C := rfl

def NormalizedValid {n k : ℕ} (g : Physical n k) (m exponent : ℕ) : Prop :=
  n ≤ m ∧ k ≤ m ∧ 0 < n ∧
  (∀ e ∈ g.active, 1 ≤ g.u e ∧ g.u e ≤ (max 2 m : ℝ) ^ (2 * exponent)) ∧
  (∑ v, g.gamma v) = 0 ∧ (∀ v, |g.gamma v| ≤ (max 2 m : ℝ) ^ exponent) ∧
  (∀ x, physicalNorm g x = 0 → ∀ v w, x v = x w)

lemma normalizedValid_scalePhysical {n k : ℕ} (g : Physical n k) (m exponent : ℕ)
    (hg : g.Valid m exponent) :
    NormalizedValid (scalePhysical ((max 2 m : ℝ) ^ exponent) g) m exponent := by
  classical
  rcases hg with ⟨hn, hk, hn0, hu, hsum, hγ, hconn⟩
  let M : ℝ := max 2 m
  have hM : 1 ≤ M := by
    exact le_trans (by norm_num) (le_max_left (2 : ℝ) (m : ℝ))
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hS0 : 0 < M ^ exponent := pow_pos hM0 _
  refine ⟨hn, hk, hn0, ?_, hsum, ?_, ?_⟩
  · intro e he
    rcases hu e he with ⟨hlo, hhi⟩
    constructor
    · have hpow : (M ^ exponent) * M ^ (-(exponent : ℤ)) = 1 := by
        rw [← zpow_natCast M exponent, ← zpow_add₀ hM0.ne']
        simp
      calc
        1 = (M ^ exponent) * M ^ (-(exponent : ℤ)) := hpow.symm
        _ ≤ (M ^ exponent) * g.u e := mul_le_mul_of_nonneg_left hlo hS0.le
    · calc
        (M ^ exponent) * g.u e ≤ (M ^ exponent) * M ^ exponent :=
          mul_le_mul_of_nonneg_left hhi hS0.le
        _ = M ^ (2 * exponent) := by rw [two_mul, pow_add]
  · intro v
    exact hγ v
  · intro x hx v w
    apply hconn x
    rw [physicalNorm_scalePhysical] at hx
    exact (mul_eq_zero.mp hx).resolve_left hS0.ne'

end DecrAlmostLinearSSSP.Decremental.NonemptyCut

open DecrAlmostLinearSSSP.Decremental DecrAlmostLinearSSSP.Decremental.NonemptyCut

theorem solution {n k : ℕ}
    (g : Physical n k) (m exponent : ℕ)
    (capacityBound : ℝ) (hg : g.Valid m exponent)
    (hB0 : 0 < capacityBound) (hB : capacityBound ≤ (max 2 m : ℝ) ^ exponent)
    (huB : ∀ e ∈ g.active, g.u e ≤ capacityBound) :
    let S : ℝ := (max 2 m : ℝ) ^ exponent
    let ĝ : Physical n k := { g with u := fun e => S * g.u e }
    (n ≤ m ∧ k ≤ m ∧ 0 < n ∧
      (∀ e ∈ ĝ.active, 1 ≤ ĝ.u e ∧ ĝ.u e ≤ (max 2 m : ℝ) ^ (2 * exponent)) ∧
      (∑ v, ĝ.gamma v) = 0 ∧ (∀ v, |ĝ.gamma v| ≤ (max 2 m : ℝ) ^ exponent) ∧
      (∀ x, physicalNorm ĝ x = 0 → ∀ v w, x v = x w)) ∧
    0 < S * capacityBound ∧ S * capacityBound ≤ (max 2 m : ℝ) ^ (2 * exponent) ∧
    ∀ e ∈ ĝ.active, ĝ.u e ≤ S * capacityBound := by
  dsimp only
  let S : ℝ := (max 2 m : ℝ) ^ exponent
  change NormalizedValid (scalePhysical S g) m exponent ∧
    0 < S * capacityBound ∧ S * capacityBound ≤ (max 2 m : ℝ) ^ (2 * exponent) ∧
    ∀ e ∈ (scalePhysical S g).active, (scalePhysical S g).u e ≤ S * capacityBound
  have hM : (1 : ℝ) ≤ max (2 : ℝ) (m : ℝ) :=
    le_trans (show (1 : ℝ) ≤ 2 by norm_num) (le_max_left (2 : ℝ) (m : ℝ))
  have hS : 0 < S := pow_pos (lt_of_lt_of_le zero_lt_one hM) _
  refine ⟨normalizedValid_scalePhysical g m exponent hg, mul_pos hS hB0, ?_, ?_⟩
  · calc
      S * capacityBound ≤ S * S := mul_le_mul_of_nonneg_left hB hS.le
      _ = (max 2 m : ℝ) ^ (2 * exponent) := by dsimp [S]; rw [two_mul, pow_add]
  · intro e he
    exact mul_le_mul_of_nonneg_left (huB e he) hS.le
