-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.weighted_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:59.935047+00:00
-- url     : https://prove2.me/submissions/c06f65c9-a069-461c-800d-47169aba8c10

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardInstance
import Theorems.Thm_ConsistentSubmodular_HardInstance_realization_bounds

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- A fibre containing the blocks `b < m` of group `g` has at least `m` cells. -/
theorem le_card_fiber {k m : ℕ} (hm : m ≤ k) (C : Finset (Fin 3 × Fin k)) (g : Fin 3)
    (hC : ∀ b : Fin k, b.val < m → (g, b) ∈ C) : m ≤ (fiber C g).card := by
  calc m = ((univ : Finset (Fin k)).filter fun b => b.val < m).card := by
        rw [Fin.card_filter_val_lt, min_eq_right hm]
    _ ≤ (fiber C g).card := by
        refine card_le_card_of_injOn (fun b => (g, b)) ?_ ?_
        · intro b hb
          have hb' := (mem_filter.mp (mem_coe.mp hb)).2
          exact mem_coe.mpr (mem_filter.mpr ⟨hC b hb', rfl⟩)
        · intro b _ b' _ h
          exact (Prod.ext_iff.mp h).2

theorem mem_elementCells_tinyAt {k : ℕ} (c : Fin 3 × Fin k) : c ∈ elementCells k (tinyAt c) := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; exact c.2.elim0
  have hb := c.2.isLt
  have hg := c.1.isLt
  have h3 : c.1.val * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
  have hdiv : (c.2.val + c.1.val * k) / k = c.1.val := by
    rw [Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hb, zero_add]
  have hmod : (c.2.val + c.1.val * k) % k = c.2.val := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  simp only [elementCells, show (tinyAt c).val = c.1.val * k + c.2.val from rfl, mem_filter,
    mem_univ, true_and]
  rw [if_pos (by omega), Nat.add_comm (c.1.val * k), hdiv, hmod]
  exact ⟨rfl, rfl⟩

theorem mem_elementCells_bigZero {k : ℕ} (b : Fin k) : ((0 : Fin 3), b) ∈ elementCells k (bigZero k) := by
  simp only [elementCells, bigZero, mem_filter, mem_univ, true_and]
  rw [if_neg (by omega)]
  simp

theorem mem_elementCells_bigOne {k : ℕ} (b : Fin k) : ((1 : Fin 3), b) ∈ elementCells k (bigOne k) := by
  simp only [elementCells, show (bigOne k).val = 3 * k + 1 from rfl, mem_filter, mem_univ,
    true_and]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

section Bounds

variable {k : ℕ} {u : Fin 3 → ℝ}

/-- A family covering at least `n_g` cells of every group `g` has weighted
coverage at least `Σ_g u_g n_g`. -/
theorem le_weightedValue (hu : ∀ g, 0 ≤ u g) (T : Finset (Fin (3 * k + 2))) {n₀ n₁ n₂ : ℝ}
    (h₀ : n₀ ≤ (fiber (T.biUnion (elementCells k)) 0).card)
    (h₁ : n₁ ≤ (fiber (T.biUnion (elementCells k)) 1).card)
    (h₂ : n₂ ≤ (fiber (T.biUnion (elementCells k)) 2).card) :
    u 0 * n₀ + u 1 * n₁ + u 2 * n₂ ≤ weightedValue k u T := by
  rw [weightedValue, Fin.sum_univ_three]
  have := mul_le_mul_of_nonneg_left h₀ (hu 0)
  have := mul_le_mul_of_nonneg_left h₁ (hu 1)
  have := mul_le_mul_of_nonneg_left h₂ (hu 2)
  linarith

end Bounds

theorem card_positions_le (k a m : ℕ) : (positions k a m).card ≤ m := by
  calc (positions k a m).card ≤ (range m).card := by
        refine card_le_card_of_injOn (fun e => e.val - a) ?_ ?_
        · intro e he
          have := (mem_filter.mp (mem_coe.mp he)).2
          exact mem_coe.mpr (mem_range.mpr (show e.val - a < m by omega))
        · intro e he e' he' h
          have h1 := (mem_filter.mp (mem_coe.mp he)).2
          have h2 := (mem_filter.mp (mem_coe.mp he')).2
          have h' : e.val - a = e'.val - a := h
          exact Fin.ext (by omega)
    _ = m := card_range m

section Competitors

variable {k : ℕ}

theorem tinyAt_mem_positions {a m : ℕ} (c : Fin 3 × Fin k) (h1 : a ≤ c.1.val * k + c.2.val)
    (h2 : c.1.val * k + c.2.val < a + m) : tinyAt c ∈ positions k a m :=
  mem_filter.mpr ⟨mem_univ _, h1, h2⟩

/-- The competitor before `U₀` arrives covers all cells of group `0`. -/
theorem firstCompetitor_fibers :
    k ≤ (fiber ((firstCompetitor k).biUnion (elementCells k)) 0).card :=
  le_card_fiber le_rfl _ 0 fun b _ => mem_biUnion.mpr ⟨tinyAt (0, b),
    tinyAt_mem_positions (0, b) (Nat.zero_le _) (by simp [b.isLt]), mem_elementCells_tinyAt _⟩

/-- The competitor after `U₀` arrives covers group `0` and `k - 1` cells of
group `1`. -/
theorem secondCompetitor_fibers :
    k ≤ (fiber ((secondCompetitor k).biUnion (elementCells k)) 0).card ∧
      k - 1 ≤ (fiber ((secondCompetitor k).biUnion (elementCells k)) 1).card := by
  refine ⟨le_card_fiber le_rfl _ 0 fun b _ =>
      mem_biUnion.mpr ⟨bigZero k, mem_insert_self _ _, mem_elementCells_bigZero b⟩, ?_⟩
  refine le_card_fiber (Nat.sub_le k 1) _ 1 fun b hb => mem_biUnion.mpr
    ⟨tinyAt (1, b), mem_insert_of_mem ?_, mem_elementCells_tinyAt _⟩
  exact tinyAt_mem_positions (1, b) (show k ≤ 1 * k + b.val by omega)
    (show 1 * k + b.val < k + (k - 1) by omega)

/-- The competitor at the end covers groups `0` and `1` and `k - 2` cells of
group `2`. -/
theorem thirdCompetitor_fibers :
    k ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 0).card ∧
      k ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 1).card ∧
      k - 2 ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 2).card := by
  refine ⟨le_card_fiber le_rfl _ 0 fun b _ =>
      mem_biUnion.mpr ⟨bigZero k, mem_insert_self _ _, mem_elementCells_bigZero b⟩,
    le_card_fiber le_rfl _ 1 fun b _ =>
      mem_biUnion.mpr ⟨bigOne k, mem_insert_of_mem (mem_insert_self _ _),
        mem_elementCells_bigOne b⟩, ?_⟩
  refine le_card_fiber (Nat.sub_le k 2) _ 2 fun b hb => mem_biUnion.mpr
    ⟨tinyAt (2, b), mem_insert_of_mem (mem_insert_of_mem ?_), mem_elementCells_tinyAt _⟩
  exact tinyAt_mem_positions (2, b) (show 2 * k ≤ 2 * k + b.val by omega)
    (show 2 * k + b.val < 2 * k + (k - 2) by omega)

variable {u : Fin 3 → ℝ}

/-- The optimum `o₀ = k u₀` before `U₀` arrives, as a lower bound. -/
theorem value_firstCompetitor (hu : ∀ g, 0 ≤ u g) :
    u 0 * k ≤ weightedValue k u (firstCompetitor k) := by
  have h := le_weightedValue hu (firstCompetitor k) (n₀ := k) (n₁ := 0) (n₂ := 0)
    (by exact_mod_cast firstCompetitor_fibers) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- The optimum `o₁ = k u₀ + (k - 1) u₁` after `U₀` arrives, as a lower bound. -/
theorem value_secondCompetitor (hu : ∀ g, 0 ≤ u g) (hk : 1 ≤ k) :
    u 0 * k + u 1 * ((k : ℝ) - 1) ≤ weightedValue k u (secondCompetitor k) := by
  obtain ⟨h0, h1⟩ := secondCompetitor_fibers (k := k)
  have h1' : (k : ℝ) - 1 ≤ (fiber ((secondCompetitor k).biUnion (elementCells k)) 1).card := by
    have := (Nat.cast_le (α := ℝ)).mpr h1
    rwa [Nat.cast_sub hk, Nat.cast_one] at this
  have h := le_weightedValue hu (secondCompetitor k) (n₀ := k) (n₂ := 0) (by exact_mod_cast h0) h1'
    (Nat.cast_nonneg _)
  linarith

/-- The optimum `o₂ = k u₀ + k u₁ + (k - 2) u₂` at the end, as a lower bound. -/
theorem value_thirdCompetitor (hu : ∀ g, 0 ≤ u g) (hk : 2 ≤ k) :
    u 0 * k + u 1 * k + u 2 * ((k : ℝ) - 2) ≤ weightedValue k u (thirdCompetitor k) := by
  obtain ⟨h0, h1, h2⟩ := thirdCompetitor_fibers (k := k)
  have h2' : (k : ℝ) - 2 ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 2).card := by
    have := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_sub hk, Nat.cast_ofNat] at this
  exact le_weightedValue hu (thirdCompetitor k) (n₀ := k) (n₁ := k) (by exact_mod_cast h0)
    (by exact_mod_cast h1) h2'

theorem card_firstCompetitor_le : (firstCompetitor k).card ≤ k := card_positions_le k 0 k

theorem card_secondCompetitor_le (hk : 1 ≤ k) : (secondCompetitor k).card ≤ k := by
  have := card_insert_le (bigZero k) (positions k k (k - 1))
  have := card_positions_le k k (k - 1)
  unfold secondCompetitor
  omega

theorem card_thirdCompetitor_le (hk : 2 ≤ k) : (thirdCompetitor k).card ≤ k := by
  have := card_insert_le (bigZero k) (insert (bigOne k) (positions k (2 * k) (k - 2)))
  have := card_insert_le (bigOne k) (positions k (2 * k) (k - 2))
  have := card_positions_le k (2 * k) (k - 2)
  unfold thirdCompetitor
  omega

theorem firstCompetitor_arrived : firstCompetitor k ⊆ arrivedPrefix (3 * k + 2) (3 * k) := by
  intro e he
  have := (mem_filter.mp he).2
  exact mem_filter.mpr ⟨mem_univ _, by omega⟩

theorem secondCompetitor_arrived : secondCompetitor k ⊆ arrivedPrefix (3 * k + 2) (3 * k + 1) := by
  intro e he
  rcases mem_insert.mp he with rfl | he
  · exact mem_filter.mpr ⟨mem_univ _, show 3 * k < 3 * k + 1 by omega⟩
  · have := (mem_filter.mp he).2
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩

theorem thirdCompetitor_arrived : thirdCompetitor k ⊆ arrivedPrefix (3 * k + 2) (3 * k + 2) :=
  fun e _ => mem_filter.mpr ⟨mem_univ _, e.isLt⟩

end Competitors

end ConsistentSubmodular.HardInstance

end

end

section

noncomputable section

namespace ConsistentSubmodular.HardInstance

/-- The convex combination of the three benchmarks. -/
theorem lpDenominator_eq (x : ℝ) :
    lpDenominator x = lpThird x + lpMuOne x * (1 + x) + lpMuTwo x * (1 + x + lpThird x) := by
  unfold lpDenominator lpThird lpMuOne lpMuTwo
  ring

end ConsistentSubmodular.HardInstance

end

end

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- Expectation is monotone on the realizations of positive probability. -/
theorem expectation_le_of {n : ℕ} (μ : RandomTrajectory n)
    {G H : (Fin (n + 1) → Finset (Fin n)) → ℝ} (h : ∀ S, μ.prob S ≠ 0 → G S ≤ H S) :
    ∑ S, μ.prob S * G S ≤ ∑ S, μ.prob S * H S := by
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases hS : μ.prob S = 0
  · simp [hS]
  · exact mul_le_mul_of_nonneg_left (h S hS) (μ.prob_nonneg S)

/-- The expectation of an affine function of three counts. -/
theorem expectation_affine {n : ℕ} (μ : RandomTrajectory n) (a b₀ b₁ b₂ : ℝ)
    (c₀ c₁ c₂ : (Fin (n + 1) → Finset (Fin n)) → ℝ) :
    ∑ S, μ.prob S * (a + b₀ * c₀ S + b₁ * c₁ S + b₂ * c₂ S) =
      a + b₀ * ∑ S, μ.prob S * c₀ S + b₁ * ∑ S, μ.prob S * c₁ S +
        b₂ * ∑ S, μ.prob S * c₂ S := by
  have h : ∀ S, μ.prob S * (a + b₀ * c₀ S + b₁ * c₁ S + b₂ * c₂ S) =
      a * μ.prob S + b₀ * (μ.prob S * c₀ S) + b₁ * (μ.prob S * c₁ S) +
        b₂ * (μ.prob S * c₂ S) := fun S => by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, μ.prob_sum, mul_one]

theorem lpWeights_nonneg {x : ℝ} (hx : 0 ≤ x) (g : Fin 3) : 0 ≤ lpWeights x g := by
  fin_cases g
  · exact zero_le_one
  · exact hx
  · change 0 ≤ lpThird x
    unfold lpThird
    positivity

end ConsistentSubmodular.HardInstance

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem solution {k C : ℕ} {x ρ : ℝ} (hk : 2 ≤ k) (hx0 : 0 < x) (hx1 : x * (1 + x) ≤ 1)
    (hρ0 : 0 ≤ ρ)
    (hρ : (k : ℝ) * lpNumerator x + lpError x * C ≤ ρ * (k * lpDenominator x - lpError x))
    (μ : RandomTrajectory (3 * k + 2)) (hμ : μ.Feasible k C) :
    ∃ (t : Fin (3 * k + 2 + 1)) (A : Finset (Fin (3 * k + 2))),
      A ⊆ arrivedPrefix (3 * k + 2) t.val ∧ A.card ≤ k ∧
      (k : ℝ) ≤ (fiber (A.biUnion (elementCells k)) 0).card ∧
      μ.expectation (weightedValue k (lpWeights x)) t ≤ ρ * weightedValue k (lpWeights x) A := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hy0 : 0 ≤ lpThird x := by unfold lpThird; positivity
  have hy : 0 < lpThird x := by unfold lpThird; positivity
  have hyx : lpThird x ≤ x := by unfold lpThird; nlinarith
  have hu := lpWeights_nonneg hx0.le
  have hu21 : lpWeights x 2 ≤ lpWeights x 1 := by simpa using hyx
  have hμ₁ : 0 ≤ lpMuOne x := by
    unfold lpMuOne
    have : 0 ≤ 1 - x := by nlinarith
    positivity
  have hμ₂ : 0 ≤ lpMuTwo x := by unfold lpMuTwo; linarith
  -- The competitors of the three times and the optima `o₀, o₁, o₂`.
  have hopt₀ := value_firstCompetitor (k := k) hu
  have hopt₁ := value_secondCompetitor hu hk1
  have hopt₂ := value_thirdCompetitor hu hk
  simp only [lpWeights_zero, lpWeights_one, lpWeights_two, one_mul] at hopt₀ hopt₁ hopt₂
  have hA₀ := hcon (timeBefore k) (firstCompetitor k) firstCompetitor_arrived
    card_firstCompetitor_le (by exact_mod_cast firstCompetitor_fibers)
  have hA₁ := hcon (timeMiddle k) (secondCompetitor k) secondCompetitor_arrived
    (card_secondCompetitor_le hk1) (by exact_mod_cast (secondCompetitor_fibers (k := k)).1)
  have hA₂ := hcon (timeAfter k) (thirdCompetitor k) thirdCompetitor_arrived
    (card_thirdCompetitor_le hk) (by exact_mod_cast (thirdCompetitor_fibers (k := k)).1)
  -- The expected counts `k₀, k₁, k₂` and the bounds on `ALG₀, ALG₁, ALG₂`.
  set f := weightedValue k (lpWeights x) with hf
  set c : Fin 3 → (Fin (3 * k + 2 + 1) → Finset (Fin (3 * k + 2))) → ℝ :=
    fun g S => (tinyCount k g (S (timeBefore k)) : ℝ) with hc
  have hE₀ : μ.expectation f (timeBefore k) ≤
      0 + 1 * ∑ S, μ.prob S * c 0 S + x * ∑ S, μ.prob S * c 1 S +
        lpThird x * ∑ S, μ.prob S * c 2 S := by
    rw [← expectation_affine]
    refine expectation_le_of μ fun S hS => ?_
    have := (realization_bounds hu hu21 (hμ S hS)).1
    simp only [lpWeights_zero, lpWeights_one, lpWeights_two] at this
    simp only [hc]
    linarith
  have hE₁ : μ.expectation f (timeMiddle k) ≤
      ((k : ℝ) + x * C) + 0 * ∑ S, μ.prob S * c 0 S + x * ∑ S, μ.prob S * c 1 S +
        lpThird x * ∑ S, μ.prob S * c 2 S := by
    rw [← expectation_affine]
    refine expectation_le_of μ fun S hS => ?_
    have := (realization_bounds hu hu21 (hμ S hS)).2.1
    simp only [lpWeights_zero, lpWeights_one, lpWeights_two] at this
    simp only [hc]
    linarith
  have hE₂ : μ.expectation f (timeAfter k) ≤
      ((k : ℝ) + x * k + 2 * lpThird x * C) + 0 * ∑ S, μ.prob S * c 0 S +
        0 * ∑ S, μ.prob S * c 1 S + lpThird x * ∑ S, μ.prob S * c 2 S := by
    rw [← expectation_affine]
    refine expectation_le_of μ fun S hS => ?_
    have := (realization_bounds hu hu21 (hμ S hS)).2.2.1
    simp only [lpWeights_zero, lpWeights_one, lpWeights_two] at this
    simp only [hc]
    linarith
  have hcount : ∑ S, μ.prob S * c 0 S + ∑ S, μ.prob S * c 1 S + ∑ S, μ.prob S * c 2 S ≤ k := by
    have h := expectation_affine μ 0 1 1 1 (c 0) (c 1) (c 2)
    have hle : ∑ S, μ.prob S * (0 + 1 * c 0 S + 1 * c 1 S + 1 * c 2 S) ≤
        ∑ S, μ.prob S * ((k : ℝ) + 0 * c 0 S + 0 * c 1 S + 0 * c 2 S) :=
      expectation_le_of μ fun S hS => by
        have := (realization_bounds hu hu21 (hμ S hS)).2.2.2
        simp only [hc]
        linarith
    rw [h, expectation_affine] at hle
    linarith
  set k₀ := ∑ S, μ.prob S * c 0 S
  set k₁ := ∑ S, μ.prob S * c 1 S
  set k₂ := ∑ S, μ.prob S * c 2 S
  set E₀ := μ.expectation f (timeBefore k)
  set E₁ := μ.expectation f (timeMiddle k)
  set E₂ := μ.expectation f (timeAfter k)
  -- The convex combination with `μ₀ = u₂`, `μ₁ = u₂/u₁ - u₂`, `μ₂ = 1 - u₂/u₁`.
  have hupper : lpThird x * E₀ + lpMuOne x * E₁ + lpMuTwo x * E₂ ≤
      k * lpNumerator x + lpError x * C := by
    have h₀ := mul_le_mul_of_nonneg_left hE₀ hy0
    have h₁ := mul_le_mul_of_nonneg_left hE₁ hμ₁
    have h₂ := mul_le_mul_of_nonneg_left hE₂ hμ₂
    have hc' := mul_le_mul_of_nonneg_left hcount hy0
    have hid : lpThird x * (0 + 1 * k₀ + x * k₁ + lpThird x * k₂) +
        lpMuOne x * (((k : ℝ) + x * C) + 0 * k₀ + x * k₁ + lpThird x * k₂) +
        lpMuTwo x * (((k : ℝ) + x * k + 2 * lpThird x * C) + 0 * k₀ + 0 * k₁ +
          lpThird x * k₂) =
        lpThird x * (k₀ + k₁ + k₂) + (k * (lpNumerator x - lpThird x) + lpError x * C) := by
      simp only [lpError, lpNumerator, lpMuOne, lpMuTwo, lpThird]
      ring
    have hid' : lpThird x * k + (k * (lpNumerator x - lpThird x) + lpError x * C) =
        k * lpNumerator x + lpError x * C := by ring
    linarith
  have hlower : ρ * (k * lpDenominator x - lpError x) <
      lpThird x * E₀ + lpMuOne x * E₁ + lpMuTwo x * E₂ := by
    have h₀ : ρ * k < E₀ := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hopt₀ hρ0) hA₀
    have h₁ : ρ * (k + x * (k - 1)) < E₁ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hopt₁ hρ0) hA₁
    have h₂ : ρ * (k + x * k + lpThird x * (k - 2)) < E₂ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hopt₂ hρ0) hA₂
    have g₀ := mul_lt_mul_of_pos_left h₀ hy
    have g₁ := mul_le_mul_of_nonneg_left h₁.le hμ₁
    have g₂ := mul_le_mul_of_nonneg_left h₂.le hμ₂
    have hid : lpThird x * (ρ * k) + lpMuOne x * (ρ * (k + x * (k - 1))) +
        lpMuTwo x * (ρ * (k + x * k + lpThird x * (k - 2))) =
        ρ * (k * lpDenominator x - lpError x) := by
      rw [lpDenominator_eq]
      unfold lpError
      ring
    linarith
  linarith

end
