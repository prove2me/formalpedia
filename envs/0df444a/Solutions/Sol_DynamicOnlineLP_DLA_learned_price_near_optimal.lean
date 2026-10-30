-- Prove2me | solution 1 for DynamicOnlineLP.DLA.learned_price_near_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T07:23:56.190492+00:00
-- url     : https://prove2.me/submissions/c5fcdceb-0486-4f15-a6ab-3aa38e0629d5

import Definitions.Def_DynamicOnlineLP_DLA_Algorithm
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Theorems.Thm_DynamicOnlineLP_DLA_bernstein_without_replacement
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_NatureSLT_GrowthFunction_growth_bound_of_vcDim
import Theorems.Thm_NatureSLT_GrowthFunction_vcDim_linear_indicators

/-!
Finite families of strict threshold patterns. The two NatureSLT references are
platform-proved inputs in the identical pinned environment. Their lightweight
local reference copies contain the platform API's `sorry` bodies; consequently
local transitive axiom reports include `sorryAx` for these external inputs.
This module introduces no placeholders or additional proof obligations.
-/

open scoped BigOperators
open NatureSLT.GrowthFunction

private theorem separations_le_two_pow {Z Λ : Type*} (Q : Λ → Z → Bool)
    {n : ℕ} (z : Fin n → Z) : numSeparations Q z ≤ 2 ^ n := by
  unfold numSeparations
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using
    (Set.ncard_le_card (Set.range fun α : Λ => fun i : Fin n => Q α (z i)))

private theorem separations_le_max {Z Λ : Type*} (Q : Λ → Z → Bool)
    {n : ℕ} (z : Fin n → Z) : numSeparations Q z ≤ maxSeparations Q n := by
  apply le_ciSup
  refine ⟨2 ^ n, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact separations_le_two_pow Q w

namespace DynamicOnlineLP.DLA

/-- All strict price-threshold patterns lie in a single nonempty finite family
whose logarithmic size is bounded independently of the coefficients and prices.
Equality is rejected by the strict threshold, as required by the DLA rule. -/
theorem finite_threshold_patterns (m n : ℕ) (hn : 0 < n)
    (a : Fin n → Fin m → ℝ) (π : Fin n → ℝ) :
    ∃ F : Finset (Fin n → Bool), F.Nonempty ∧
      (∀ p : Fin m → ℝ,
        (fun j => decide ((∑ i : Fin m, p i * a j i) < π j)) ∈ F) ∧
      Real.log (F.card : ℝ) ≤ ((m : ℝ) + 2) * (Real.log (n : ℝ) + 1) := by
  classical
  let Q := fun (α : (Fin (m + 1) → ℝ) × ℝ)
      (z : EuclideanSpace ℝ (Fin (m + 1))) =>
    stepFunction (∑ k : Fin (m + 1), α.1 k * z k + α.2)
  let z : Fin n → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun j => WithLp.toLp 2 (Fin.snoc (a j) (π j))
  let S : Set (Fin n → Bool) := Set.range fun α => fun j => Q α (z j)
  let F : Finset (Fin n → Bool) := S.toFinset.image (fun v j => !(v j))
  have hFnonempty : F.Nonempty := by
    apply Finset.image_nonempty.mpr
    apply Set.toFinset_nonempty.mpr
    exact ⟨_, ⟨(0, 0), rfl⟩⟩
  refine ⟨F, hFnonempty, ?_, ?_⟩
  · intro p
    apply Finset.mem_image.mpr
    refine ⟨fun j => Q (Fin.snoc p (-1), 0) (z j), ?_, ?_⟩
    · exact Set.mem_toFinset.mpr ⟨(Fin.snoc p (-1), 0), rfl⟩
    · funext j
      simp [Q, z, stepFunction, Fin.sum_univ_castSucc, ← decide_not]
  · have hcard : F.card ≤ numSeparations Q z := by
      calc
        F.card ≤ S.toFinset.card := Finset.card_image_le
        _ = numSeparations Q z := (Set.ncard_eq_toFinset_card' S).symm
    have hcardpos : 0 < (F.card : ℝ) := by
      exact_mod_cast hFnonempty.card_pos
    by_cases hlarge : m + 2 < n
    · have hlog : Real.log (F.card : ℝ) ≤ growthFunction Q n := by
        apply Real.log_le_log hcardpos
        exact_mod_cast hcard.trans (separations_le_max Q z)
      have hvc : vcDim Q = ((m + 2 : ℕ) : ℕ∞) := by
        exact vcDim_linear_indicators (m + 1)
      have hgrowth := growth_bound_of_vcDim Q (m + 2) hvc n hlarge
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hmreal : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
      have hmone : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
        push_cast
        linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
      have hdiv : (n : ℝ) / ((m + 2 : ℕ) : ℝ) ≤ n :=
        div_le_self hnreal.le hmone
      have hlogdiv := Real.log_le_log (div_pos hnreal hmreal) hdiv
      calc
        Real.log (F.card : ℝ) ≤ growthFunction Q n := hlog
        _ ≤ ((m + 2 : ℕ) : ℝ) *
            (Real.log ((n : ℝ) / ((m + 2 : ℕ) : ℝ)) + 1) := hgrowth
        _ ≤ ((m + 2 : ℕ) : ℝ) * (Real.log (n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add hlogdiv le_rfl) hmreal.le
        _ = ((m : ℝ) + 2) * (Real.log (n : ℝ) + 1) := by norm_num
    · have hsmall : n ≤ m + 2 := Nat.le_of_not_gt hlarge
      have hpow : F.card ≤ 2 ^ n := hcard.trans (separations_le_two_pow Q z)
      have hlogpow : Real.log (F.card : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := by
        apply Real.log_le_log hcardpos
        exact_mod_cast hpow
      have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
      have hmreal : 0 ≤ (m : ℝ) + 2 := by positivity
      calc
        Real.log (F.card : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := hlogpow
        _ = (n : ℝ) * Real.log 2 := Real.log_pow 2 n
        _ ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg n)
        _ ≤ (m : ℝ) + 2 := by
          simpa only [mul_one, Nat.cast_add, Nat.cast_ofNat] using
            (show (n : ℝ) ≤ ((m + 2 : ℕ) : ℝ) from by exact_mod_cast hsmall)
        _ ≤ ((m : ℝ) + 2) * (Real.log (n : ℝ) + 1) := by
          apply le_mul_of_one_le_right hmreal
          linarith only [hlogn]

end DynamicOnlineLP.DLA

/-!
Finite population moments used by the exact without-replacement Bernstein bound.
All quantities use the population mean and variance with denominator the population size.
-/

open Finset

namespace TCSShortlistPriceNearOptimal.Bernstein

theorem mean_mem_extrema {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → ℝ) :
    (⨅ i, c i) ≤ (∑ i, c i) / (Fintype.card ι : ℝ) ∧
      (∑ i, c i) / (Fintype.card ι : ℝ) ≤ ⨆ i, c i := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · apply (le_div_iff₀ hn).mpr
    calc
      (⨅ i, c i) * (Fintype.card ι : ℝ) = ∑ _i : ι, ⨅ i, c i := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i, c i := sum_le_sum fun i _ ↦ ciInf_le (Set.finite_range c).bddBelow i
  · apply (div_le_iff₀ hn).mpr
    calc
      (∑ i, c i) ≤ ∑ _i : ι, ⨆ i, c i :=
        sum_le_sum fun i _ ↦ le_ciSup (Set.finite_range c).bddAbove i
      _ = (⨆ i, c i) * (Fintype.card ι : ℝ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_comm]

theorem population_range_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) : 0 ≤ (⨆ i, c i) - (⨅ i, c i) := by
  exact sub_nonneg.mpr (ciInf_le_ciSup (Set.finite_range c).bddBelow
    (Set.finite_range c).bddAbove)

theorem abs_sub_mean_le_range {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (j : ι) :
    |c j - (∑ i, c i) / (Fintype.card ι : ℝ)| ≤ (⨆ i, c i) - (⨅ i, c i) := by
  obtain ⟨hlo, hhi⟩ := mean_mem_extrema c
  have hjlo := ciInf_le (Set.finite_range c).bddBelow j
  have hjhi := le_ciSup (Set.finite_range c).bddAbove j
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem population_variance_nonneg {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    0 ≤ (∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
      (Fintype.card ι : ℝ) := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

theorem population_variance_eq_zero_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) :
    (∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
        (Fintype.card ι : ℝ) = 0 ↔
      ∀ i, c i = (∑ j, c j) / (Fintype.card ι : ℝ) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro h i
    have hs := (div_eq_zero_iff.mp h).resolve_right hn
    have hi := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
      (c j - (∑ k, c k) / (Fintype.card ι : ℝ)))).mp hs i (mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    apply div_eq_zero_iff.mpr
    left
    apply sum_eq_zero
    intro i _
    rw [show c i - (∑ j, c j) / (Fintype.card ι : ℝ) = 0 from sub_eq_zero.mpr (h i)]
    norm_num

theorem population_range_eq_zero_of_variance_eq_zero {ι : Type*}
    [Fintype ι] [Nonempty ι] (c : ι → ℝ)
    (h : (∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
      (Fintype.card ι : ℝ) = 0) : (⨆ i, c i) - (⨅ i, c i) = 0 := by
  have hc := (population_variance_eq_zero_iff c).mp h
  have hsup : (⨆ i, c i) = (∑ j, c j) / (Fintype.card ι : ℝ) := by
    simpa only [ciSup_const] using
      congrArg (fun f : ι → ℝ ↦ ⨆ i, f i) (funext hc)
  have hinf : (⨅ i, c i) = (∑ j, c j) / (Fintype.card ι : ℝ) := by
    simpa only [ciInf_const] using
      congrArg (fun f : ι → ℝ ↦ ⨅ i, f i) (funext hc)
  rw [hsup, hinf, sub_self]

theorem firstTimes_card_eq {R r : ℕ} (hr : r ≤ R) :
    (DynamicOnlineLP.DLA.firstTimes R r).card = r := by
  classical
  let e : ↥(DynamicOnlineLP.DLA.firstTimes R r) ≃ Fin r := {
    toFun := fun t ↦ ⟨t.val.val, by
      simpa [DynamicOnlineLP.DLA.firstTimes] using t.property⟩
    invFun := fun t ↦ ⟨⟨t.val, lt_of_lt_of_le t.isLt hr⟩,
      by simp [DynamicOnlineLP.DLA.firstTimes, t.isLt]⟩
    left_inv := by intro t; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro t; apply Fin.ext; rfl }
  simpa using Fintype.card_congr e

theorem sum_firstTimes_centered {R r : ℕ} (hr : r ≤ R) (c : Fin R → ℝ)
    (σ : Equiv.Perm (Fin R)) :
    (∑ k ∈ DynamicOnlineLP.DLA.firstTimes R r,
        (c (σ k) - (∑ j, c j) / (R : ℝ))) =
      (∑ k ∈ DynamicOnlineLP.DLA.firstTimes R r, c (σ k)) -
        (r : ℝ) * ((∑ j, c j) / (R : ℝ)) := by
  rw [sum_sub_distrib]
  simp only [sum_const, firstTimes_card_eq hr, nsmul_eq_mul]

theorem probPerm_le_one {R : ℕ} (P : Equiv.Perm (Fin R) → Prop) :
    DynamicOnlineLP.DLA.probPerm P ≤ 1 := by
  classical
  have hn : 0 < (Fintype.card (Equiv.Perm (Fin R)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold DynamicOnlineLP.DLA.probPerm
  apply (div_le_one hn).mpr
  exact_mod_cast (card_filter_le (univ : Finset (Equiv.Perm (Fin R))) P)

end TCSShortlistPriceNearOptimal.Bernstein

/-!
Bounded-population tails for fixed time sets, and the two fixed-pattern block events used
in the canonical learned-price argument. No price or population is selected from the arrival
permutation in these statements.
-/

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistPriceNearOptimal.Bernstein

theorem probPerm_mono {n : ℕ} {P Q : Equiv.Perm (Fin n) → Prop}
    (h : ∀ σ, P σ → Q σ) : probPerm P ≤ probPerm Q := by
  classical
  unfold probPerm
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (monotone_filter_right univ fun σ _ ↦ h σ)

theorem probPerm_comp_mulRight {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    (τ : Equiv.Perm (Fin n)) : probPerm (fun σ ↦ P (σ * τ)) = probPerm P := by
  classical
  unfold probPerm
  congr 2
  exact card_bijective (Equiv.mulRight τ) (Equiv.mulRight τ).bijective
    (fun σ ↦ by simp)

theorem bounded_population_mean_nonneg {n : ℕ} (c : Fin n → ℝ)
    (hc : ∀ j, 0 ≤ c j) : 0 ≤ (∑ j, c j) / (n : ℝ) :=
  div_nonneg (sum_nonneg fun j _ ↦ hc j) (Nat.cast_nonneg _)

theorem bounded_population_variance_le_mean {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) :
    (∑ j, (c j - (∑ k, c k) / (n : ℝ)) ^ 2) / (n : ℝ) ≤
      (∑ j, c j) / (n : ℝ) := by
  let μ : ℝ := (∑ j, c j) / (n : ℝ)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmean : (∑ j, c j) = (n : ℝ) * μ := by
    dsimp [μ]
    field_simp
  have hsquares : (∑ j, c j ^ 2) ≤ ∑ j, c j :=
    sum_le_sum fun j _ ↦ by nlinarith [hc0 j, hc1 j]
  have hexpand : (∑ j, (c j - μ) ^ 2) =
      (∑ j, c j ^ 2) - 2 * μ * (∑ j, c j) + (n : ℝ) * μ ^ 2 := by
    have heach (j : Fin n) : (c j - μ) ^ 2 = c j ^ 2 - (2 * μ) * c j + μ ^ 2 :=
      by ring
    simp_rw [heach]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    simp
  apply (div_le_div_iff_of_pos_right hn').mpr
  change (∑ j, (c j - μ) ^ 2) ≤ ∑ j, c j
  rw [hexpand, hmean] at *
  nlinarith [mul_nonneg (le_of_lt hn') (sq_nonneg μ)]

/-- The bounded-population Bernstein bound for any deterministic set of arrival times. -/
theorem bounded_population_tail {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (S : Finset (Fin n))
    (t : ℝ) (ht : 0 < t) :
    probPerm (fun σ ↦ t ≤ |(∑ k ∈ S, c (σ k)) -
        (S.card : ℝ) * ((∑ j, c j) / (n : ℝ))|) ≤
      2 * Real.exp (-(t ^ 2) /
        (2 * (S.card : ℝ) * ((∑ j, c j) / (n : ℝ)) + t)) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ : ℝ := (∑ j, c j) / (n : ℝ)
  let V : ℝ := (∑ j, (c j - μ) ^ 2) / (n : ℝ)
  let D : ℝ := (⨆ j, c j) - (⨅ j, c j)
  have hμ : 0 ≤ μ := bounded_population_mean_nonneg c hc0
  have hV : 0 ≤ V := by
    simpa only [Fintype.card_fin] using population_variance_nonneg c
  have hVμ : V ≤ μ := bounded_population_variance_le_mean hn c hc0 hc1
  have hD : 0 ≤ D := population_range_nonneg c
  have hD1 : D ≤ 1 := by
    have hup : (⨆ j, c j) ≤ 1 := ciSup_le hc1
    have hlo : 0 ≤ (⨅ j, c j) := le_ciInf hc0
    dsimp [D]
    linarith
  have hsize : S.card ≤ n := by simpa using S.card_le_univ
  have hprob : probPerm (fun σ ↦ t ≤ |(∑ k ∈ S, c (σ k)) - (S.card : ℝ) * μ|) =
      probPerm (fun σ ↦ t ≤ |(∑ k ∈ firstTimes n S.card, c (σ k)) -
        (S.card : ℝ) * μ|) := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq (firstTimes n S.card) S
      (firstTimes_card_eq hsize)
    have hsum (σ : Equiv.Perm (Fin n)) : (∑ k ∈ S, c (σ k)) =
        ∑ k ∈ firstTimes n S.card, c ((σ * τ) k) := by
      calc
        (∑ k ∈ S, c (σ k)) =
            ∑ k ∈ (firstTimes n S.card).map τ.toEmbedding, c (σ k) := by rw [hτ]
        _ = _ := by simp only [sum_map, Equiv.coe_toEmbedding]; rfl
    simp_rw [hsum]
    exact probPerm_comp_mulRight (fun σ : Equiv.Perm (Fin n) ↦
      t ≤ |(∑ k ∈ firstTimes n S.card, c (σ k)) - (S.card : ℝ) * μ|) τ
  change probPerm (fun σ ↦ t ≤ |(∑ k ∈ S, c (σ k)) - (S.card : ℝ) * μ|) ≤ _
  by_cases hzero : V = 0
  · have hc : ∀ j, c j = μ := by
      have hz := population_variance_eq_zero_iff c
      simp only [Fintype.card_fin] at hz
      exact hz.mp hzero
    have hevent : probPerm (fun σ ↦ t ≤
        |(∑ k ∈ S, c (σ k)) - (S.card : ℝ) * μ|) = 0 := by
      have hsumzero (σ : Equiv.Perm (Fin n)) :
          (∑ k ∈ S, c (σ k)) - (S.card : ℝ) * μ = 0 := by
        have hs : (∑ k ∈ S, c (σ k)) = ∑ _k ∈ S, μ :=
          sum_congr rfl (fun k _ ↦ hc (σ k))
        rw [hs]
        simp only [sum_const, nsmul_eq_mul, sub_self]
      unfold probPerm
      simp only [hsumzero, abs_zero, not_le.mpr ht, filter_false, card_empty,
        Nat.cast_zero, zero_div]
    rw [hevent]
    positivity
  by_cases hcard : S.card = 0
  · have hS : S = ∅ := card_eq_zero.mp hcard
    subst S
    unfold probPerm
    simp only [sum_empty, card_empty, Nat.cast_zero, zero_mul, sub_zero, abs_zero,
      not_le.mpr ht, filter_false, zero_div]
    positivity
  have hcardpos : 0 < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hcard
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
  have hden : 0 < 2 * (S.card : ℝ) * V + t * D := by positivity
  have hden' : 0 < 2 * (S.card : ℝ) * μ + t := by positivity
  have hdenle : 2 * (S.card : ℝ) * V + t * D ≤
      2 * (S.card : ℝ) * μ + t := by
    nlinarith [mul_nonneg (le_of_lt hcardpos) (sub_nonneg.mpr hVμ)]
  rw [hprob]
  apply (bernstein_without_replacement hn c S.card hsize t ht).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  change -(t ^ 2) / (2 * (S.card : ℝ) * V + t * D) ≤
    -(t ^ 2) / (2 * (S.card : ℝ) * μ + t)
  apply (div_le_div_iff₀ hden hden').mpr
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hdenle)]

private theorem block_tail_exponent_le (q t β h : ℝ) (hq0 : 0 ≤ q)
    (hβ : 0 < β) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (ht : h * β / 2 ≤ t) (hq : q ≤ t + 2 * β) :
    h ^ 2 * β / 32 ≤ t ^ 2 / (2 * q + t) := by
  have ht0 : 0 < t := by nlinarith
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hscale : h ^ 2 * β ≤ 2 * t := by nlinarith
  have hprod : h ^ 2 * β * t ≤ 2 * t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hscale (le_of_lt ht0)]
  have hsquare : h ^ 2 * β ^ 2 ≤ 4 * t ^ 2 := by
    have hs : (h * β) ^ 2 ≤ (2 * t) ^ 2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr
      nlinarith
    nlinarith
  have hmult : (2 * q + t) * (h ^ 2 * β) ≤
      (3 * t + 4 * β) * (h ^ 2 * β) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hden : 0 < 2 * q + t := by positivity
  apply (le_div_iff₀ hden).mpr
  nlinarith

private theorem bounded_population_tail_le {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (S : Finset (Fin n)) (t β h : ℝ) (hβ : 0 < β) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (ht : h * β / 2 ≤ t)
    (hq : (S.card : ℝ) * ((∑ j, c j) / (n : ℝ)) ≤ t + 2 * β) :
    probPerm (fun σ ↦ t ≤ |(∑ k ∈ S, c (σ k)) -
        (S.card : ℝ) * ((∑ j, c j) / (n : ℝ))|) ≤
      2 * Real.exp (-(h ^ 2 * β / 32)) := by
  have ht0 : 0 < t := by nlinarith
  apply (bounded_population_tail hn c hc0 hc1 S t ht0).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hq0 : 0 ≤ (S.card : ℝ) * ((∑ j, c j) / (n : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (bounded_population_mean_nonneg c hc0)
  have he := block_tail_exponent_le _ t β h hq0 hβ hh0 hh1 ht hq
  simpa only [neg_div, mul_assoc] using neg_le_neg he

theorem second_block_card {n ℓ : ℕ} (hℓ : 2 * ℓ ≤ n) :
    ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ).card = ℓ := by
  classical
  have hsub : firstTimes n ℓ ⊆ firstTimes n (2 * ℓ) := by
    intro k hk
    simp only [firstTimes, mem_filter, mem_univ, true_and] at *
    omega
  rw [card_sdiff_of_subset hsub, firstTimes_card_eq hℓ,
    firstTimes_card_eq (by omega : ℓ ≤ n)]
  omega

/-- Fixed-pattern feasibility block event (F), including both boundary equalities. -/
theorem bounded_blocks_feasible_tail {n ℓ : ℕ} (hn : 0 < n) (hℓ0 : 1 ≤ ℓ)
    (hℓ : 2 * ℓ ≤ n) (c : Fin n → ℝ)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (β h : ℝ) (hβ : 0 < β) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    probPerm (fun σ ↦
      (∑ k ∈ firstTimes n ℓ, c (σ k)) ≤ (1 - h) * β ∧
      β ≤ ∑ k ∈ ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ), c (σ k)) ≤
        4 * Real.exp (-(h ^ 2 * β / 32)) := by
  let μ : ℝ := (∑ j, c j) / (n : ℝ)
  let q : ℝ := (ℓ : ℝ) * μ
  have hcardA : (firstTimes n ℓ).card = ℓ := firstTimes_card_eq (by omega)
  have hcardB : ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ).card = ℓ :=
    second_block_card hℓ
  have hfour : 2 * Real.exp (-(h ^ 2 * β / 32)) ≤
      4 * Real.exp (-(h ^ 2 * β / 32)) := by
    nlinarith [Real.exp_pos (-(h ^ 2 * β / 32))]
  by_cases hsplit : (1 - h / 2) * β ≤ q
  · let d : ℝ := q - (1 - h) * β
    have hd : h * β / 2 ≤ d := by dsimp [d]; nlinarith
    have hq : q ≤ d + 2 * β := by dsimp [d]; nlinarith
    have hevent : probPerm (fun σ ↦
        (∑ k ∈ firstTimes n ℓ, c (σ k)) ≤ (1 - h) * β ∧
        β ≤ ∑ k ∈ ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ), c (σ k)) ≤
        probPerm (fun σ ↦ d ≤ |(∑ k ∈ firstTimes n ℓ, c (σ k)) - q|) := by
      apply probPerm_mono
      intro σ hσ
      have habs := neg_le_abs ((∑ k ∈ firstTimes n ℓ, c (σ k)) - q)
      dsimp [d]
      linarith [hσ.1]
    apply hevent.trans
    apply le_trans _ hfour
    have ht := bounded_population_tail_le hn c hc0 hc1 (firstTimes n ℓ)
      d β h hβ hh0 hh1 hd (by simpa only [hcardA] using hq)
    simpa only [hcardA] using ht
  · have hq : q < (1 - h / 2) * β := lt_of_not_ge hsplit
    have hq' : q ≤ h * β / 2 + 2 * β := by nlinarith
    have hevent : probPerm (fun σ ↦
        (∑ k ∈ firstTimes n ℓ, c (σ k)) ≤ (1 - h) * β ∧
        β ≤ ∑ k ∈ ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ), c (σ k)) ≤
        probPerm (fun σ ↦ h * β / 2 ≤
          |(∑ k ∈ ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ), c (σ k)) - q|) := by
      apply probPerm_mono
      intro σ hσ
      have habs := le_abs_self
        ((∑ k ∈ ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ), c (σ k)) - q)
      nlinarith [hσ.2]
    apply hevent.trans
    apply le_trans _ hfour
    have ht := bounded_population_tail_le hn c hc0 hc1
      ((firstTimes n (2 * ℓ)) \ firstTimes n ℓ) (h * β / 2) β h hβ hh0 hh1
      le_rfl (by simpa only [hcardB] using hq')
    simpa only [hcardB] using ht

/-- Fixed-pattern near-optimality block event (N), including both boundary equalities. -/
theorem bounded_blocks_nearoptimal_tail {n ℓ : ℕ} (hn : 0 < n) (hℓ0 : 1 ≤ ℓ)
    (hℓ : 2 * ℓ ≤ n) (c : Fin n → ℝ)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (β h e : ℝ) (hβ : 0 < β) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (he : 0 ≤ e) (hρ : 0 ≤ 1 - 2 * h - e) :
    probPerm (fun σ ↦
      (1 - h - e) * β ≤ ∑ k ∈ firstTimes n ℓ, c (σ k) ∧
      (∑ k ∈ firstTimes n (2 * ℓ), c (σ k)) ≤ 2 * (1 - 2 * h - e) * β) ≤
        4 * Real.exp (-(h ^ 2 * β / 32)) := by
  let μ : ℝ := (∑ j, c j) / (n : ℝ)
  let q : ℝ := (ℓ : ℝ) * μ
  let ρ : ℝ := 1 - 2 * h - e
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; linarith [hρ]
  have hcardA : (firstTimes n ℓ).card = ℓ := firstTimes_card_eq (by omega)
  have hcardT : (firstTimes n (2 * ℓ)).card = 2 * ℓ := firstTimes_card_eq hℓ
  have hmeanT : ((firstTimes n (2 * ℓ)).card : ℝ) * μ = 2 * q := by
    rw [hcardT]
    dsimp [q]
    push_cast
    ring
  have hfour : 2 * Real.exp (-(h ^ 2 * β / 32)) ≤
      4 * Real.exp (-(h ^ 2 * β / 32)) := by
    nlinarith [Real.exp_pos (-(h ^ 2 * β / 32))]
  by_cases hsplit : (ρ + h / 2) * β ≤ q
  · let d : ℝ := 2 * q - 2 * ρ * β
    have hd : h * β / 2 ≤ d := by dsimp [d]; nlinarith
    have hq : 2 * q ≤ d + 2 * β := by dsimp [d]; nlinarith
    have hevent : probPerm (fun σ ↦
        (1 - h - e) * β ≤ ∑ k ∈ firstTimes n ℓ, c (σ k) ∧
        (∑ k ∈ firstTimes n (2 * ℓ), c (σ k)) ≤ 2 * (1 - 2 * h - e) * β) ≤
        probPerm (fun σ ↦ d ≤ |(∑ k ∈ firstTimes n (2 * ℓ), c (σ k)) - 2 * q|) := by
      apply probPerm_mono
      intro σ hσ
      have habs := neg_le_abs ((∑ k ∈ firstTimes n (2 * ℓ), c (σ k)) - 2 * q)
      dsimp [d, ρ]
      linarith [hσ.2]
    apply hevent.trans
    apply le_trans _ hfour
    have ht := bounded_population_tail_le hn c hc0 hc1 (firstTimes n (2 * ℓ))
      d β h hβ hh0 hh1 hd (by change _ * μ ≤ _; simpa only [hmeanT] using hq)
    change probPerm (fun σ ↦ d ≤ |(∑ k ∈ firstTimes n (2 * ℓ), c (σ k)) -
      ((firstTimes n (2 * ℓ)).card : ℝ) * μ|) ≤ _ at ht
    simpa only [hmeanT] using ht
  · have hq : q < (ρ + h / 2) * β := lt_of_not_ge hsplit
    have hq' : q ≤ h * β / 2 + 2 * β := by nlinarith
    have hevent : probPerm (fun σ ↦
        (1 - h - e) * β ≤ ∑ k ∈ firstTimes n ℓ, c (σ k) ∧
        (∑ k ∈ firstTimes n (2 * ℓ), c (σ k)) ≤ 2 * (1 - 2 * h - e) * β) ≤
        probPerm (fun σ ↦ h * β / 2 ≤ |(∑ k ∈ firstTimes n ℓ, c (σ k)) - q|) := by
      apply probPerm_mono
      intro σ hσ
      have habs := le_abs_self ((∑ k ∈ firstTimes n ℓ, c (σ k)) - q)
      dsimp [ρ] at hq
      nlinarith [hσ.1]
    apply hevent.trans
    apply le_trans _ hfour
    have ht := bounded_population_tail_le hn c hc0 hc1 (firstTimes n ℓ)
      (h * β / 2) β h hβ hh0 hh1 le_rfl (by simpa only [hcardA] using hq')
    simpa only [hcardA] using ht

end TCSShortlistPriceNearOptimal.Bernstein

/-! Deterministic packing-LP support for the canonical learned-price rule.
The compactness and duality arguments are copied from the accepted local proofs;
resource complementary slackness and the training bounds are proved here.
-/

open scoped BigOperators
open Matrix

namespace DynamicOnlineLP.DLA.TrainingPrices

theorem feasibleOptimumExists {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    ∃ x : α → ℝ, IsPrimalOptimal S π a d x ∧ (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
      (∀ j, j ∉ S → x j = 0) ∧ primalObj S π x = optValue S π a d := by
  classical
  let K : Set (α → ℝ) := {x | IsFeasible S a d x} ∩ Set.Icc 0 1
  have hclosed : IsClosed {x : α → ℝ | IsFeasible S a d x} := by
    have heq : {x : α → ℝ | IsFeasible S a d x} =
        (⋂ i : Fin m, {x : α → ℝ | ∑ t ∈ S, a t i * x t ≤ d i}) ∩
        (⋂ j : α, ⋂ _ : j ∈ S, {x : α → ℝ | 0 ≤ x j ∧ x j ≤ 1}) := by
      ext x
      simp [IsFeasible]
    rw [heq]
    apply IsClosed.inter
    · exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
        (isClosed_le continuous_const (continuous_apply j)).inter
          (isClosed_le (continuous_apply j) continuous_const)
  have hcompact : IsCompact K := isCompact_Icc.inter_left hclosed
  have hzero : (0 : α → ℝ) ∈ K := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      simpa using hd i
    · simp
    · exact ⟨le_rfl, by intro j; norm_num⟩
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩
    (show ContinuousOn (primalObj S π) K by unfold primalObj; fun_prop)
  let z : α → ℝ := fun j ↦ if j ∈ S then x j else 0
  have hzfeas : IsFeasible S a d z := by
    constructor
    · simpa [z] using hx.1.1
    · intro j hj
      simpa [z, hj] using hx.1.2 j hj
  have hzbox : ∀ j, 0 ≤ z j ∧ z j ≤ 1 := by
    intro j
    by_cases hj : j ∈ S
    · simpa [z, hj] using And.intro (hx.2.1 j) (hx.2.2 j)
    · simp [z, hj]
  have hobj : primalObj S π z = primalObj S π x := by simp [primalObj, z]
  have hbound (w : α → ℝ) (hw : IsFeasible S a d w) :
      primalObj S π w ≤ primalObj S π z := by
    let w' : α → ℝ := fun j ↦ if j ∈ S then w j else 0
    have hw' : w' ∈ K := by
      refine ⟨?_, ?_⟩
      · constructor
        · simpa [w'] using hw.1
        · intro j hj
          simpa [w', hj] using hw.2 j hj
      · constructor <;> intro j <;> by_cases hj : j ∈ S
        · simpa [w', hj] using (hw.2 j hj).1
        · simp [w', hj]
        · simpa [w', hj] using (hw.2 j hj).2
        · simp [w', hj]
    rw [hobj]
    simpa [primalObj, w'] using hmax hw'
  refine ⟨z, ⟨hzfeas, hbound⟩, hzbox, ?_, ?_⟩
  · intro j hj
    simp [z, hj]
  · have hbd : BddAbove (primalObj S π '' {x | IsFeasible S a d x}) := by
      refine ⟨primalObj S π z, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact hbound w hw
    apply le_antisymm
    · exact le_csSup hbd ⟨z, hzfeas, rfl⟩
    · apply csSup_le
      · exact ⟨primalObj S π z, z, hzfeas, rfl⟩
      · rintro y ⟨w, hw, rfl⟩
        exact hbound w hw

private theorem packing_weak_duality {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsFeasible S a d x) (hy : IsDualFeasible S π a p y) :
    primalObj S π x ≤ dualObj S d p y := by
  classical
  calc
    primalObj S π x ≤ ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
    _ = (∑ i, p i * (∑ t ∈ S, a t i * x t)) + ∑ t ∈ S, y t * x t := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ (∑ i, p i * d i) + ∑ t ∈ S, y t := by
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
      · exact Finset.sum_le_sum fun t ht ↦
          (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
    _ = dualObj S d p y := by simp only [dualObj, mul_comm]

private theorem packing_optimal_values_eq {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsPrimalOptimal S π a d x)
    (hy : IsDualOptimal S π a d p y) : primalObj S π x = dualObj S d p y := by
  classical
  let Row := Fin m ⊕ (↥S ⊕ ↥S)
  let A : Matrix Row ↥S ℝ := fun r t ↦ match r with
    | Sum.inl i => a t i
    | Sum.inr (Sum.inl s) => if s = t then 1 else 0
    | Sum.inr (Sum.inr s) => if s = t then -1 else 0
  let b : Row → ℝ
    | Sum.inl i => d i
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 0
  let c : ↥S → ℝ := fun t ↦ π t
  let dual0 : Row → ℝ
    | Sum.inl i => p i
    | Sum.inr (Sum.inl t) => y t
    | Sum.inr (Sum.inr t) => (∑ i, a t i * p i) + y t - π t
  have hP : ∃ u : ↥S → ℝ, A *ᵥ u ≤ b := by
    refine ⟨fun t ↦ x t, ?_⟩
    rintro (i | t | t)
    · change (∑ t : ↥S, a t.val i * x t.val) ≤ d i
      rw [Finset.sum_coe_sort S (fun t ↦ a t i * x t)]
      exact hx.1.1 i
    · simpa [A, b, Matrix.mulVec, dotProduct] using (hx.1.2 t.val t.property).2
    · simpa [A, b, Matrix.mulVec, dotProduct] using
        neg_nonpos.mpr (hx.1.2 t.val t.property).1
  have hD : ∃ v : Row → ℝ, 0 ≤ v ∧ Aᵀ *ᵥ v = c := by
    refine ⟨dual0, ?_, ?_⟩
    · rintro (i | t | t)
      · exact hy.1.1 i
      · exact (hy.1.2 t.val t.property).1
      · exact sub_nonneg.mpr (hy.1.2 t.val t.property).2
    · funext t
      change (∑ r : Row, A r t * dual0 r) = π t
      simp [Row, A, dual0, Fintype.sum_sum_type]
      ring
  obtain ⟨u, v, hu, hv, hvA, heq, _⟩ := LP.strong_duality_matrix A b c hP hD
  let u' : ι → ℝ := fun t ↦ if ht : t ∈ S then u ⟨t, ht⟩ else 0
  let p' : Fin m → ℝ := fun i ↦ v (Sum.inl i)
  let y' : ι → ℝ := fun t ↦ if ht : t ∈ S then v (Sum.inr (Sum.inl ⟨t, ht⟩)) else 0
  have hu' : IsFeasible S a d u' := by
    constructor
    · intro i
      have h := hu (Sum.inl i)
      change (∑ t : ↥S, a t i * u t) ≤ d i at h
      rw [← Finset.sum_coe_sort S (fun t ↦ a t i * u' t)]
      simpa [u'] using h
    · intro t ht
      have hlo := hu (Sum.inr (Sum.inr ⟨t, ht⟩))
      have hhi := hu (Sum.inr (Sum.inl ⟨t, ht⟩))
      constructor
      · have hlo' : -u ⟨t, ht⟩ ≤ 0 := by
          simpa [Matrix.mulVec, dotProduct, A, b] using hlo
        simpa [u', ht] using neg_nonpos.mp hlo'
      · simpa [Matrix.mulVec, dotProduct, A, b, u', ht] using hhi
  have hy' : IsDualFeasible S π a p' y' := by
    refine ⟨fun i ↦ hv (Sum.inl i), ?_⟩
    intro t ht
    refine ⟨by simpa [y', ht] using hv (Sum.inr (Sum.inl ⟨t, ht⟩)), ?_⟩
    have h := congrFun hvA ⟨t, ht⟩
    have hlo := hv (Sum.inr (Sum.inr ⟨t, ht⟩))
    change (0 : ℝ) ≤ v (Sum.inr (Sum.inr ⟨t, ht⟩)) at hlo
    change (∑ r : Row, A r ⟨t, ht⟩ * v r) = π t at h
    simp [Row, A, Fintype.sum_sum_type] at h
    dsimp [p']
    simp only [y', dif_pos ht]
    linarith
  have hprimal : primalObj S π u' = c ⬝ᵥ u := by
    unfold primalObj
    rw [← Finset.sum_coe_sort S (fun t ↦ π t * u' t)]
    simp [dotProduct, c, u']
  have hdual : dualObj S d p' y' = b ⬝ᵥ v := by
    unfold dualObj
    rw [← Finset.sum_coe_sort S y']
    simp [Row, dotProduct, b, p', y', Fintype.sum_sum_type]
  apply le_antisymm
  · exact packing_weak_duality S π a d x p y hx.1 hy.1
  · calc
      dualObj S d p y ≤ dualObj S d p' y' := hy.2 p' y' hy'
      _ = b ⬝ᵥ v := hdual
      _ = c ⬝ᵥ u := heq.symm
      _ = primalObj S π u' := hprimal.symm
      _ ≤ primalObj S π x := hx.2 u' hu'

private theorem packing_complementarity {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsFeasible S a d x)
    (hy : IsDualFeasible S π a p y) (heq : primalObj S π x = dualObj S d p y) :
    ∀ t ∈ S, ((∑ i, a t i * p i) + y t - π t) * x t = 0 ∧ y t * (1 - x t) = 0 := by
  classical
  let W := ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t
  let R := ∑ i, p i * (∑ t ∈ S, a t i * x t)
  let B := ∑ i, d i * p i
  let Y := ∑ t ∈ S, y t * x t
  let Q := ∑ t ∈ S, y t
  have hW : W = R + Y := by
    dsimp [W, R, Y]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hR : R ≤ B := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
  have hY : Y ≤ Q := Finset.sum_le_sum fun t ht ↦
    (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
  have hfirst : primalObj S π x ≤ W := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
  have hWupper : W ≤ B + Y := by rw [hW]; exact add_le_add hR le_rfl
  have hdual : dualObj S d p y = B + Q := rfl
  have heqW : W = dualObj S d p y := by
    apply le_antisymm
    · exact hWupper.trans (add_le_add le_rfl hY)
    · rw [← heq]
      exact hfirst
  have hYeq : Y = Q := by linarith [heqW, hdual, hWupper]
  have hA0 : (∑ t ∈ S, ((∑ i, a t i * p i) + y t - π t) * x t) = 0 := by
    calc
      _ = W - primalObj S π x := by
        dsimp [W, primalObj]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [heqW, heq]; ring
  have hB0 : (∑ t ∈ S, y t * (1 - x t)) = 0 := by
    calc
      _ = Q - Y := by
        dsimp [Q, Y]
        simp_rw [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hYeq]; ring
  have hApos (t : ι) (ht : t ∈ S) :
      0 ≤ ((∑ i, a t i * p i) + y t - π t) * x t :=
    mul_nonneg (sub_nonneg.mpr (hy.2 t ht).2) (hx.2 t ht).1
  have hBpos (t : ι) (ht : t ∈ S) : 0 ≤ y t * (1 - x t) :=
    mul_nonneg (hy.2 t ht).1 (sub_nonneg.mpr (hx.2 t ht).2)
  intro t ht
  constructor
  · exact le_antisymm ((Finset.single_le_sum hApos ht).trans_eq hA0) (hApos t ht)
  · exact le_antisymm ((Finset.single_le_sum hBpos ht).trans_eq hB0) (hBpos t ht)

theorem thresholdComparison {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsPrimalOptimal S π a d x) (hpy : IsDualOptimal S π a d p y) :
    (∀ t ∈ S, threshold π a p t ≤ x t) ∧
      (GeneralPositionOn S π a → (S.filter (fun t => threshold π a p t ≠ x t)).card ≤ m) := by
  classical
  have heq := packing_optimal_values_eq S π a d x p y hx hpy
  have hcomp := packing_complementarity S π a d x p y hx.1 hpy.1 heq
  have hsum (t : ι) : (∑ i, p i * a t i) = ∑ i, a t i * p i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hthreshold : ∀ t ∈ S, threshold π a p t ≤ x t := by
    intro t ht
    by_cases hπ : π t ≤ ∑ i, p i * a t i
    · simpa [threshold, hπ] using (hx.1.2 t ht).1
    · have hπ' : (∑ i, a t i * p i) < π t := by
        simpa only [hsum t] using lt_of_not_ge hπ
      have hypos : 0 < y t := by linarith [(hpy.1.2 t ht).2]
      have hxone : x t = 1 := by
        rcases mul_eq_zero.mp (hcomp t ht).2 with h | h
        · exact False.elim ((ne_of_gt hypos) h)
        · linarith
      simp [threshold, hπ, hxone]
  refine ⟨hthreshold, ?_⟩
  intro hgp
  apply le_trans (Finset.card_le_card ?_) (hgp p)
  intro t ht
  obtain ⟨htS, hne⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htS, ?_⟩
  by_contra hnot
  rcases lt_or_gt_of_ne hnot with hlt | hgt
  · have hπ : ¬ π t ≤ ∑ i, p i * a t i := not_le_of_gt hlt
    have hxone : x t = 1 := le_antisymm (hx.1.2 t htS).2
      (by simpa [threshold, hπ] using hthreshold t htS)
    exact hne (by simp [threshold, hπ, hxone])
  · have hπ : π t ≤ ∑ i, p i * a t i := le_of_lt hgt
    have hδpos : 0 < (∑ i, a t i * p i) + y t - π t := by
      rw [hsum t] at hgt
      linarith [(hpy.1.2 t htS).1]
    have hxzero : x t = 0 :=
      (mul_eq_zero.mp (hcomp t htS).1).resolve_left (ne_of_gt hδpos)
    exact hne (by simp [threshold, hπ, hxzero])

/-- Zero duality gap forces each resource price times its slack to vanish. -/
theorem resourceComplementarity {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsFeasible S a d x)
    (hy : IsDualFeasible S π a p y) (heq : primalObj S π x = dualObj S d p y) :
    ∀ i, p i * (d i - ∑ t ∈ S, a t i * x t) = 0 := by
  classical
  let W := ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t
  let R := ∑ i, p i * (∑ t ∈ S, a t i * x t)
  let B := ∑ i, d i * p i
  let Y := ∑ t ∈ S, y t * x t
  let Q := ∑ t ∈ S, y t
  have hW : W = R + Y := by
    dsimp [W, R, Y]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hR : R ≤ B := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
  have hY : Y ≤ Q := Finset.sum_le_sum fun t ht ↦
    (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
  have hfirst : primalObj S π x ≤ W := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
  have hdual : dualObj S d p y = B + Q := rfl
  have hReq : R = B := by linarith only [hW, hR, hY, hfirst, heq, hdual]
  have hsum : (∑ i, p i * (d i - ∑ t ∈ S, a t i * x t)) = 0 := by
    calc
      _ = B - R := by
        dsimp [B, R]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hReq]; ring
  have hnonneg (i : Fin m) (_ : i ∈ Finset.univ) :
      0 ≤ p i * (d i - ∑ t ∈ S, a t i * x t) :=
    mul_nonneg (hy.1 i) (sub_nonneg.mpr (hx.1 i))
  intro i
  exact le_antisymm ((Finset.single_le_sum hnonneg (Finset.mem_univ i)).trans_eq hsum)
    (hnonneg i (Finset.mem_univ i))

/-- Every positive-price resource is saturated at a primal optimum. -/
theorem positivePrice_saturated {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsPrimalOptimal S π a d x)
    (hy : IsDualOptimal S π a d p y) (i : Fin m) (hi : 0 < p i) :
    (∑ t ∈ S, a t i * x t) = d i := by
  have h := resourceComplementarity S π a d x p y hx.1 hy.1
    (packing_optimal_values_eq S π a d x p y hx hy) i
  have hzero := (mul_eq_zero.mp h).resolve_left (ne_of_gt hi)
  linarith only [hzero]

/-- Canonical threshold proposals from an optimal dual price are resource feasible. -/
theorem thresholdLoad_le {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ t ∈ S, ∀ i, 0 ≤ a t i) (hp : IsOptimalDualPrice S π a d p) (i : Fin m) :
    (∑ t ∈ S, a t i * threshold π a p t) ≤ d i := by
  obtain ⟨x, hx, _, _, _⟩ := feasibleOptimumExists S π a d hd
  obtain ⟨y, hy⟩ := hp
  have hcomp := (thresholdComparison S π a d x p y hx hy).1
  exact (Finset.sum_le_sum fun t ht ↦
    mul_le_mul_of_nonneg_left (hcomp t ht) (ha t ht i)).trans (hx.1.1 i)

/-- In general position, a positive-price resource loses at most `m` units
when a primal optimum is replaced by its canonical threshold proposal. -/
theorem thresholdLoad_lower {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ t ∈ S, ∀ i, 0 ≤ a t i ∧ a t i ≤ 1)
    (hp : IsOptimalDualPrice S π a d p) (hgp : GeneralPositionOn S π a)
    (i : Fin m) (hi : 0 < p i) :
    d i - (m : ℝ) ≤ ∑ t ∈ S, a t i * threshold π a p t := by
  classical
  obtain ⟨x, hx, _, _, _⟩ := feasibleOptimumExists S π a d hd
  obtain ⟨y, hy⟩ := hp
  have hsat := positivePrice_saturated S π a d x p y hx hy i hi
  have hcard := (thresholdComparison S π a d x p y hx hy).2 hgp
  have hterm (t : α) (ht : t ∈ S) :
      a t i * x t ≤ a t i * threshold π a p t +
        if threshold π a p t ≠ x t then 1 else 0 := by
    by_cases hne : threshold π a p t ≠ x t
    · have hxone : a t i * x t ≤ 1 := by
        calc
          _ ≤ a t i * 1 := mul_le_mul_of_nonneg_left (hx.1.2 t ht).2 (ha t ht i).1
          _ = a t i := mul_one _
          _ ≤ 1 := (ha t ht i).2
      have hthreshold : 0 ≤ threshold π a p t := by
        unfold threshold
        split_ifs <;> norm_num
      have hnonneg := mul_nonneg (ha t ht i).1 hthreshold
      simp only [if_pos hne]
      linarith only [hxone, hnonneg]
    · have heq : threshold π a p t = x t := not_ne_iff.mp hne
      simp only [heq, ne_eq, not_true_eq_false, if_false, add_zero, le_refl]
  have hsum := Finset.sum_le_sum hterm
  have hcount : (∑ t ∈ S, if threshold π a p t ≠ x t then (1 : ℝ) else 0) =
      ((S.filter (fun t ↦ threshold π a p t ≠ x t)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_add_distrib, hcount] at hsum
  have hcard' : ((S.filter (fun t ↦ threshold π a p t ≠ x t)).card : ℝ) ≤ m := by
    exact_mod_cast hcard
  linarith only [hsat, hsum, hcard']

/-- The two deterministic training bounds at an arbitrary canonical optimal dual price. -/
theorem trainingBounds {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ t ∈ S, ∀ i, 0 ≤ a t i ∧ a t i ≤ 1)
    (hp : IsOptimalDualPrice S π a d p) (hgp : GeneralPositionOn S π a) :
    ∀ i, (∑ t ∈ S, a t i * threshold π a p t) ≤ d i ∧
      (0 < p i → d i - (m : ℝ) ≤ ∑ t ∈ S, a t i * threshold π a p t) := by
  intro i
  exact ⟨thresholdLoad_le S π a d p hd (fun t ht i ↦ (ha t ht i).1) hp i,
    thresholdLoad_lower S π a d p hd ha hp hgp i⟩

/-- Positive-price resource coverage converts directly into a scaled optimum
bound for canonical threshold revenue. No dual optimality is assumed here. -/
theorem scaledOptimum_le_thresholdRevenue {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (ρ : ℝ) (hd : ∀ i, 0 ≤ d i) (hp : ∀ i, 0 ≤ p i)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hcoverage : ∀ i, 0 < p i → ρ * d i ≤ ∑ t ∈ S, a t i * threshold π a p t) :
    ρ * optValue S π a d ≤ primalObj S π (threshold π a p) := by
  classical
  let y : α → ℝ := fun t ↦ max (π t - ∑ i, a t i * p i) 0
  have hy0 (t : α) : 0 ≤ y t := le_max_right _ _
  have hy : IsDualFeasible S π a p y := by
    refine ⟨hp, ?_⟩
    intro t ht
    refine ⟨hy0 t, ?_⟩
    have h : π t - ∑ i, a t i * p i ≤ y t := le_max_left _ _
    linarith only [h]
  obtain ⟨x, hx, _, _, hxeq⟩ := feasibleOptimumExists S π a d hd
  have hopt : optValue S π a d ≤ dualObj S d p y := by
    rw [← hxeq]
    exact packing_weak_duality S π a d x p y hx.1 hy
  have hcost (t : α) : (∑ i, p i * a t i) = ∑ i, a t i * p i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcolumn (t : α) : π t * threshold π a p t =
      (∑ i, a t i * p i) * threshold π a p t + y t := by
    by_cases hπ : π t ≤ ∑ i, p i * a t i
    · have hdiff : π t - ∑ i, a t i * p i ≤ 0 := by
        rw [hcost t] at hπ
        exact sub_nonpos.mpr hπ
      simp only [threshold, if_pos hπ, mul_zero, zero_add, y, max_eq_right hdiff]
    · have hdiff : 0 ≤ π t - ∑ i, a t i * p i := by
        rw [hcost t] at hπ
        exact sub_nonneg.mpr (le_of_lt (lt_of_not_ge hπ))
      simp only [threshold, if_neg hπ, mul_one, y, max_eq_left hdiff]
      ring
  have hobj : primalObj S π (threshold π a p) =
      (∑ i, p i * (∑ t ∈ S, a t i * threshold π a p t)) + ∑ t ∈ S, y t := by
    unfold primalObj
    simp_rw [hcolumn, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hprice (i : Fin m) : ρ * (d i * p i) ≤
      p i * (∑ t ∈ S, a t i * threshold π a p t) := by
    by_cases hi : p i = 0
    · simp only [hi, mul_zero, mul_zero, zero_mul, le_refl]
    · have hipos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
      calc
        ρ * (d i * p i) = p i * (ρ * d i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcoverage i hipos) (hp i)
  have hY : ρ * (∑ t ∈ S, y t) ≤ ∑ t ∈ S, y t := by
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun t ht ↦ hy0 t) hρ.2
  calc
    ρ * optValue S π a d ≤ ρ * dualObj S d p y :=
      mul_le_mul_of_nonneg_left hopt hρ.1
    _ = (∑ i, ρ * (d i * p i)) + ρ * (∑ t ∈ S, y t) := by
      simp only [dualObj, mul_add, Finset.mul_sum]
    _ ≤ (∑ i, p i * (∑ t ∈ S, a t i * threshold π a p t)) + ∑ t ∈ S, y t :=
      add_le_add (Finset.sum_le_sum fun i hi ↦ hprice i) hY
    _ = primalObj S π (threshold π a p) := hobj.symm

end DynamicOnlineLP.DLA.TrainingPrices

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistPriceNearOptimal.LearnedPrices

theorem eps_pos (E : ℕ) : 0 < eps E := pow_pos (by norm_num) _

theorem eps_le_half {E : ℕ} (hE : 1 ≤ E) : eps E ≤ 1 / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : E ≠ 0)
  unfold eps
  rw [pow_succ]
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem learnLen_mul_pow_eq {n E : ℕ} (hdvd : 2 ^ E ∣ n) :
    learnLen n E * 2 ^ E = n := Nat.div_mul_cancel hdvd

theorem learnLen_pos {n E : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n) :
    0 < learnLen n E := by
  exact Nat.div_pos (Nat.le_of_dvd hn hdvd) (pow_pos (by decide) _)

theorem eps_mul_population_eq_learnLen {n E : ℕ} (hdvd : 2 ^ E ∣ n) :
    eps E * (n : ℝ) = (learnLen n E : ℝ) := by
  have h : (learnLen n E : ℝ) * (2 : ℝ) ^ E = n := by
    exact_mod_cast learnLen_mul_pow_eq hdvd
  have hp : (2 : ℝ) ^ E ≠ 0 := by positivity
  unfold eps
  rw [div_pow, one_pow]
  rw [← h]
  field_simp

theorem phase_time_bounds {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) : 0 < ℓ ∧ 2 * ℓ ≤ n ∧ learnLen n E ≤ ℓ := by
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hℓ
  have hkE : k < E := mem_range.mp hk
  have hlen := learnLen_pos hn hdvd
  have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  refine ⟨mul_pos hlen hpow, ?_, Nat.le_mul_of_pos_right _ hpow⟩
  calc
    2 * (learnLen n E * 2 ^ k) = learnLen n E * 2 ^ (k + 1) := by
      rw [pow_succ]
      ring
    _ ≤ learnLen n E * 2 ^ E :=
      Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))
    _ = n := learnLen_mul_pow_eq hdvd

theorem phase_card_le (n E : ℕ) : (phases n E).card ≤ E := by
  exact (card_image_le).trans_eq (card_range E)

theorem exponent_le_population {n E : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n) : E ≤ n := by
  exact (Nat.le_of_lt (Nat.lt_two_pow_self : E < 2 ^ E)).trans (Nat.le_of_dvd hn hdvd)

theorem two_le_population {n E : ℕ} (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) : 2 ≤ n := by
  have hpow : (2 : ℕ) ≤ 2 ^ E := by
    simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hE
  exact hpow.trans (Nat.le_of_dvd hn hdvd)

theorem phase_ratio_bounds {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) : 0 < (ℓ : ℝ) / n ∧ eps E ≤ (ℓ : ℝ) / n := by
  obtain ⟨hℓpos, _, hlen⟩ := phase_time_bounds hn hdvd hℓ
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨div_pos (by exact_mod_cast hℓpos) hnreal, ?_⟩
  apply (le_div_iff₀ hnreal).mpr
  rw [eps_mul_population_eq_learnLen hdvd]
  exact_mod_cast hlen

theorem phase_slack_sq_ratio {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) :
    (slack n E ℓ) ^ 2 * ((ℓ : ℝ) / n) = (eps E) ^ 2 := by
  have hℓpos := (phase_time_bounds hn hdvd hℓ).1
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hℓreal : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  unfold slack
  rw [mul_pow, Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  field_simp

theorem phase_slack_bounds {n E ℓ : ℕ} (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) (hℓ : ℓ ∈ phases n E) :
    0 < slack n E ℓ ∧ slack n E ℓ ≤ 1 := by
  have hℓpos := (phase_time_bounds hn hdvd hℓ).1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓreal : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hpos : 0 < slack n E ℓ :=
    mul_pos (eps_pos E) (Real.sqrt_pos.mpr (div_pos hnreal hℓreal))
  refine ⟨hpos, ?_⟩
  have hratio := phase_ratio_bounds hn hdvd hℓ
  have heps := eps_pos E
  have hhalf := eps_le_half hE
  have hepssq : (eps E) ^ 2 ≤ eps E := by nlinarith
  have heq := phase_slack_sq_ratio hn hdvd hℓ
  apply le_of_not_gt
  intro hgt
  have hsq : 1 < (slack n E ℓ) ^ 2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hsq hratio.1
  rw [one_mul, heq] at hmul
  exact (not_lt_of_ge (hepssq.trans hratio.2)) hmul

theorem phase_budget_identity {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) (b : ℝ) :
    (slack n E ℓ) ^ 2 * (((ℓ : ℝ) / n) * b) = (eps E) ^ 2 * b := by
  rw [← mul_assoc, phase_slack_sq_ratio hn hdvd hℓ]

theorem log_population_accuracy_ge_one {n E : ℕ} (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) : 1 ≤ Real.log ((n : ℝ) / eps E) := by
  have heps := eps_pos E
  have hhalf := eps_le_half hE
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast two_le_population hn hE hdvd
  have hQ : (4 : ℝ) ≤ (n : ℝ) / eps E := (le_div_iff₀ heps).mpr (by linarith)
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  exact Real.exp_one_lt_three.le.trans (by linarith)

end TCSShortlistPriceNearOptimal.LearnedPrices

/-!
Deterministic interfaces for the exact canonical learned-price output. General
position is transported through the actual arrival permutation, and no selected
representative price replaces the dual rule's output.
-/

open scoped BigOperators
open DynamicOnlineLP.DLA

namespace TCSShortlistPriceNearOptimal.LearnedPrices

/-- General position survives permutation and restriction to any time set. -/
theorem generalPositionOn_arrivals {m n : ℕ} (I : Instance m n)
    (hgp : I.GeneralPosition) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    GeneralPositionOn S (I.arrPi σ) (I.arrA σ) := by
  classical
  intro p
  have himage :
      (S.filter (fun t => ∑ i : Fin m, p i * I.arrA σ t i = I.arrPi σ t)).image σ ⊆
        Finset.univ.filter (fun j => ∑ i : Fin m, p i * I.a j i = I.π j) := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
  calc
    (S.filter (fun t => ∑ i : Fin m, p i * I.arrA σ t i = I.arrPi σ t)).card =
        ((S.filter (fun t => ∑ i : Fin m, p i * I.arrA σ t i = I.arrPi σ t)).image σ).card :=
      (Finset.card_image_of_injective _ σ.injective).symm
    _ ≤ (Finset.univ.filter (fun j => ∑ i : Fin m, p i * I.a j i = I.π j)).card :=
      Finset.card_le_card himage
    _ ≤ m := hgp p

/-- The canonical learned price is optimal for its exact training right side. -/
theorem learnedPrice_optimal {m n : ℕ} (I : Instance m n) (rule : DualRule m n)
    (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hvalid : IsValidDualRule rule)
    (hℓ : ℓ ≤ n)
    (hd : ∀ i, 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i) :
    IsOptimalDualPrice (firstTimes n ℓ) (I.arrPi σ) (I.arrA σ)
      (fun i => (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
      (learnedPrice I rule E σ ℓ) := by
  exact hvalid.2 ℓ (I.arrPi σ) (I.arrA σ) _ hℓ hd

/-- Validity forces every coordinate of the actual learned price to be nonnegative. -/
theorem learnedPrice_nonneg {m n : ℕ} (I : Instance m n) (rule : DualRule m n)
    (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hvalid : IsValidDualRule rule)
    (hℓ : ℓ ≤ n)
    (hd : ∀ i, 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i) :
    ∀ i, 0 ≤ learnedPrice I rule E σ ℓ i := by
  obtain ⟨y, hy⟩ := learnedPrice_optimal I rule E σ ℓ hvalid hℓ hd
  exact hy.1.1

/-- Both training bounds hold for the output of the canonical dual rule itself. -/
theorem learnedPrice_trainingBounds {m n : ℕ} (I : Instance m n) (rule : DualRule m n)
    (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hvalid : IsValidDualRule rule)
    (hℓ : ℓ ≤ n)
    (hd : ∀ i, 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
    (hgp : I.GeneralPosition) :
    ∀ i,
      (∑ t ∈ firstTimes n ℓ,
        I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ)
          (learnedPrice I rule E σ ℓ) t) ≤
          (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i ∧
      (0 < learnedPrice I rule E σ ℓ i →
        (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i - (m : ℝ) ≤
          ∑ t ∈ firstTimes n ℓ,
            I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ)
              (learnedPrice I rule E σ ℓ) t) := by
  exact TrainingPrices.trainingBounds (firstTimes n ℓ) (I.arrPi σ) (I.arrA σ)
    (fun i => (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
    (learnedPrice I rule E σ ℓ) hd
    (fun t _ i => ⟨I.a_nonneg (σ t) i, I.a_le_one (σ t) i⟩)
    (learnedPrice_optimal I rule E σ ℓ hvalid hℓ hd)
    (generalPositionOn_arrivals I hgp σ (firstTimes n ℓ))

/-- A fixed Boolean pattern defines a population in the interval `[0,1]`. -/
theorem pattern_population_bounds {m n : ℕ} (I : Instance m n)
    (v : Fin n → Bool) (i : Fin m) :
    ∀ j, 0 ≤ (if v j then I.a j i else 0) ∧ (if v j then I.a j i else 0) ≤ 1 := by
  intro j
  split_ifs
  · exact ⟨I.a_nonneg j i, I.a_le_one j i⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The strict base-column pattern is the exact threshold load after permutation. -/
theorem threshold_population_eq {m n : ℕ} (I : Instance m n)
    (σ : Equiv.Perm (Fin n)) (p : Fin m → ℝ) (i : Fin m) (t : Fin n) :
    (if decide ((∑ k : Fin m, p k * I.a (σ t) k) < I.π (σ t))
      then I.a (σ t) i else 0) =
        I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ) p t := by
  classical
  by_cases h : I.π (σ t) ≤ ∑ k : Fin m, p k * I.a (σ t) k
  · simp [threshold, Instance.arrPi, Instance.arrA, h, not_lt.mpr h]
  · simp [threshold, Instance.arrPi, Instance.arrA, h, lt_of_not_ge h]

/-- The population identity also holds on every fixed time set. -/
theorem threshold_population_sum_eq {m n : ℕ} (I : Instance m n)
    (σ : Equiv.Perm (Fin n)) (p : Fin m → ℝ) (i : Fin m) (S : Finset (Fin n)) :
    (∑ t ∈ S, if decide ((∑ k : Fin m, p k * I.a (σ t) k) < I.π (σ t))
      then I.a (σ t) i else 0) =
        ∑ t ∈ S, I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ) p t := by
  apply Finset.sum_congr rfl
  intro t _
  exact threshold_population_eq I σ p i t

/-- Difference of the two prefix sets is the exact window in Lemma 5. -/
theorem secondBlock_eq_window (n ℓ : ℕ) :
    (firstTimes n (2 * ℓ)) \ firstTimes n ℓ =
      Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ) := by
  ext t
  simp only [Finset.mem_sdiff, firstTimes, Finset.mem_filter, Finset.mem_univ,
    true_and, not_lt]
  exact and_comm

end TCSShortlistPriceNearOptimal.LearnedPrices

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistPriceNearOptimal.LearnedPrices

private theorem probPerm_eq_count {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    [DecidablePred P] : probPerm P =
      ((univ.filter P).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  unfold probPerm
  congr

theorem probPerm_not {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) :
    probPerm (fun σ ↦ ¬P σ) = 1 - probPerm P := by
  classical
  have hn : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard : ((univ.filter P).card : ℝ) +
      ((univ.filter (fun σ ↦ ¬P σ)).card : ℝ) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := univ) P)
  simp only [probPerm_eq_count]
  apply eq_sub_iff_add_eq.mpr
  rw [← add_div]
  apply (div_eq_one_iff_eq hn).mpr
  linarith only [hcard]

theorem probPerm_exists_le_sum {α : Type*} {n : ℕ} (s : Finset α)
    (P : α → Equiv.Perm (Fin n) → Prop) :
    probPerm (fun σ ↦ ∃ i ∈ s, P i σ) ≤ ∑ i ∈ s, probPerm (P i) := by
  classical
  have hset : (univ.filter (fun σ : Equiv.Perm (Fin n) ↦ ∃ i ∈ s, P i σ)) =
      s.biUnion (fun i ↦ univ.filter (P i)) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
  have hcard : (s.biUnion (fun i ↦ univ.filter (P i))).card ≤
      ∑ i ∈ s, (univ.filter (P i)).card := card_biUnion_le
  have hcast : ((s.biUnion (fun i ↦ univ.filter (P i))).card : ℝ) ≤
      ∑ i ∈ s, ((univ.filter (P i)).card : ℝ) := by exact_mod_cast hcard
  simp only [probPerm_eq_count]
  rw [hset]
  calc
    _ ≤ (∑ i ∈ s, ((univ.filter (P i)).card : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
      div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
    _ = _ := sum_div _ _ _

theorem probPerm_forall_ge_one_sub_sum {α : Type*} {n : ℕ} (s : Finset α)
    (P : α → Equiv.Perm (Fin n) → Prop) :
    1 - (∑ i ∈ s, probPerm (fun σ ↦ ¬P i σ)) ≤
      probPerm (fun σ ↦ ∀ i ∈ s, P i σ) := by
  classical
  have hbad := probPerm_exists_le_sum s (fun i σ ↦ ¬P i σ)
  have hc := probPerm_not (fun σ ↦ ∀ i ∈ s, P i σ)
  simp only [not_forall, exists_prop] at hc
  linarith

end TCSShortlistPriceNearOptimal.LearnedPrices

open DynamicOnlineLP.DLA

namespace TCSShortlistPriceNearOptimal.LearnedPrices

theorem log_pattern_bound {m n E N : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n)
    (hN : Real.log (N : ℝ) ≤ ((m : ℝ) + 2) * (Real.log (n : ℝ) + 1)) :
    Real.log (N : ℝ) ≤ 6 * (m : ℝ) * Real.log ((n : ℝ) / eps E) := by
  have hL := log_population_accuracy_ge_one hn hE hdvd
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have heps := eps_pos E
  have heps1 : eps E ≤ 1 := (eps_le_half hE).trans (by norm_num)
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) / eps E) := by
    apply Real.log_le_log (by exact_mod_cast hn)
    apply (le_div_iff₀ heps).mpr
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) heps1
  have hdim : (m : ℝ) + 2 ≤ 3 * m := by linarith
  have hlog : Real.log (n : ℝ) + 1 ≤ 2 * Real.log ((n : ℝ) / eps E) := by linarith
  calc
    Real.log (N : ℝ) ≤ ((m : ℝ) + 2) * (Real.log (n : ℝ) + 1) := hN
    _ ≤ (3 * (m : ℝ)) * (2 * Real.log ((n : ℝ) / eps E)) :=
      mul_le_mul hdim hlog (by linarith [Real.log_natCast_nonneg n]) (by positivity)
    _ = _ := by ring

theorem union_factor_bound {m n E N : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n) (hNpos : 0 < N)
    (hN : Real.log (N : ℝ) ≤ ((m : ℝ) + 2) * (Real.log (n : ℝ) + 1)) :
    4 * (m : ℝ) * E * N * Real.exp (-16 * (m : ℝ) * Real.log ((n : ℝ) / eps E)) ≤
      eps E := by
  let L := Real.log ((n : ℝ) / eps E)
  have hL : 1 ≤ L := log_population_accuracy_ge_one hn hE hdvd
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hEp : (0 : ℝ) < E := by exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 1) hE
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have heps := eps_pos E
  have hlogn0 := Real.log_natCast_nonneg n
  have hlogn : Real.log (n : ℝ) ≤ L := by
    apply Real.log_le_log hnp
    apply (le_div_iff₀ heps).mpr
    exact mul_le_of_le_one_right hnp.le ((eps_le_half hE).trans (by norm_num))
  have hlogE : Real.log (E : ℝ) ≤ L :=
    (Real.log_le_log hEp (by exact_mod_cast exponent_le_population hn hdvd)).trans hlogn
  have hlog4 : Real.log (4 : ℝ) ≤ L := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ heps).mpr
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast two_le_population hn hE hdvd
    linarith [eps_le_half hE]
  have hlogm := Real.log_le_self (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hmL : (m : ℝ) ≤ (m : ℝ) * L := le_mul_of_one_le_right hmp.le hL
  have hLm : L ≤ (m : ℝ) * L := le_mul_of_one_le_left (by linarith : 0 ≤ L) hmreal
  have hlogN : Real.log (N : ℝ) ≤ 6 * (m : ℝ) * L := log_pattern_bound hm hn hE hdvd hN
  have hlogK : Real.log (4 * (m : ℝ) * E * N) ≤ 9 * (m : ℝ) * L := by
    rw [Real.log_mul (by positivity) hNp.ne', Real.log_mul (by positivity) hEp.ne',
      Real.log_mul (by norm_num) hmp.ne']
    linarith
  have hnegL : -L ≤ Real.log (eps E) := by
    dsimp [L]
    rw [Real.log_div hnp.ne' heps.ne']
    linarith
  calc
    _ = Real.exp (Real.log (4 * (m : ℝ) * E * N) - 16 * (m : ℝ) * L) := by
      change 4 * (m : ℝ) * E * N * Real.exp (-16 * (m : ℝ) * L) = _
      rw [Real.exp_sub, Real.exp_log (by positivity)]
      rw [show -16 * (m : ℝ) * L = -(16 * (m : ℝ) * L) by ring,
        Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-7 * (m : ℝ) * L) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ Real.exp (Real.log (eps E)) := Real.exp_le_exp.mpr (by linarith only [hLm, hL, hnegL])
    _ = eps E := Real.exp_log heps

theorem capacity_tail_factor_bound {m n E : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n) (b : ℝ)
    (hb : 512 * (m : ℝ) * Real.log ((n : ℝ) / eps E) / (eps E) ^ 2 ≤ b) :
    Real.exp (-((eps E) ^ 2 * b) / 32) ≤
      Real.exp (-16 * (m : ℝ) * Real.log ((n : ℝ) / eps E)) := by
  have heps := eps_pos E
  have hmul := (div_le_iff₀ (sq_pos_of_pos heps)).mp hb
  apply Real.exp_le_exp.mpr
  nlinarith

theorem capacity_nonneg {m n E : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) (b : ℝ)
    (hb : 512 * (m : ℝ) * Real.log ((n : ℝ) / eps E) / (eps E) ^ 2 ≤ b) : 0 ≤ b := by
  have hL := log_population_accuracy_ge_one hn hE hdvd
  exact (by positivity : 0 ≤ 512 * (m : ℝ) * Real.log ((n : ℝ) / eps E) / (eps E) ^ 2).trans hb

end TCSShortlistPriceNearOptimal.LearnedPrices

open Finset DynamicOnlineLP.DLA TCSShortlistPriceNearOptimal.Bernstein TCSShortlistPriceNearOptimal.LearnedPrices

private theorem nonnegative_packing_optimum {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i) : 0 ≤ optValue S π a d := by
  obtain ⟨x, hx, _, _, hxeq⟩ := TrainingPrices.feasibleOptimumExists S π a d hd
  have hz : IsFeasible S a d (fun _ ↦ 0) := by
    constructor
    · intro i
      simpa only [mul_zero, sum_const_zero] using hd i
    · intro j hj
      norm_num
  have hzero := hx.2 (fun _ ↦ 0) hz
  rw [← hxeq]
  simpa only [primalObj, mul_zero, sum_const_zero] using hzero

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n E : ℕ) (I : Instance m n) (rule : DualRule m n),
        1 ≤ m → 1 ≤ E → 0 < n → 2 ^ E ∣ n → I.GeneralPosition → IsValidDualRule rule →
        (∀ i : Fin m, C * (m : ℝ) * Real.log ((n : ℝ) / eps E) / eps E ^ 2 ≤ I.b i) →
        1 - eps E ≤ probPerm (fun σ : Equiv.Perm (Fin n) =>
          ∀ ℓ ∈ phases n E,
            (1 - 2 * slack n E ℓ - eps E) *
                I.partialOPT σ (2 * ℓ) (fun i => (2 * (ℓ : ℝ) / (n : ℝ)) * I.b i) ≤
              ∑ t ∈ firstTimes n (2 * ℓ),
                I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ)
                  (learnedPrice I rule E σ ℓ) t) := by
  classical
  refine ⟨512, by norm_num, ?_⟩
  intro m n E I rule hm hE hn hdvd hgp hvalid hcap
  obtain ⟨F, hF, hcontains, hlogF⟩ := finite_threshold_patterns m n hn I.a I.π
  let pop : (Fin n → Bool) → Fin m → Fin n → ℝ :=
    fun v i j ↦ if v j then I.a j i else 0
  let β : ℕ → Fin m → ℝ := fun ℓ i ↦ ((ℓ : ℝ) / n) * I.b i
  let Bad : (Fin n → Bool) × (ℕ × Fin m) → Equiv.Perm (Fin n) → Prop :=
    fun q σ ↦
      0 ≤ 1 - 2 * slack n E q.2.1 - eps E ∧
        (1 - slack n E q.2.1 - eps E) * β q.2.1 q.2.2 ≤
          (∑ k ∈ firstTimes n q.2.1, pop q.1 q.2.2 (σ k)) ∧
        (∑ k ∈ firstTimes n (2 * q.2.1), pop q.1 q.2.2 (σ k)) ≤
          2 * (1 - 2 * slack n E q.2.1 - eps E) * β q.2.1 q.2.2
  let J : Finset ((Fin n → Bool) × (ℕ × Fin m)) :=
    F.product ((phases n E).product univ)
  let g : ℝ := 4 * Real.exp (-16 * (m : ℝ) * Real.log ((n : ℝ) / eps E))
  have heps := TCSShortlistPriceNearOptimal.LearnedPrices.eps_pos E
  have hL := log_population_accuracy_ge_one hn hE hdvd
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbpos (i : Fin m) : 0 < I.b i := by
    apply lt_of_lt_of_le _ (hcap i)
    positivity
  have hβpos (ℓ : ℕ) (hℓ : ℓ ∈ phases n E) (i : Fin m) : 0 < β ℓ i :=
    mul_pos (phase_ratio_bounds hn hdvd hℓ).1 (hbpos i)
  have hloss (ℓ : ℕ) (hℓ : ℓ ∈ phases n E) (i : Fin m) :
      (m : ℝ) ≤ eps E * β ℓ i := by
    have hrow := (div_le_iff₀ (sq_pos_of_pos heps)).mp (hcap i)
    have hmL : (m : ℝ) ≤ (m : ℝ) * Real.log ((n : ℝ) / eps E) :=
      le_mul_of_one_le_right (Nat.cast_nonneg m) hL
    have hmL0 : 0 ≤ (m : ℝ) * Real.log ((n : ℝ) / eps E) := by positivity
    have hbase : (m : ℝ) ≤ (eps E) ^ 2 * I.b i := by
      nlinarith only [hrow, hmL, hmL0]
    have hratio := (phase_ratio_bounds hn hdvd hℓ).2
    have hmul := mul_le_mul_of_nonneg_left hratio
      (mul_nonneg heps.le (hbpos i).le)
    dsimp [β]
    nlinarith only [hbase, hmul]
  have hpop0 (v : Fin n → Bool) (i : Fin m) (j : Fin n) : 0 ≤ pop v i j :=
    (pattern_population_bounds I v i j).1
  have hpop1 (v : Fin n → Bool) (i : Fin m) (j : Fin n) : pop v i j ≤ 1 :=
    (pattern_population_bounds I v i j).2
  have hbad (q : (Fin n → Bool) × (ℕ × Fin m)) (hq : q ∈ J) :
      probPerm (Bad q) ≤ g := by
    have hℓ : q.2.1 ∈ phases n E := (mem_product.mp (mem_product.mp hq).2).1
    have htime := phase_time_bounds hn hdvd hℓ
    have hslack := phase_slack_bounds hn hE hdvd hℓ
    by_cases hρ : 0 ≤ 1 - 2 * slack n E q.2.1 - eps E
    · have h := bounded_blocks_nearoptimal_tail hn (by omega : 1 ≤ q.2.1) htime.2.1
        (pop q.1 q.2.2) (hpop0 q.1 q.2.2) (hpop1 q.1 q.2.2)
        (β q.2.1 q.2.2) (slack n E q.2.1) (eps E)
        (hβpos _ hℓ _) hslack.1 hslack.2 heps.le hρ
      have htail : probPerm (Bad q) ≤ 4 * Real.exp
          (-(slack n E q.2.1 ^ 2 * β q.2.1 q.2.2 / 32)) := by
        apply le_trans ?_ h
        apply TCSShortlistPriceNearOptimal.Bernstein.probPerm_mono
        intro σ hσ
        exact hσ.2
      apply htail.trans
      dsimp [g]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
      rw [phase_budget_identity hn hdvd hℓ]
      simpa only [neg_div] using
        capacity_tail_factor_bound hm hn hE hdvd (I.b q.2.2) (hcap q.2.2)
    · have hzero : probPerm (Bad q) = 0 := by
        unfold probPerm
        simp only [Bad, hρ, false_and, filter_false, card_empty, Nat.cast_zero, zero_div]
      rw [hzero]
      positivity
  have hJcard : (J.card : ℝ) ≤ (F.card : ℝ) * E * m := by
    have hc : ((phases n E).card : ℝ) ≤ E := by exact_mod_cast phase_card_le n E
    dsimp [J]
    simp only [card_product, card_univ, Fintype.card_fin, Nat.cast_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg m)) (Nat.cast_nonneg F.card)
  have htotal : (∑ q ∈ J, probPerm (Bad q)) ≤ eps E := by
    calc
      _ ≤ ∑ _q ∈ J, g := sum_le_sum hbad
      _ = (J.card : ℝ) * g := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ ((F.card : ℝ) * E * m) * g := mul_le_mul_of_nonneg_right hJcard (by positivity)
      _ = 4 * (m : ℝ) * E * F.card *
          Real.exp (-16 * (m : ℝ) * Real.log ((n : ℝ) / eps E)) := by dsimp [g]; ring
      _ ≤ eps E := union_factor_bound hm hn hE hdvd hF.card_pos hlogF
  have hgood := probPerm_forall_ge_one_sub_sum J (fun q σ ↦ ¬Bad q σ)
  simp only [not_not] at hgood
  apply (sub_le_sub_left htotal 1).trans
  apply hgood.trans
  apply TCSShortlistPriceNearOptimal.Bernstein.probPerm_mono
  intro σ hσ ℓ hℓ
  let p : Fin m → ℝ := learnedPrice I rule E σ ℓ
  let ρ : ℝ := 1 - 2 * slack n E ℓ - eps E
  let d : Fin m → ℝ := fun i ↦ (2 * (ℓ : ℝ) / (n : ℝ)) * I.b i
  have htime := phase_time_bounds hn hdvd hℓ
  have hslack := phase_slack_bounds hn hE hdvd hℓ
  have hd (i : Fin m) : 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hslack.2)
      (phase_ratio_bounds hn hdvd hℓ).1.le) (hbpos i).le
  have hd2 (i : Fin m) : 0 ≤ d i := by
    dsimp [d]
    exact mul_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg n)) (hbpos i).le
  have hp : ∀ i, 0 ≤ p i :=
    learnedPrice_nonneg I rule E σ ℓ hvalid (by omega) hd
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; linarith only [hslack.1, heps]
  change ρ * optValue (firstTimes n (2 * ℓ)) (I.arrPi σ) (I.arrA σ) d ≤
    primalObj (firstTimes n (2 * ℓ)) (I.arrPi σ) (threshold (I.arrPi σ) (I.arrA σ) p)
  by_cases hρ : 0 ≤ ρ
  · let v : Fin n → Bool := fun j ↦ decide ((∑ i, p i * I.a j i) < I.π j)
    have hv : v ∈ F := hcontains p
    have hcoverage (i : Fin m) (hi : 0 < p i) :
        ρ * d i ≤ ∑ t ∈ firstTimes n (2 * ℓ),
          I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ) p t := by
      have htraining := (learnedPrice_trainingBounds I rule E σ ℓ hvalid
        (by omega : ℓ ≤ n) hd hgp i).2 hi
      have hpop (k : Fin n) : pop v i (σ k) =
          I.arrA σ k i * threshold (I.arrPi σ) (I.arrA σ) p k :=
        threshold_population_eq I σ p i k
      have htrain : (1 - slack n E ℓ) * β ℓ i - (m : ℝ) ≤
          ∑ k ∈ firstTimes n ℓ, pop v i (σ k) := by
        simpa only [hpop, mul_assoc] using htraining
      have htrain' : (1 - slack n E ℓ - eps E) * β ℓ i ≤
          ∑ k ∈ firstTimes n ℓ, pop v i (σ k) := by
        nlinarith only [htrain, hloss ℓ hℓ i]
      have hnot := hσ (v, (ℓ, i))
        (mem_product.mpr ⟨hv, mem_product.mpr ⟨hℓ, mem_univ i⟩⟩)
      have hTnot : ¬(∑ k ∈ firstTimes n (2 * ℓ), pop v i (σ k)) ≤
          2 * ρ * β ℓ i := by
        intro hT
        exact hnot ⟨hρ, htrain', hT⟩
      calc
        ρ * d i = 2 * ρ * β ℓ i := by dsimp [d, β]; ring
        _ ≤ ∑ k ∈ firstTimes n (2 * ℓ), pop v i (σ k) := (lt_of_not_ge hTnot).le
        _ = _ := sum_congr rfl (fun k _ ↦ hpop k)
    exact TrainingPrices.scaledOptimum_le_thresholdRevenue (firstTimes n (2 * ℓ))
      (I.arrPi σ) (I.arrA σ) d p ρ hd2 hp ⟨hρ, hρ1⟩ hcoverage
  · have hopt0 := nonnegative_packing_optimum (firstTimes n (2 * ℓ))
      (I.arrPi σ) (I.arrA σ) d hd2
    have hrev0 : 0 ≤ primalObj (firstTimes n (2 * ℓ)) (I.arrPi σ)
        (threshold (I.arrPi σ) (I.arrA σ) p) := by
      apply sum_nonneg
      intro t ht
      apply mul_nonneg (I.π_nonneg (σ t))
      unfold threshold
      split_ifs <;> norm_num
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hρ)) hopt0).trans hrev0
