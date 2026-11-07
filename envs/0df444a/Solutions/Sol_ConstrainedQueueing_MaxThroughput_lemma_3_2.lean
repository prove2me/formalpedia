-- Prove2me | solution 1 for ConstrainedQueueing.MaxThroughput.lemma_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:03:44.447292+00:00
-- url     : https://prove2.me/submissions/246dc105-d350-4797-ad2a-b27e6101ca78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model
import Theorems.Thm_ConstrainedQueueing_MaxThroughput_theorem_3_1
import Theorems.Thm_ConstrainedQueueing_MaxThroughput_drift_A6_A7

open scoped ENNReal

namespace CQLem32Aux

/-- Product formula for an infinite sum over `Fin n → ℕ`. -/
theorem tsum_prod_fin : ∀ (n : ℕ) (f : Fin n → ℕ → ℝ≥0∞),
    ∑' A : Fin n → ℕ, ∏ i, f i (A i) = ∏ i, ∑' k, f i k
  | 0, f => by
    simp
  | n + 1, f => by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq]
    simp only [Fin.prod_univ_succ]
    rw [ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left]
    rw [tsum_prod_fin n (fun i => f i.succ), ENNReal.tsum_mul_right]

/-- Product formula for an infinite sum over `ι → ℕ`, `ι` a fintype. -/
theorem tsum_prod_fintype {ι : Type*} [Fintype ι] (f : ι → ℕ → ℝ≥0∞) :
    ∑' A : ι → ℕ, ∏ i, f i (A i) = ∏ i, ∑' k, f i k := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h1 := tsum_prod_fin (Fintype.card ι) (fun i => f (e.symm i))
  let E : (Fin (Fintype.card ι) → ℕ) ≃ (ι → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
  rw [← E.tsum_eq]
  have h2 : ∀ B : Fin (Fintype.card ι) → ℕ, ∏ i, f i (E B i) = ∏ i, f (e.symm i) (B i) := by
    intro B
    rw [← e.symm.prod_comp]
    simp [E, Equiv.arrowCongr_apply]
  simp_rw [h2]
  rw [h1, ← e.symm.prod_comp]

end CQLem32Aux

open ConstrainedQueueing.MaxThroughput in
theorem solution {L N J : ℕ} (net : ConstrainedQueueing.MaxThroughput.Network L N J)
    (hC1 : ConstrainedQueueing.MaxThroughput.C1 net)
    (hempty : (∅ : Finset (Fin N)) ∈ net.S) (hsingle : ∀ i : Fin N, ({i} : Finset (Fin N)) ∈ net.S)
    (hm : ∀ i, 0 < net.m i ∧ net.m i ≤ 1) (hC2 : ConstrainedQueueing.MaxThroughput.C2 net)
    (g : (QIdx net → ℕ) → MultiAct N J) (hg : IsPi0Rule net g) :
    Cprime net ⊆ stabRegion net g := by
  classical
  intro a ha
  refine ⟨ha.1, ?_⟩
  intro α hα hmean
  subst hmean
  -- the transition matrix is stochastic
  have hS : ∑ M : Fin N → Bool, serviceProb net M = 1 := by
    unfold serviceProb
    have := (Finset.prod_univ_sum (fun _ : Fin N => (Finset.univ : Finset Bool))
      (fun i (b : Bool) => if b then ENNReal.ofReal (net.m i)
        else ENNReal.ofReal (1 - net.m i))).symm
    rw [Fintype.piFinset_univ] at this
    rw [this]
    apply Finset.prod_eq_one
    intro i _
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [← ENNReal.ofReal_add (hm i).1.le (by linarith [(hm i).2])]
    simp
  have hA : ∑' A : QIdx net → ℕ, arrivalProb α A = 1 := by
    unfold arrivalProb
    rw [CQLem32Aux.tsum_prod_fintype (fun p k => α p k)]
    simp
  have hstoch : IsStochastic (transProb net g α) := by
    intro x
    unfold transProb
    rw [ENNReal.tsum_comm]
    have : ∀ A : QIdx net → ℕ, ∑' y : QIdx net → ℕ, ∑ M : Fin N → Bool,
        arrivalProb α A * serviceProb net M * (if nextState net g x A M = y then 1 else 0)
        = arrivalProb α A := by
      intro A
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      simp only [mul_ite, mul_one, mul_zero]
      have hite : ∀ (c : ℝ≥0∞) (z : QIdx net → ℕ),
          ∑' y : QIdx net → ℕ, (if z = y then c else 0) = c := by
        intro c z
        have := tsum_ite_eq z (fun _ => c)
        rw [← this]
        congr 1
        funext y
        by_cases h : z = y
        · subst h; simp
        · rw [if_neg h, if_neg (Ne.symm h)]
      simp only [hite]
      rw [← Finset.mul_sum, hS, mul_one]
    simp_rw [this]
    exact hA
  -- the drift conditions
  obtain ⟨b, hb, hsum, hdrift⟩ :=
    drift_A6_A7 net hC1 hempty hsingle hm hC2 g hg α hα ha 1 one_pos
  let V : (QIdx net → ℕ) → ℝ := fun x => ∑ p, ((x p : ℝ)) ^ 2
  have hfin : {x : QIdx net → ℕ | V x < b}.Finite := by
    apply (Set.Finite.pi (t := fun _ : QIdx net => Set.Iic ⌈b⌉₊)
      (fun _ => Set.finite_Iic _)).subset
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, forall_const]
    intro p
    have h1 : ((x p : ℝ)) ^ 2 ≤ V x :=
      Finset.single_le_sum (f := fun p => ((x p : ℝ)) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ p)
    have h2 : (x p : ℝ) ≤ ((x p : ℝ)) ^ 2 := by
      rcases Nat.eq_zero_or_pos (x p) with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ x p := by exact_mod_cast h
        nlinarith
    have h3 : (x p : ℝ) < b := by
      have : V x < b := hx
      linarith
    have h4 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    exact_mod_cast (show (x p : ℝ) ≤ ⌈b⌉₊ by linarith)
  have hcount : Countable (QIdx net → ℕ) := inferInstance
  refine theorem_3_1 (transProb net g α) hstoch V ⟨0, ?_⟩ 1 one_pos hfin.toFinset ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · intro y hy
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hy
    exact ⟨hsum y, (hdrift y hy).le⟩
  · intro y _
    exact hsum y
