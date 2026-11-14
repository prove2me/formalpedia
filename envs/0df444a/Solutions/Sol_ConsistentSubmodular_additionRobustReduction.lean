-- Prove2me | solution 1 for ConsistentSubmodular.additionRobustReduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:40:00.558944+00:00
-- url     : https://prove2.me/submissions/0670fbf9-10c0-43f0-b314-cd53af158a5e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_Checkpoints
import Theorems.Thm_ConsistentSubmodular_Checkpoints_exists_subset_fraction
import Theorems.Thm_ConsistentSubmodular_Checkpoints_feasible_run
import Theorems.Thm_ConsistentSubmodular_Checkpoints_params_spec
import Theorems.Thm_ConsistentSubmodular_Checkpoints_expect_run_ge

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

namespace Law

variable {Ω : Type*} [Fintype Ω]

theorem expect_const (μ : Law Ω) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.sum_one, one_mul]

theorem expect_dirac [DecidableEq Ω] (ω₀ : Ω) (X : Ω → ℝ) :
    (dirac ω₀).expect X = X ω₀ := by
  simp [expect, dirac]

/-- Weights of a product law vanish unless every coordinate has positive weight. -/
theorem weight_pi_ne_zero {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (μ : ι → Law X) {x : ι → X} (hx : (pi μ).weight x ≠ 0) (i : ι) :
    (μ i).weight (x i) ≠ 0 := by
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

variable {Y : Type*} [Fintype Y]

theorem weight_prod_ne_zero (μ : Law Ω) (ν : Law Y) {p : Ω × Y}
    (hp : (μ.prod ν).weight p ≠ 0) : μ.weight p.1 ≠ 0 ∧ ν.weight p.2 ≠ 0 := by
  simp only [prod] at hp
  exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩

theorem expectation_trajectory (μ : Law Ω) {n : ℕ} (τ : Ω → Fin (n + 1) → Finset (Fin n))
    (g : Finset (Fin n) → ℝ) (t : Fin (n + 1)) :
    (μ.trajectory τ).expectation g t = μ.expect (fun ω => g (τ ω t)) := by
  classical
  unfold RandomTrajectory.expectation trajectory expect
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ τ (fun ω => μ.weight ω * g (τ ω t))]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.mp hω).2]

theorem feasible_trajectory (μ : Law Ω) {n : ℕ} (τ : Ω → Fin (n + 1) → Finset (Fin n))
    {k C : ℕ} (h : ∀ ω, μ.weight ω ≠ 0 → FeasibleTrajectory k C (τ ω)) :
    (μ.trajectory τ).Feasible k C := by
  classical
  intro S hS
  obtain ⟨ω, hω, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [← (Finset.mem_filter.mp hω).2]
  exact h ω hne

end Law

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem block_inter (ℓ i r : ℕ) (hr : r ≤ ℓ) :
    block n ℓ i ∩ arrivedPrefix n (i * ℓ + r) = future n (i * ℓ) r := by
  ext e
  simp only [block, future, arrivedPrefix, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  omega

variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem state_zero (i : ℕ) : state P A σ i 0 = oldCore n P.ℓ A i := by
  have hd : done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) 0 = 0 := by
    simp [done, elapsed]
  have hb : block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + 0) = ∅ := by
    rw [block_inter _ _ _ (Nat.zero_le _)]
    ext e
    simp [future]
  rw [state, hd, path_zero, hb, Finset.union_empty]

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

theorem consistency_le {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    (consistency γ : ℝ) ≤ 17 * (1 / γ) ^ 2 := by
  have hinv : 8 < 1 / γ := by rw [lt_one_div (by norm_num) hγ]; linarith
  have hsq : 64 < (1 / γ) ^ 2 := by nlinarith
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 16 / γ ^ 2 by positivity)
  have h16 : 16 / γ ^ 2 = 16 * (1 / γ) ^ 2 := by field_simp
  unfold consistency
  push_cast
  linarith

variable {n : ℕ} {α : ℝ}

theorem good_of_weight (hadm : AdmitsAdditionRobust α) (f : Objective n) (P : Params)
    (hh : 0 < P.h) {ω : Sample n P.h} (hω : (sampleLaw hadm f P hh).weight ω ≠ 0) :
    Good P (samplesOf ω.1) (choicesOf ω.2) := by
  have hA := (Law.weight_prod_ne_zero _ _ hω).1
  intro i
  by_cases hi : i < n + 1
  · have hw := Law.weight_pi_ne_zero _ hA ⟨i, hi⟩
    obtain ⟨hsub, hcard⟩ := (robustWeights_spec hadm f P.κ (i * P.ℓ)).2.2.1 _ hw
    simp only [samplesOf, choicesOf, dif_pos hi]
    exact ⟨(ω.2 ⟨i, hi⟩).isLt, hsub, hcard⟩
  · simp only [samplesOf, choicesOf, dif_neg hi]
    exact ⟨hh, Finset.empty_subset _, by simp⟩

theorem feasible_mono {n k C C' : ℕ} {S : Fin (n + 1) → Finset (Fin n)}
    (hS : FeasibleTrajectory k C S) (hC : C ≤ C') : FeasibleTrajectory k C' S :=
  ⟨hS.1, hS.2.1, fun t => (hS.2.2 t).trans hC⟩

theorem feasible_optimum (f : Objective n) (k : ℕ) :
    FeasibleTrajectory k (2 * k) (fun t : Fin (n + 1) => optimum f k t.val) := by
  obtain ⟨hsub0, -, -⟩ := optimalCore_spec f (arrivedPrefix n 0) ∅ k
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · apply Finset.subset_empty.mp
    intro e he
    have := hsub0 he
    simp [arrivedPrefix] at this
  · exact ⟨(optimalCore_spec _ _ _ _).1, (optimalCore_spec _ _ _ _).2.1⟩
  · unfold recourse
    have h1 := (optimalCore_spec f (arrivedPrefix n (t.val + 1)) ∅ k).2.1
    have h2 := (optimalCore_spec f (arrivedPrefix n t.val) ∅ k).2.1
    have h3 := Finset.card_union_le (optimum f k (t.val + 1) \ optimum f k t.val)
      (optimum f k t.val \ optimum f k (t.val + 1))
    have h4 := Finset.card_le_card (Finset.sdiff_subset (s := optimum f k (t.val + 1))
      (t := optimum f k t.val))
    have h5 := Finset.card_le_card (Finset.sdiff_subset (s := optimum f k t.val)
      (t := optimum f k (t.val + 1)))
    simp only [Fin.val_succ, Fin.val_castSucc]
    unfold optimum at *
    omega

theorem le_optimum (f : Objective n) {k t : ℕ} {A : Finset (Fin n)}
    (hA : A ⊆ arrivedPrefix n t) (hAk : A.card ≤ k) : f.value A ≤ f.value (optimum f k t) := by
  have h := (optimalCore_spec f (arrivedPrefix n t) ∅ k).2.2 A hA hAk
  simpa [optimum] using h

/-- **Lemma 1** (from clairvoyant addition robustness to consistency). An
`α`-addition-robust routine gives, for every `γ ∈ (0, 1/8)`, a randomized
clairvoyant algorithm that is `(⌈16 γ⁻²⌉ + 3)`-consistent, at most `17 γ⁻²`, and an
`(α - 3γ)`-approximation. -/
theorem additionRobustReduction : AdditionRobustReductionGoal := by
  refine ⟨17, fun γ hγ hγ8 => ⟨consistency γ, consistency_le hγ hγ8,
    fun α hα0 hα1 hadm n k f => ?_⟩⟩
  by_cases hk : 8 / γ ^ 2 ≤ (k : ℝ)
  · -- Algorithm 1
    obtain ⟨hP, hcons, hh, hκ⟩ := params_spec hγ hγ8 hk
    set P := params γ k
    let τ : Sample n P.h → Fin (n + 1) → Finset (Fin n) :=
      fun ω t => run P (samplesOf ω.1) (choicesOf ω.2) t.val
    refine ⟨(sampleLaw hadm f P hP.subblocks_pos).trajectory τ, ?_, fun t A hA hAk => ?_⟩
    · apply Law.feasible_trajectory
      intro ω hω
      exact feasible_mono (feasible_run hP (good_of_weight hadm f P hP.subblocks_pos hω)) hcons
    · rw [Law.expectation_trajectory]
      have hγ2 : 0 < γ ^ 2 := by positivity
      have hkpos : 0 < k := by
        have : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
        exact_mod_cast this
      have hfA := f.nonnegative A
      obtain ⟨u, rfl⟩ | ht0 : (∃ u : Fin n, t = u.succ) ∨ t = 0 := by
        rcases Fin.eq_zero_or_eq_succ t with h0 | ⟨u, hu⟩
        · exact Or.inr h0
        · exact Or.inl ⟨u, hu⟩
      · -- a time after an arrival
        have hκk : P.κ ≤ k := by have := hP.budget; omega
        obtain ⟨T, hTA, hTcard, hTval⟩ := exists_subset_fraction f hAk hκk hkpos
        have hT : T ⊆ arrivedPrefix n (u.val + 1) := hTA.trans (by simpa using hA)
        have hE := expect_run_ge hα0 hα1 hadm f hP u.val (by omega) hT hTcard
        show (α - 3 * γ) * f.value A ≤ (sampleLaw hadm f P hP.subblocks_pos).expect
          (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u.val + 1)))
        have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
        have hγ' : γ < 1 := by linarith
        have h1 : 1 - γ ≤ 1 - 1 / (P.h : ℝ) := by linarith
        have h1' : 0 ≤ 1 - γ := by linarith
        have h2' : 0 ≤ 1 - 2 * γ := by linarith
        have hfrac : (1 - γ) * (1 - 2 * γ) ≤ (1 - 1 / (P.h : ℝ)) * ((P.κ : ℝ) / k) :=
          mul_le_mul h1 hκ h2' (by linarith)
        have hfT := f.nonnegative T
        -- `(α - 3γ) f(A) ≤ (1 - 3γ) α f(A) ≤ (1 - 1/h) (κ/k) α f(A) ≤ (1 - 1/h) α f(T)`
        have hstep1 : (α - 3 * γ) * f.value A ≤ ((1 - γ) * (1 - 2 * γ)) * (α * f.value A) := by
          have : (α - 3 * γ) ≤ ((1 - γ) * (1 - 2 * γ)) * α := by nlinarith
          nlinarith
        have hstep2 : ((1 - γ) * (1 - 2 * γ)) * (α * f.value A) ≤
            ((1 - 1 / (P.h : ℝ)) * ((P.κ : ℝ) / k)) * (α * f.value A) :=
          mul_le_mul_of_nonneg_right hfrac (mul_nonneg hα0 hfA)
        have hstep3 : ((1 - 1 / (P.h : ℝ)) * ((P.κ : ℝ) / k)) * (α * f.value A) ≤
            (1 - 1 / (P.h : ℝ)) * (α * f.value T) := by
          have h3 : 0 ≤ (1 - 1 / (P.h : ℝ)) * α := mul_nonneg (by linarith) hα0
          have := mul_le_mul_of_nonneg_left hTval h3
          linarith
        linarith
      · -- time zero
        subst ht0
        have hA0 : A = ∅ := by
          apply Finset.subset_empty.mp
          intro e he
          have := hA he
          simp [arrivedPrefix] at this
        subst hA0
        have hrun (ω : Sample n P.h) : run P (samplesOf ω.1) (choicesOf ω.2) 0 = ∅ := by
          have := state_zero (P := P) (A := samplesOf ω.1) (σ := choicesOf ω.2) 0
          simp only [run, phase, pos, Nat.zero_sub, Nat.zero_div, zero_mul] at this ⊢
          rw [this]
          simp [oldCore]
        show (α - 3 * γ) * f.value ∅ ≤ (sampleLaw hadm f P hP.subblocks_pos).expect
          (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) 0))
        simp only [hrun, Law.expect_const]
        have h0 := f.nonnegative ∅
        nlinarith
  · -- small budgets: an exact optimum after every arrival
    have hk' : (k : ℝ) < 8 / γ ^ 2 := lt_of_not_ge hk
    have hrec : 2 * k ≤ consistency γ := by
      have hc := Nat.le_ceil (16 / γ ^ 2)
      have : ((2 * k : ℕ) : ℝ) ≤ ((consistency γ : ℕ) : ℝ) := by
        unfold consistency
        push_cast
        have : 16 / γ ^ 2 = 2 * (8 / γ ^ 2) := by ring
        linarith
      exact_mod_cast this
    refine ⟨(Law.dirac ()).trajectory (fun _ t => optimum f k t.val), ?_, fun t A hA hAk => ?_⟩
    · exact Law.feasible_trajectory _ _ fun _ _ => feasible_mono (feasible_optimum f k) hrec
    · rw [Law.expectation_trajectory, Law.expect_dirac]
      have hle := le_optimum f hA hAk
      have hfA := f.nonnegative A
      nlinarith

end ConsistentSubmodular.Checkpoints

end

end

section

open ConsistentSubmodular

theorem solution : AdditionRobustReductionGoal :=
  Checkpoints.additionRobustReduction

end
