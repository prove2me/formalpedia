-- Prove2me | solution 1 for CompetitiveChores.IndivisibleRounding.weighted_ef11_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:59:13.010888+00:00
-- url     : https://prove2.me/submissions/18eb7528-8408-4e54-a047-9fd2d210c4bc

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Indivisible

set_option autoImplicit false
open CompetitiveChores.RichFamily CompetitiveChores.IndivisibleRounding

theorem cci_ind_price {n m : ℕ} (σ : Fin m → Fin n) (p : Fin m → ℝ) (i : Fin n) :
    bundlePrice p (indicator σ i) = setPrice p (bundle σ i) := by
  classical
  unfold bundlePrice setPrice indicator bundle
  simp [Finset.sum_filter]

theorem cci_ind_util {n m : ℕ} (σ : Fin m → Fin n) (v : Fin n → Fin m → ℝ) (i : Fin n) :
    bundleUtility v i (indicator σ i) = setUtility v i (bundle σ i) := by
  classical
  unfold bundleUtility setUtility indicator bundle
  simp [Finset.sum_filter]

theorem cci_test_price {m : ℕ} (p : Fin m → ℝ) (S : Finset (Fin m)) (j : Fin m) (t : ℝ) :
    bundlePrice p (fun c => t * (if c ∈ S then 1 else 0) + (if c = j then 1 else 0)) =
      t * setPrice p S + p j := by
  classical
  unfold bundlePrice setPrice
  simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem cci_test_util {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (S : Finset (Fin m)) (j : Fin m)
    (t : ℝ) :
    bundleUtility v i (fun c => t * (if c ∈ S then 1 else 0) + (if c = j then 1 else 0)) =
      t * setUtility v i S + v i j := by
  classical
  unfold bundleUtility setUtility
  simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- core: agent `i` cannot gain by swapping in `t·1_S + e_j` when it is affordable. -/
theorem cci_core {n m : ℕ} (v : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) (b' : Fin n → ℝ)
    (p : Fin m → ℝ)
    (hσ : IsCompetitiveWith v b' (indicator σ) p) (i : Fin n) (j : Fin m)
    (hj : j ∈ bundle σ i) (S : Finset (Fin m)) (t : ℝ) (ht : 0 ≤ t)
    (hS : t * setPrice p S ≤ setPrice p ((bundle σ i).erase j)) :
    t * setUtility v i S + v i j ≤ setUtility v i ((bundle σ i).erase j) + v i j := by
  classical
  obtain ⟨_, _, hi⟩ := hσ
  obtain ⟨hbud, hopt⟩ := hi i
  rw [cci_ind_price] at hbud
  have hsplit : ∀ f : Fin m → ℝ, ∑ c ∈ bundle σ i, f c = ∑ c ∈ (bundle σ i).erase j, f c + f j := by
    intro f
    rw [← Finset.sum_erase_add _ _ hj]
  have hP : setPrice p (bundle σ i) = setPrice p ((bundle σ i).erase j) + p j := hsplit p
  have hU : setUtility v i (bundle σ i) = setUtility v i ((bundle σ i).erase j) + v i j := hsplit (v i)
  have key := hopt (fun c => t * (if c ∈ S then 1 else 0) + (if c = j then 1 else 0))
    (fun c => by
      have : 0 ≤ (if c ∈ S then (1:ℝ) else 0) := by split_ifs <;> norm_num
      have : 0 ≤ (if c = j then (1:ℝ) else 0) := by split_ifs <;> norm_num
      positivity)
    (by rw [cci_test_price]; linarith)
  rw [cci_test_util, cci_ind_util, hU] at key
  exact key

theorem solution {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, v i j < 0)
    (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i) (σ : Fin m → Fin n) (b' : Fin n → ℝ) (p : Fin m → ℝ)
    (hσ : CompetitiveChores.RichFamily.IsCompetitiveWith v b' (indicator σ) p) (i i' : Fin n) (j j' : Fin m)
    (hj : j ∈ bundle σ i)
    (hi : -β i ≤ setPrice p ((bundle σ i).erase j))
    (hi' : setPrice p (insert j' (bundle σ i')) ≤ -β i') :
    setUtility v i (insert j' (bundle σ i')) / β i' ≤ setUtility v i ((bundle σ i).erase j) / β i := by
  have hβi := hβ i
  have hβi' := hβ i'
  have hcore := cci_core v σ b' p hσ i j hj (insert j' (bundle σ i')) (β i / β i') (by positivity)
    (by
      have h1 : β i / β i' * setPrice p (insert j' (bundle σ i')) ≤ β i / β i' * -β i' :=
        mul_le_mul_of_nonneg_left hi' (by positivity)
      have : β i / β i' * -β i' = -β i := by field_simp
      linarith)
  have h1 : β i / β i' * setUtility v i (insert j' (bundle σ i')) ≤ setUtility v i ((bundle σ i).erase j) := by
    linarith
  rw [div_le_div_iff₀ hβi' hβi]
  have : β i / β i' * setUtility v i (insert j' (bundle σ i')) * β i' = β i * setUtility v i (insert j' (bundle σ i')) := by
    field_simp
  nlinarith
