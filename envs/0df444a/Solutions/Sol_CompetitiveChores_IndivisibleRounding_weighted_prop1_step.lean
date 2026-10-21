-- Prove2me | solution 1 for CompetitiveChores.IndivisibleRounding.weighted_prop1_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:57:25.55832+00:00
-- url     : https://prove2.me/submissions/97801ad2-a2a7-4de6-b15d-807db17bb302

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
    (hσ : CompetitiveChores.RichFamily.IsCompetitiveWith v b' (indicator σ) p) (hp : ∑ j, p j = -∑ i, β i) (i : Fin n)
    (j : Fin m) (hj : j ∈ bundle σ i)
    (hi : -β i ≤ setPrice p ((bundle σ i).erase j)) :
    setUtility v i Finset.univ / ∑ i', β i' ≤ setUtility v i ((bundle σ i).erase j) / β i := by
  have hB : 0 < ∑ i', β i' := Finset.sum_pos (fun k _ => hβ k) ⟨i, Finset.mem_univ _⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = ∑ i', β i' := ⟨_, rfl⟩
  rw [← hBdef] at hB hp ⊢
  have hβi := hβ i
  have hsp : setPrice p Finset.univ = -B := hp
  have hcore := cci_core v σ b' p hσ i j hj Finset.univ (β i / B) (by positivity)
    (by
      rw [hsp]
      have : β i / B * -B = -β i := by field_simp
      linarith)
  have h1 : β i / B * setUtility v i Finset.univ ≤ setUtility v i ((bundle σ i).erase j) := by
    linarith
  rw [div_le_div_iff₀ hB hβi]
  have : β i / B * setUtility v i Finset.univ * B = β i * setUtility v i Finset.univ := by
    field_simp
  nlinarith
