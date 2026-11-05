-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:11:08.36852+00:00
-- url     : https://prove2.me/submissions/b94328a9-bf2e-41ed-9934-6f5cf708e984

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Estimator
import Theorems.Thm_DynAssortPers_Regret_lemma_2
import Theorems.Thm_DynAssortPers_Regret_lemma_5
import Theorems.Thm_WainwrightHDS_NucNorm_cone_constraint_nuclear
import Theorems.Thm_WainwrightHDS_NucNorm_exists_top_r_singular_subspaces
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_le_sqrt_two_r_frob_of_mem_Mbar
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_le
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_smul

open DynAssortPers.Regret MatrixCompletion

namespace DAPl6

lemma rank_le_min {m n : ℕ} (X : RealMatrix m n) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) ≤ min m n := by
  refine le_min ?_ ?_
  · have := Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin X))
    simpa [finrank_euclideanSpace_fin] using this
  · have := LinearMap.finrank_range_le (Matrix.toEuclideanLin X)
    simpa [finrank_euclideanSpace_fin] using this

lemma nuclear_eq_nuc {m n : ℕ} (X : RealMatrix m n) :
    nuclearNorm X = WainwrightHDS.NucNorm.nucNorm X := by
  unfold nuclearNorm WainwrightHDS.NucNorm.nucNorm WainwrightHDS.NucNorm.singVal
  refine Finsupp.sum_of_support_subset _ ?_ _ (fun _ _ => rfl)
  rw [LinearMap.support_singularValues]
  exact Finset.range_subset_range.2 (rank_le_min X)

lemma nuclear_nonneg {m n : ℕ} (X : RealMatrix m n) : 0 ≤ nuclearNorm X := by
  rw [nuclear_eq_nuc]
  exact Finset.sum_nonneg (fun i _ => LinearMap.singularValues_nonneg _ i)

lemma tail_nonneg {m n : ℕ} (X : RealMatrix m n) (r : ℕ) : 0 ≤ tailNuclear X r :=
  Finset.sum_nonneg (fun i _ => LinearMap.singularValues_nonneg _ i)

lemma tail_zero {m n : ℕ} (X : RealMatrix m n) : tailNuclear X 0 = nuclearNorm X := by
  rw [nuclear_eq_nuc]
  unfold tailNuclear WainwrightHDS.NucNorm.nucNorm WainwrightHDS.NucNorm.singVal
  rw [Finset.range_eq_Ico]

lemma nuclear_add_le {m n : ℕ} (X Y : RealMatrix m n) :
    nuclearNorm (X + Y) ≤ nuclearNorm X + nuclearNorm Y := by
  simp only [nuclear_eq_nuc]; exact WainwrightHDS.NucNorm.nucNorm_add_le X Y

lemma nuclear_neg {m n : ℕ} (X : RealMatrix m n) : nuclearNorm (-X) = nuclearNorm X := by
  have := WainwrightHDS.NucNorm.nucNorm_smul (-1 : ℝ) X
  simp only [neg_one_smul, abs_neg, abs_one, one_mul] at this
  simp only [nuclear_eq_nuc]; exact this

lemma nuclear_sub_le {m n : ℕ} (X Y : RealMatrix m n) :
    nuclearNorm (X - Y) ≤ nuclearNorm X + nuclearNorm Y := by
  have := nuclear_add_le X (-Y)
  rwa [← sub_eq_add_neg, nuclear_neg] at this

lemma lquad_nonneg {m n : ℕ} (O : List (Obs m n)) (Δ : RealMatrix m n) : 0 ≤ lquad O Δ := by
  unfold lquad
  refine mul_nonneg (by positivity) ?_
  induction O with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) ih

/-- convexity of the loss on the box, from Lemma 2. -/
lemma convex_loss {m n : ℕ} (O : List (Obs m n)) (α : ℝ) (Θs Δ : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘΔ : entrySupNorm (Θs + Δ) ≤ α / Real.sqrt ((m : ℝ) * n)) :
    loss O Θs + matrixInner (lossGrad O Θs) Δ ≤ loss O (Θs + Δ) := by
  have h := lemma_2 n O (fun o _ => by simpa using Finset.card_le_univ o.2.2) α Θs Δ hΘs hΘΔ
  have hq : 0 ≤ lquad O Δ := lquad_nonneg O Δ
  have hc : 0 ≤ (1 / 2) * (1 / Real.exp (4 * (2 * α / Real.sqrt ((m : ℝ) * n)))) *
      (1 / (4 * (n : ℝ))) := by positivity
  have := mul_nonneg hc hq
  unfold bregman at h
  linarith

theorem l6 {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (hlam : 0 < lam)
    (Θs Θh : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘh : IsEstimate O lam α Θh)
    (hgrad : MatrixCompletion.spectralNorm (lossGrad O Θs) ≤ lam / 2) (r : ℕ) :
    nuclearNorm (Θh - Θs) ≤
      16 * max (Real.sqrt (r : ℝ) * frobeniusNorm (Θh - Θs)) (tailNuclear Θs r) := by
  set Δ := Θh - Θs with hΔ
  set B := α / Real.sqrt ((m : ℝ) * n)
  set G := lossGrad O Θs
  have hmax0 : 0 ≤ max (Real.sqrt (r : ℝ) * frobeniusNorm Δ) (tailNuclear Θs r) :=
    (tail_nonneg Θs r).trans (le_max_right _ _)
  have htail_le : tailNuclear Θs r ≤ max (Real.sqrt (r : ℝ) * frobeniusNorm Δ) (tailNuclear Θs r) :=
    le_max_right _ _
  have hfrob_le : Real.sqrt (r : ℝ) * frobeniusNorm Δ ≤
      max (Real.sqrt (r : ℝ) * frobeniusNorm Δ) (tailNuclear Θs r) := le_max_left _ _
  rcases Nat.eq_zero_or_pos (min m n) with hmn | hmn
  · -- degenerate dimensions: the nuclear norm vanishes
    have : nuclearNorm Δ = 0 := by
      rw [nuclear_eq_nuc]; unfold WainwrightHDS.NucNorm.nucNorm; rw [hmn]; simp
    rw [this]; linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- r = 0
    subst hr
    have hconv := convex_loss O α Θs Δ hΘs (by rw [hΔ, add_sub_cancel]; exact hΘh.1)
    have h5 := (lemma_5 O lam α hlam Θs Θh hΘs hΘh).1
    unfold bregman at h5
    rw [hΔ, add_sub_cancel] at hconv
    rw [add_sub_cancel] at h5
    have hn := nuclear_nonneg Δ
    have h1 : MatrixCompletion.spectralNorm G * nuclearNorm Δ ≤ lam / 2 * nuclearNorm Δ :=
      mul_le_mul_of_nonneg_right hgrad hn
    have h2 := nuclear_sub_le Θh Θs
    rw [← hΔ] at hconv h5 h2
    rw [tail_zero] at htail_le ⊢
    have key : lam * nuclearNorm Δ ≤ lam * (4 * nuclearNorm Θs) := by nlinarith
    have := le_of_mul_le_mul_left key hlam
    linarith
  -- main case
  set r' := min r (min m n) with hr'
  have hr'1 : 1 ≤ r' := le_min hr hmn
  have hr'2 : r' ≤ min m n := min_le_right _ _
  obtain ⟨U, V, hU, hV, hperp, hmem, hfro⟩ :=
    WainwrightHDS.NucNorm.exists_top_r_singular_subspaces Θs r' hr'1 hr'2
  -- the loss extended off the box
  let L : RealMatrix m n → ℝ := fun Θ =>
    if entrySupNorm Θ ≤ B then loss O Θ else
      max (loss O Θs + matrixInner G (Θ - Θs)) (loss O Θh + lam * nuclearNorm Θh - lam * nuclearNorm Θ)
  have hLs : L Θs = loss O Θs := by simp only [L]; rw [if_pos hΘs]
  have hLh : L Θh = loss O Θh := by simp only [L]; rw [if_pos hΘh.1]
  have hG : ∀ D : RealMatrix m n, L Θs + WainwrightHDS.NucNorm.traceInner G D ≤ L (Θs + D) := by
    intro D
    rw [hLs]
    show loss O Θs + matrixInner G D ≤ L (Θs + D)
    by_cases hf : entrySupNorm (Θs + D) ≤ B
    · simp only [L, hf, if_true]
      exact convex_loss O α Θs D hΘs hf
    · simp only [L, hf, if_false]
      refine le_trans (le_of_eq ?_) (le_max_left _ _)
      rw [add_sub_cancel_left]
  have hmin : ∀ Θ : RealMatrix m n, L Θh + lam * WainwrightHDS.NucNorm.nucNorm Θh ≤
      L Θ + lam * WainwrightHDS.NucNorm.nucNorm Θ := by
    intro Θ
    rw [hLh, ← nuclear_eq_nuc, ← nuclear_eq_nuc]
    by_cases hf : entrySupNorm Θ ≤ B
    · simp only [L, hf, if_true]
      exact hΘh.2 Θ hf
    · simp only [L, hf, if_false]
      have := le_max_right (loss O Θs + matrixInner G (Θ - Θs))
        (loss O Θh + lam * nuclearNorm Θh - lam * nuclearNorm Θ)
      linarith
  have hcone := WainwrightHDS.NucNorm.cone_constraint_nuclear L Θs G hG lam hlam
    (by show 2 * MatrixCompletion.spectralNorm G ≤ lam; linarith) Θh hmin U V
  rw [← hΔ] at hcone
  simp only [← nuclear_eq_nuc] at hcone hperp
  -- split Δ
  have hsplit : Δ = WainwrightHDS.NucNorm.projMbar U V Δ + WainwrightHDS.NucNorm.projMbarPerp U V Δ := by
    unfold WainwrightHDS.NucNorm.projMbar; abel
  have htri := nuclear_add_le (WainwrightHDS.NucNorm.projMbar U V Δ)
    (WainwrightHDS.NucNorm.projMbarPerp U V Δ)
  rw [← hsplit] at htri
  have hsq := WainwrightHDS.NucNorm.nucNorm_le_sqrt_two_r_frob_of_mem_Mbar U V r' hU hV _ (hmem Δ)
  rw [← nuclear_eq_nuc] at hsq
  have hF : Real.sqrt (WainwrightHDS.NucNorm.frobSq (WainwrightHDS.NucNorm.projMbar U V Δ)) ≤
      frobeniusNorm Δ := Real.sqrt_le_sqrt (hfro Δ)
  -- tails agree
  have htail : tailNuclear Θs r' = tailNuclear Θs r := by
    rcases le_total r (min m n) with h | h
    · rw [hr', min_eq_left h]
    · rw [hr', min_eq_right h]
      unfold tailNuclear
      rw [Finset.Ico_eq_empty_of_le le_rfl, Finset.Ico_eq_empty_of_le h]
  have hperp' : nuclearNorm (WainwrightHDS.NucNorm.projMperp U V Θs) ≤ tailNuclear Θs r := by
    rw [← htail]; exact hperp
  have hsr : Real.sqrt (2 * (r' : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (r : ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast min_le_left _ _))
      (Real.sqrt_nonneg _)
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hfn : 0 ≤ frobeniusNorm Δ := Real.sqrt_nonneg _
  have hsrn : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hA : nuclearNorm (WainwrightHDS.NucNorm.projMbar U V Δ) ≤
      Real.sqrt 2 * (Real.sqrt (r : ℝ) * frobeniusNorm Δ) := by
    calc _ ≤ Real.sqrt (2 * (r' : ℝ)) *
          Real.sqrt (WainwrightHDS.NucNorm.frobSq (WainwrightHDS.NucNorm.projMbar U V Δ)) := hsq
      _ ≤ (Real.sqrt 2 * Real.sqrt (r : ℝ)) * frobeniusNorm Δ :=
          mul_le_mul hsr hF (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hX := mul_le_mul_of_nonneg_left hfrob_le (Real.sqrt_nonneg 2)
  have hY : Real.sqrt 2 * max (Real.sqrt (r : ℝ) * frobeniusNorm Δ) (tailNuclear Θs r) ≤
      3 / 2 * max (Real.sqrt (r : ℝ) * frobeniusNorm Δ) (tailNuclear Θs r) :=
    mul_le_mul_of_nonneg_right hs2 hmax0
  linarith

end DAPl6

theorem solution {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (hlam : 0 < lam)
    (Θs Θh : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘh : IsEstimate O lam α Θh)
    (hgrad : MatrixCompletion.spectralNorm (lossGrad O Θs) ≤ lam / 2) (r : ℕ) :
    nuclearNorm (Θh - Θs) ≤
      16 * max (Real.sqrt (r : ℝ) * frobeniusNorm (Θh - Θs)) (tailNuclear Θs r) :=
  DAPl6.l6 O lam α hlam Θs Θh hΘs hΘh hgrad r
