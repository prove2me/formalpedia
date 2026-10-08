-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.proposition_5_1_c
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:07:48.677523+00:00
-- url     : https://prove2.me/submissions/63e04260-6aa6-4a08-a2a6-532445f6583e

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

open BeckTeboulleMD.EMDA in
lemma p135_entropy_hasFDerivAt {n : ℕ} (y : Fin n → ℝ) (hy : ∀ j, y j ≠ 0) :
    HasFDerivAt (entropy (n := n))
      (∑ j : Fin n, (Real.log (y j) + 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) y := by
  have hfun : (entropy (n := n)) = fun x : Fin n → ℝ => ∑ j : Fin n, x j * Real.log (x j) := by
    funext x; rfl
  rw [hfun]
  apply HasFDerivAt.fun_sum (A := fun j (x : Fin n → ℝ) => x j * Real.log (x j))
  intro j _
  have h1 := (Real.hasDerivAt_mul_log (hy j)).hasFDerivAt
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt (x := y)
  have h3 := h1.comp y h2
  convert h3 using 1
  · funext v; rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring

open BeckTeboulleMD.EMDA in
theorem solution {n : ℕ} :
    ∀ xstar ∈ stdSimplex ℝ (Fin n),
      bregman (entropy (n := n)) xstar (fun _ => 1 / (n : ℝ)) ≤ Real.log n := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hx1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hy : ∀ j : Fin n, (fun _ => 1 / (n : ℝ)) j ≠ 0 := by
    intro j; simp [hn]
  have hD := (p135_entropy_hasFDerivAt (fun _ => 1 / (n : ℝ)) hy).fderiv
  unfold bregman
  rw [hD]
  have hlin : (∑ j : Fin n, (Real.log ((fun _ => 1 / (n : ℝ)) j) + 1) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)
      (x - fun _ => 1 / (n : ℝ)) = 0 := by
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    simp only [ContinuousLinearMap.proj_apply, Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hx1]
    simp [Finset.card_univ, Fintype.card_fin]
    field_simp
    simp
  rw [hlin]
  have hEy : entropy (n := n) (fun _ => 1 / (n : ℝ)) = - Real.log n := by
    unfold entropy
    simp [Finset.card_univ, Fintype.card_fin, Real.log_inv]
    field_simp
  have hEx : entropy (n := n) x ≤ 0 := by
    unfold entropy
    apply Finset.sum_nonpos
    intro j _
    have hle : x j ≤ 1 := by
      rw [← hx1]
      exact Finset.single_le_sum (fun i _ => hx0 i) (Finset.mem_univ j)
    exact mul_nonpos_of_nonneg_of_nonpos (hx0 j) (Real.log_nonpos (hx0 j) hle)
  rw [hEy]
  linarith
