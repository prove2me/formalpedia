-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.eda_is_sanp_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:31:03.27245+00:00
-- url     : https://prove2.me/submissions/3c3b3014-8c69-4783-9860-6466c14a7882

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
set_option autoImplicit false

open BeckTeboulleMD.EMDA

lemma zzb_hasFDeriv_entropy {n : ℕ} (y : Fin n → ℝ) (hy : ∀ j, 0 < y j) :
    HasFDerivAt (fun x : Fin n → ℝ => entropy (n := n) x)
      (∑ j : Fin n, (Real.log (y j) + 1) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
  unfold entropy
  apply HasFDerivAt.fun_sum
  intro j _
  have h1 : HasDerivAt (fun r : ℝ => r * Real.log r) (Real.log (y j) + 1) (y j) := by
    have := (hasDerivAt_id (y j)).mul (Real.hasDerivAt_log (hy j).ne')
    refine this.congr_deriv ?_
    simp [(hy j).ne']
  have h2 := HasDerivAt.comp_hasFDerivAt (f := fun x : Fin n → ℝ => x j) y h1 (hasFDerivAt_apply (𝕜 := ℝ) j y)
  exact h2

lemma zzb_bregman {n : ℕ} (x y : Fin n → ℝ) (hy : ∀ j, 0 < y j)
    (hx : ∑ j, x j = 1) (hy1 : ∑ j, y j = 1) :
    bregman (entropy (n := n)) x y = ∑ j, x j * (Real.log (x j) - Real.log (y j)) := by
  unfold bregman
  rw [(zzb_hasFDeriv_entropy y hy).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    Pi.sub_apply, smul_eq_mul]
  unfold entropy
  have e1 : ∑ j, (Real.log (y j) + 1) * (x j - y j) = ∑ j, x j * Real.log (y j) + 1 - ∑ j, y j * Real.log (y j) - 1 := by
    have : ∀ j, (Real.log (y j) + 1) * (x j - y j) = x j * Real.log (y j) + x j - y j * Real.log (y j) - y j := by
      intro j; ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, hx, hy1]
  have e2 : ∑ j, x j * (Real.log (x j) - Real.log (y j)) = ∑ j, x j * Real.log (x j) - ∑ j, x j * Real.log (y j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e1, e2]; ring

lemma zzb_gibbs {n : ℕ} (u w : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j) (hw : ∀ j, 0 < w j)
    (hu1 : ∑ j, u j = 1) (hw1 : ∑ j, w j = 1) :
    0 ≤ ∑ j, u j * (Real.log (u j) - Real.log (w j)) := by
  have key : ∀ j, u j * (Real.log (w j) - Real.log (u j)) ≤ w j - u j := by
    intro j
    rcases (hu j).eq_or_lt with h | h
    · rw [← h]; simpa using (hw j).le
    · have := Real.log_le_sub_one_of_pos (div_pos (hw j) h)
      rw [Real.log_div (hw j).ne' h.ne'] at this
      have h3 := mul_le_mul_of_nonneg_left this h.le
      calc u j * (Real.log (w j) - Real.log (u j)) ≤ u j * (w j / u j - 1) := h3
        _ = w j - u j := by field_simp
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
  rw [Finset.sum_sub_distrib, hw1, hu1] at this
  have e : ∑ j, u j * (Real.log (u j) - Real.log (w j)) = -∑ j, u j * (Real.log (w j) - Real.log (u j)) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [e]; linarith

theorem solution {n : ℕ} (y : Fin n → ℝ) (hy : y ∈ relIntSimplex n)
    (z : Fin n → ℝ) (t : ℝ) (ht : 0 < t) :
    (fun j => y j * Real.exp (-(t * z j)) / ∑ i, y i * Real.exp (-(t * z i))) ∈ relIntSimplex n ∧
    ∀ u ∈ stdSimplex ℝ (Fin n),
      ∑ j, (y j * Real.exp (-(t * z j)) / ∑ i, y i * Real.exp (-(t * z i))) * z j
          + (1 / t) * bregman (entropy (n := n))
              (fun j => y j * Real.exp (-(t * z j)) / ∑ i, y i * Real.exp (-(t * z i))) y
        ≤ ∑ j, u j * z j + (1 / t) * bregman (entropy (n := n)) u y := by
  obtain ⟨hy0, hy1⟩ := hy
  set Z : ℝ := ∑ i, y i * Real.exp (-(t * z i)) with hZ
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hy1
  have hZpos : 0 < Z := by
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hy0 i) (Real.exp_pos _)) Finset.univ_nonempty
  set w : Fin n → ℝ := fun j => y j * Real.exp (-(t * z j)) / Z with hwdef
  have hw0 : ∀ j, 0 < w j := fun j => div_pos (mul_pos (hy0 j) (Real.exp_pos _)) hZpos
  have hw1 : ∑ j, w j = 1 := by
    simp only [hwdef, ← Finset.sum_div]
    exact div_self hZpos.ne'
  refine ⟨⟨hw0, hw1⟩, ?_⟩
  intro u hu
  obtain ⟨hu0, hu1⟩ := hu
  have hlogw : ∀ j, Real.log (w j) = Real.log (y j) - t * z j - Real.log Z := by
    intro j
    simp only [hwdef]
    rw [Real.log_div (mul_pos (hy0 j) (Real.exp_pos _)).ne' hZpos.ne', Real.log_mul (hy0 j).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  show ∑ j, w j * z j + (1 / t) * bregman (entropy (n := n)) w y ≤ ∑ j, u j * z j + (1 / t) * bregman (entropy (n := n)) u y
  rw [zzb_bregman w y hy0 hw1 hy1, zzb_bregman u y hy0 hu1 hy1]
  have hg := zzb_gibbs u w hu0 hw0 hu1 hw1
  -- value at w
  have eW : ∑ j, w j * z j + (1 / t) * ∑ j, w j * (Real.log (w j) - Real.log (y j)) = -(1 / t) * Real.log Z := by
    have : ∀ j, w j * z j + (1 / t) * (w j * (Real.log (w j) - Real.log (y j))) = w j * (-(1 / t) * Real.log Z) := by
      intro j; rw [hlogw j]; field_simp; ring
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, hw1, one_mul]
  -- value at u
  have eU : ∑ j, u j * z j + (1 / t) * ∑ j, u j * (Real.log (u j) - Real.log (y j))
      = (1 / t) * ∑ j, u j * (Real.log (u j) - Real.log (w j)) - (1 / t) * Real.log Z := by
    have : ∀ j, u j * z j + (1 / t) * (u j * (Real.log (u j) - Real.log (y j)))
        = (1 / t) * (u j * (Real.log (u j) - Real.log (w j))) - u j * ((1 / t) * Real.log Z) := by
      intro j; rw [hlogw j]; field_simp; ring
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun j _ => this j),
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hu1, one_mul]
  rw [eW, eU]
  have : 0 ≤ (1 / t) * ∑ j, u j * (Real.log (u j) - Real.log (w j)) := mul_nonneg (by positivity) hg
  linarith
