-- Prove2me | solution 1 for DQI.Semicircle.lemma_9_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:04:39.717182+00:00
-- url     : https://prove2.me/submissions/fa6e17fd-aeb8-4956-b9b2-15b1015f8ba2

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_lemma_9_3_A

open DQI.Semicircle

/-- AM-GM in the form `2 s ℓ √(X Y) ≤ s² X + ℓ² Y`. -/
lemma amgm (s l X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    2 * s * l * Real.sqrt (X * Y) ≤ s ^ 2 * X + l ^ 2 * Y := by
  rw [Real.sqrt_mul hX]
  have h := two_mul_le_add_sq (s * Real.sqrt X) (l * Real.sqrt Y)
  rw [mul_pow, mul_pow, Real.sq_sqrt hX, Real.sq_sqrt hY] at h
  linarith

end Aux_DQI_Semicircle_lemma_9_3_A

namespace Aux_DQI_Semicircle_lemma_9_3_A

open DQI.Semicircle in
theorem eq129 (m ℓ : ℕ) (dpar : ℝ) (hℓ : 1 ≤ ℓ) (hℓm : 2 * ℓ ≤ m)
    (hd : -((m : ℝ) - 2 * ℓ) / Real.sqrt (ℓ * ((m : ℝ) - ℓ)) ≤ dpar) :
    ∀ t ∈ spectrum ℝ (Atri m ℓ dpar),
      t ≤ 2 * Real.sqrt m + ℓ * dpar + 2 * Real.sqrt (ℓ * ((m : ℝ) - ℓ)) := by
  intro t ht
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (Atri m ℓ dpar)) t := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact ht
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  have hti : t ≤ Atri m ℓ dpar i i + ∑ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖ := by
    have := le_abs_self (t - Atri m ℓ dpar i i)
    linarith
  have hdiag : Atri m ℓ dpar i i = ((i : ℕ) : ℝ) * dpar := by
    simp [Atri]
  have hiℓ : (i : ℕ) ≤ ℓ := by have := i.isLt; omega
  -- the radius
  have hpt : ∀ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖ ≤
      (if (j : ℕ) = (i : ℕ) + 1 then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
      (if (i : ℕ) = (j : ℕ) + 1 then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hji' : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    simp only [Atri, if_neg hji']
    by_cases h1 : (j : ℕ) = (i : ℕ) + 1
    · rw [if_pos h1, if_pos h1, if_neg (show ¬ ((i : ℕ) = (j : ℕ) + 1) by omega),
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), add_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos h2, if_pos h2, zero_add, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        have hj' : ((j : ℕ) : ℝ) = ((i : ℕ) : ℝ) - 1 := by
          rw [h2]; push_cast; ring
        rw [hj']
        apply le_of_eq
        congr 1
        ring
      · rw [if_neg h2, if_neg h2]
        simp
  have hPsum : ∑ j : Fin (ℓ + 1),
      (if (j : ℕ) = (i : ℕ) + 1 then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) =
      if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0 := by
    by_cases h : (i : ℕ) + 1 ≤ ℓ
    · rw [if_pos h, Finset.sum_eq_single (⟨(i : ℕ) + 1, by omega⟩ : Fin (ℓ + 1))]
      · rw [if_pos]
        rfl
      · intro j _ hj
        rw [if_neg]
        intro hc
        exact hj (Fin.ext hc)
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hc
      have := j.isLt
      omega
  have hQsum : ∑ j : Fin (ℓ + 1),
      (if (i : ℕ) = (j : ℕ) + 1 then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) =
      if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0 := by
    by_cases h : 1 ≤ (i : ℕ)
    · rw [if_pos h, Finset.sum_eq_single (⟨(i : ℕ) - 1, by omega⟩ : Fin (ℓ + 1))]
      · rw [if_pos]
        show (i : ℕ) = (i : ℕ) - 1 + 1
        omega
      · intro j _ hj
        rw [if_neg]
        intro hc
        apply hj
        apply Fin.ext
        show (j : ℕ) = (i : ℕ) - 1
        omega
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hc
      omega
  have hR : ∑ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖ ≤
      (if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
      (if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) := by
    calc ∑ j ∈ Finset.univ.erase i, ‖Atri m ℓ dpar i j‖
        ≤ ∑ j ∈ Finset.univ.erase i,
          ((if (j : ℕ) = (i : ℕ) + 1 then
              Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
            (if (i : ℕ) = (j : ℕ) + 1 then
              Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0)) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ j : Fin (ℓ + 1),
          ((if (j : ℕ) = (i : ℕ) + 1 then
              Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) +
            (if (i : ℕ) = (j : ℕ) + 1 then
              Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro j _ _
          apply add_nonneg
          · split_ifs
            · exact Real.sqrt_nonneg _
            · exact le_rfl
          · split_ifs
            · exact Real.sqrt_nonneg _
            · exact le_rfl
      _ = _ := by rw [Finset.sum_add_distrib, hPsum, hQsum]
  -- real-number facts
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((i : ℕ) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxℓ : x ≤ ℓ := by rw [hx]; exact_mod_cast hiℓ
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓmR : 2 * (ℓ : ℝ) ≤ m := by exact_mod_cast hℓm
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (ℓ * ((m : ℝ) - ℓ)) := ⟨_, rfl⟩
  have hprod : 0 < (ℓ : ℝ) * ((m : ℝ) - ℓ) :=
    mul_pos (by linarith) (by linarith)
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hprod
  have hs2 : s ^ 2 = ℓ * ((m : ℝ) - ℓ) := by rw [hs]; exact Real.sq_sqrt hprod.le
  obtain ⟨M, hM⟩ : ∃ M, M = Real.sqrt (m : ℝ) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.sqrt_nonneg _
  have hM2 : M ^ 2 = m := by rw [hM]; exact Real.sq_sqrt (by positivity)
  rw [← hs, ← hM]
  rw [← hs] at hd
  have F3 : -((m : ℝ) - 2 * ℓ) ≤ dpar * s := (div_le_iff₀ hs0).mp hd
  have hsM : M ≤ 2 * s := by
    have h1 : M ^ 2 ≤ 4 * s ^ 2 := by
      rw [hM2, hs2]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ℓ - 1) (by linarith : (0:ℝ) ≤ m - ℓ)]
    nlinarith
  have F5 : (m : ℝ) ≤ 4 * s * M := by
    nlinarith [mul_le_mul_of_nonneg_left hsM hM0, mul_nonneg hs0.le hM0]
  have F2 : 2 * s * ℓ *
      (if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) ≤
      ℓ * ((m : ℝ) - ℓ) * (x + 1) + (ℓ : ℝ) ^ 2 * ((m : ℝ) - x) := by
    split_ifs
    · have := amgm s ℓ (((i : ℕ) + 1 : ℝ)) ((m : ℝ) - (i : ℕ)) (by positivity) (by rw [← hx]; linarith)
      rw [hs2, ← hx] at this
      rw [← hx]
      linarith
    · have : 0 ≤ (ℓ : ℝ) * ((m : ℝ) - ℓ) * (x + 1) := by
        apply mul_nonneg hprod.le; linarith
      have : 0 ≤ (ℓ : ℝ) ^ 2 * ((m : ℝ) - x) := by
        apply mul_nonneg (by positivity); linarith
      linarith
  have F1 : 2 * s * ℓ *
      (if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) ≤
      ℓ * ((m : ℝ) - ℓ) * x + (ℓ : ℝ) ^ 2 * ((m : ℝ) - x + 1) := by
    split_ifs
    · have := amgm s ℓ (((i : ℕ) : ℝ)) ((m : ℝ) - (i : ℕ) + 1) (by positivity) (by rw [← hx]; linarith)
      rw [hs2, ← hx] at this
      rw [← hx]
      linarith
    · have : 0 ≤ (ℓ : ℝ) * ((m : ℝ) - ℓ) * x := mul_nonneg hprod.le hx0
      have : 0 ≤ (ℓ : ℝ) ^ 2 * ((m : ℝ) - x + 1) := by
        apply mul_nonneg (by positivity); linarith
      linarith
  have F3' : 2 * ℓ * (ℓ - x) * (-((m : ℝ) - 2 * ℓ)) ≤ 2 * ℓ * (ℓ - x) * (dpar * s) :=
    mul_le_mul_of_nonneg_left F3 (mul_nonneg (by linarith) (by linarith))
  have F5' : (ℓ : ℝ) * m ≤ ℓ * (4 * s * M) := mul_le_mul_of_nonneg_left F5 (by linarith)
  have hs2' : s * s * ℓ = ℓ * (ℓ * ((m : ℝ) - ℓ)) := by rw [← sq, hs2]; ring
  obtain ⟨BP, hBP⟩ : ∃ B, B =
      (if (i : ℕ) + 1 ≤ ℓ then Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) :=
    ⟨_, rfl⟩
  obtain ⟨BQ, hBQ⟩ : ∃ B, B =
      (if 1 ≤ (i : ℕ) then Real.sqrt (((i : ℕ) : ℝ) * ((m : ℝ) - (i : ℕ) + 1)) else 0) :=
    ⟨_, rfl⟩
  rw [← hBP] at F2 hR
  rw [← hBQ] at F1 hR
  rw [hdiag, ← hx] at hti
  have key : 2 * s * ℓ * (x * dpar + (BP + BQ)) ≤
      2 * s * ℓ * (2 * M + ℓ * dpar + 2 * s) := by
    nlinarith
  have h2sl : 0 < 2 * s * ℓ := mul_pos (mul_pos two_pos hs0) (by linarith)
  have := le_of_mul_le_mul_left key h2sl
  linarith

end Aux_DQI_Semicircle_lemma_9_3_A

namespace Aux_DQI_Semicircle_lemma_9_3_B

open DQI.Semicircle Matrix Filter Topology

lemma rayleigh {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (v : Fin N → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ sSup (spectrum ℝ A) * (v ⬝ᵥ v) := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℝ,
      U = (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := ⟨_, rfl⟩
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    rw [hU]
    exact this
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  obtain ⟨w, hw⟩ : ∃ w : Fin N → ℝ, w = Uᵀ *ᵥ v := ⟨_, rfl⟩
  have hL : ∀ j, hA.eigenvalues j ≤ sSup (spectrum ℝ A) := fun j =>
    le_csSup (Matrix.finite_spectrum A).bddAbove (hA.eigenvalues_mem_spectrum_real j)
  have h1 : v ⬝ᵥ (A *ᵥ v) = ∑ j, hA.eigenvalues j * (w j) ^ 2 := by
    have hAv : A *ᵥ v =
        U *ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (Uᵀ *ᵥ v)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hstar, ← hspec]
    rw [hAv, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hw]
    simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
      id_eq]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : v ⬝ᵥ v = ∑ j, (w j) ^ 2 := by
    have : w ⬝ᵥ w = v ⬝ᵥ v := by
      rw [hw, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
        Matrix.mulVec_mulVec, ← hstar, hUU, Matrix.one_mulVec]
    rw [← this, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hL j) (sq_nonneg _)

lemma atri_herm (m ℓ : ℕ) (d : ℝ) : (Atri m ℓ d).IsHermitian := by
  show (Atri m ℓ d)ᴴ = Atri m ℓ d
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  simp only [Matrix.transpose_apply, Atri]
  split_ifs <;> first
    | rfl
    | (exfalso; omega)
    | (have h : i = j := Fin.ext (by omega); subst h; rfl)

/-- Lower bound for the quadratic form on the indicator of the last `K+1` coordinates. -/
lemma quad_lb (m ℓ K : ℕ) (d : ℝ) (hK : K ≤ ℓ) (hℓm : 2 * ℓ ≤ m) :
    ((K : ℝ) + 1) * (ℓ * d - K * |d|) +
        2 * K * Real.sqrt (((ℓ : ℝ) - K) * ((m : ℝ) - ℓ)) ≤
      (fun i : Fin (ℓ + 1) => if ℓ - K ≤ (i : ℕ) then (1 : ℝ) else 0) ⬝ᵥ
        (Atri m ℓ d *ᵥ (fun i : Fin (ℓ + 1) => if ℓ - K ≤ (i : ℕ) then (1 : ℝ) else 0)) := by
  obtain ⟨β, hβ⟩ : ∃ β, β = Real.sqrt (((ℓ : ℝ) - K) * ((m : ℝ) - ℓ)) := ⟨_, rfl⟩
  rw [← hβ]
  have hβ0 : 0 ≤ β := by rw [hβ]; exact Real.sqrt_nonneg _
  have hKR : (K : ℝ) ≤ ℓ := by exact_mod_cast hK
  have hℓmR : 2 * (ℓ : ℝ) ≤ m := by exact_mod_cast hℓm
  -- the row bound
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ n, c n = if ℓ - K ≤ n then
      (ℓ * d - K * |d|) + (if n + 1 ≤ ℓ then β else 0) + (if ℓ - K + 1 ≤ n then β else 0)
      else 0 := ⟨fun n => if ℓ - K ≤ n then
      (ℓ * d - K * |d|) + (if n + 1 ≤ ℓ then β else 0) + (if ℓ - K + 1 ≤ n then β else 0)
      else 0, fun _ => rfl⟩
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hrow : ∀ i : Fin (ℓ + 1), c i ≤
      (if ℓ - K ≤ (i : ℕ) then (1 : ℝ) else 0) *
        ∑ j : Fin (ℓ + 1), Atri m ℓ d i j * (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) := by
    intro i
    have hi := i.isLt
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hc]
    by_cases hW : ℓ - K ≤ (i : ℕ)
    · simp only [if_pos hW, one_mul]
      -- split the row sum
      have hsplit : ∀ j : Fin (ℓ + 1), Atri m ℓ d i j * (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) =
          (if j = i then ((i : ℕ) : ℝ) * d else 0) +
          ((if (j : ℕ) = (i : ℕ) + 1 then
              Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) *
            (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) +
          (if (i : ℕ) = (j : ℕ) + 1 then
              Real.sqrt (((j : ℕ) + 1 : ℝ) * ((m : ℝ) - (j : ℕ))) else 0) *
            (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0)) := by
        intro j
        simp only [Atri]
        by_cases h1 : j = i
        · subst h1
          simp [hW]
        · have h1' : (i : ℕ) ≠ (j : ℕ) := fun h => h1 (Fin.ext h.symm)
          rw [if_neg h1', if_neg h1, zero_add]
          by_cases h2 : (j : ℕ) = (i : ℕ) + 1
          · rw [if_pos h2, if_pos h2, if_neg (show ¬ ((i : ℕ) = (j : ℕ) + 1) by omega), zero_mul,
              add_zero]
          · rw [if_neg h2, if_neg h2, zero_mul, zero_add]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
      -- diagonal part
      have hdiag : (ℓ : ℝ) * d - K * |d| ≤ ((i : ℕ) : ℝ) * d := by
        have hi1 : ((i : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast (show (i : ℕ) ≤ ℓ by omega)
        have hi2 : (ℓ : ℝ) - K ≤ ((i : ℕ) : ℝ) := by
          have : ℓ - K ≤ (i : ℕ) := hW
          have h' : ((ℓ - K : ℕ) : ℝ) = (ℓ : ℝ) - K := Nat.cast_sub hK
          rw [← h']
          exact_mod_cast this
        have := abs_nonneg d
        rcases le_or_gt 0 d with hd | hd
        · rw [abs_of_nonneg hd]; nlinarith
        · rw [abs_of_neg hd]; nlinarith
      -- the off-diagonal parts
      have hP : (if (i : ℕ) + 1 ≤ ℓ then β else 0) ≤ ∑ j : Fin (ℓ + 1),
          (if (j : ℕ) = (i : ℕ) + 1 then
              Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) *
            (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) := by
        by_cases h : (i : ℕ) + 1 ≤ ℓ
        · rw [if_pos h]
          have hle : (⟨(i : ℕ) + 1, by omega⟩ : Fin (ℓ + 1)) ∈ Finset.univ := Finset.mem_univ _
          have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))), 0 ≤
              (if (j : ℕ) = (i : ℕ) + 1 then
                Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) *
              (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) := by
            intro j _
            apply mul_nonneg
            · split_ifs
              · exact Real.sqrt_nonneg _
              · exact le_rfl
            · split_ifs <;> norm_num
          refine le_trans ?_ (Finset.single_le_sum hnn hle)
          show β ≤ (if (i : ℕ) + 1 = (i : ℕ) + 1 then
                Real.sqrt (((i : ℕ) + 1 : ℝ) * ((m : ℝ) - (i : ℕ))) else 0) *
              (if ℓ - K ≤ (i : ℕ) + 1 then (1 : ℝ) else 0)
          rw [if_pos rfl, if_pos (show ℓ - K ≤ (i : ℕ) + 1 by omega), mul_one, hβ]
          apply Real.sqrt_le_sqrt
          have hi1 : ((i : ℕ) : ℝ) + 1 ≤ ℓ := by exact_mod_cast h
          have hi2 : (ℓ : ℝ) - K ≤ ((i : ℕ) : ℝ) := by
            have h' : ((ℓ - K : ℕ) : ℝ) = (ℓ : ℝ) - K := Nat.cast_sub hK
            rw [← h']
            exact_mod_cast hW
          apply mul_le_mul <;> nlinarith
        · rw [if_neg h]
          apply Finset.sum_nonneg
          intro j _
          apply mul_nonneg
          · split_ifs
            · exact Real.sqrt_nonneg _
            · exact le_rfl
          · split_ifs <;> norm_num
      have hQ : (if ℓ - K + 1 ≤ (i : ℕ) then β else 0) ≤ ∑ j : Fin (ℓ + 1),
          (if (i : ℕ) = (j : ℕ) + 1 then
              Real.sqrt (((j : ℕ) + 1 : ℝ) * ((m : ℝ) - (j : ℕ))) else 0) *
            (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) := by
        by_cases h : ℓ - K + 1 ≤ (i : ℕ)
        · rw [if_pos h]
          have hle : (⟨(i : ℕ) - 1, by omega⟩ : Fin (ℓ + 1)) ∈ Finset.univ := Finset.mem_univ _
          have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))), 0 ≤
              (if (i : ℕ) = (j : ℕ) + 1 then
                Real.sqrt (((j : ℕ) + 1 : ℝ) * ((m : ℝ) - (j : ℕ))) else 0) *
              (if ℓ - K ≤ (j : ℕ) then (1 : ℝ) else 0) := by
            intro j _
            apply mul_nonneg
            · split_ifs
              · exact Real.sqrt_nonneg _
              · exact le_rfl
            · split_ifs <;> norm_num
          refine le_trans ?_ (Finset.single_le_sum hnn hle)
          show β ≤ (if (i : ℕ) = (i : ℕ) - 1 + 1 then
                Real.sqrt ((((i : ℕ) - 1 : ℕ) + 1 : ℝ) * ((m : ℝ) - ((i : ℕ) - 1 : ℕ))) else 0) *
              (if ℓ - K ≤ (i : ℕ) - 1 then (1 : ℝ) else 0)
          rw [if_pos (show (i : ℕ) = (i : ℕ) - 1 + 1 by omega),
            if_pos (show ℓ - K ≤ (i : ℕ) - 1 by omega), mul_one, hβ]
          apply Real.sqrt_le_sqrt
          have hcast : (((i : ℕ) - 1 : ℕ) : ℝ) = ((i : ℕ) : ℝ) - 1 := by
            have : 1 ≤ (i : ℕ) := by omega
            rw [Nat.cast_sub this, Nat.cast_one]
          rw [hcast]
          have hi1 : ((i : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast (show (i : ℕ) ≤ ℓ by omega)
          have hi2 : (ℓ : ℝ) - K + 1 ≤ ((i : ℕ) : ℝ) := by
            have h' : ((ℓ - K + 1 : ℕ) : ℝ) = (ℓ : ℝ) - K + 1 := by
              rw [Nat.cast_add, Nat.cast_sub hK, Nat.cast_one]
            rw [← h']
            exact_mod_cast h
          apply mul_le_mul <;> nlinarith
        · rw [if_neg h]
          apply Finset.sum_nonneg
          intro j _
          apply mul_nonneg
          · split_ifs
            · exact Real.sqrt_nonneg _
            · exact le_rfl
          · split_ifs <;> norm_num
      linarith
    · simp only [if_neg hW, zero_mul, le_refl]
  -- sum of the row bounds
  have hsum : ∑ i : Fin (ℓ + 1), c i =
      ((K : ℝ) + 1) * (ℓ * d - K * |d|) + 2 * K * β := by
    rw [Fin.sum_univ_eq_sum_range c (ℓ + 1)]
    simp only [hc]
    have e1 : ∀ n ∈ Finset.range (ℓ + 1), (if ℓ - K ≤ n then
        (ℓ * d - K * |d|) + (if n + 1 ≤ ℓ then β else 0) + (if ℓ - K + 1 ≤ n then β else 0)
        else 0) =
        (if ℓ - K ≤ n then (ℓ * d - K * |d|) else 0) +
        (if ℓ - K ≤ n ∧ n + 1 ≤ ℓ then β else 0) + (if ℓ - K + 1 ≤ n then β else 0) := by
      intro n _
      by_cases h1 : ℓ - K ≤ n
      · by_cases h2 : n + 1 ≤ ℓ
        · simp [h1, h2]
        · simp [h1, h2]
      · have h3 : ¬ (ℓ - K + 1 ≤ n) := by omega
        simp [h1, h3]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have c1 : ((Finset.range (ℓ + 1)).filter (fun n => ℓ - K ≤ n)).card = K + 1 := by
      have : (Finset.range (ℓ + 1)).filter (fun n => ℓ - K ≤ n) = Finset.Ico (ℓ - K) (ℓ + 1) := by
        ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]; omega
    have c2 : ((Finset.range (ℓ + 1)).filter (fun n => ℓ - K ≤ n ∧ n + 1 ≤ ℓ)).card = K := by
      have : (Finset.range (ℓ + 1)).filter (fun n => ℓ - K ≤ n ∧ n + 1 ≤ ℓ) =
          Finset.Ico (ℓ - K) ℓ := by
        ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]; omega
    have c3 : ((Finset.range (ℓ + 1)).filter (fun n => ℓ - K + 1 ≤ n)).card = K := by
      have : (Finset.range (ℓ + 1)).filter (fun n => ℓ - K + 1 ≤ n) =
          Finset.Ico (ℓ - K + 1) (ℓ + 1) := by
        ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]; omega
    rw [c1, c2, c3]
    push_cast
    ring
  rw [← hsum, dotProduct]
  apply Finset.sum_le_sum
  intro i _
  have := hrow i
  simp only [Matrix.mulVec, dotProduct] at this ⊢
  linarith

end Aux_DQI_Semicircle_lemma_9_3_B

namespace Aux_DQI_Semicircle_lemma_9_3_B

open DQI.Semicircle Filter Topology in
theorem eq114 (μ dpar : ℝ) (hμ : 0 < μ) (m ℓ : ℕ → ℕ)
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) (hℓm : ∀ j, 2 * ℓ j ≤ m j) :
    ∀ ε > 0, ∀ᶠ j in Filter.atTop,
      μ * dpar + 2 * Real.sqrt (μ * (1 - μ)) - ε ≤ lamMax (Atri (m j) (ℓ j) dpar) / m j := by
  intro ε hε
  -- choose the window length
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 / ε < K := exists_nat_gt (1 / ε)
  have hKpos : (0 : ℝ) < K := lt_trans (one_div_pos.mpr hε) hK
  have hsq : Real.sqrt (μ * (1 - μ)) ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [sq_nonneg (μ - 1 / 2)]
  have hgap : 2 * Real.sqrt (μ * (1 - μ)) - 2 * ((K : ℝ) / (K + 1)) * Real.sqrt (μ * (1 - μ)) < ε := by
    have h1 : 2 * Real.sqrt (μ * (1 - μ)) - 2 * ((K : ℝ) / (K + 1)) * Real.sqrt (μ * (1 - μ)) =
        2 * Real.sqrt (μ * (1 - μ)) / (K + 1) := by
      have : (K : ℝ) + 1 ≠ 0 := by positivity
      field_simp <;> ring
    rw [h1, div_lt_iff₀ (by positivity)]
    have h2 : 1 < ε * K := by rwa [div_lt_iff₀ hε, mul_comm] at hK
    nlinarith [Real.sqrt_nonneg (μ * (1 - μ))]
  -- the limit of the lower bound
  have hmR : Tendsto (fun j => (m j : ℝ)) atTop atTop := tendsto_natCast_atTop_iff.mpr hm
  have hK0 : Tendsto (fun j => (K : ℝ) / (m j : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).comp hm
  have hKd : Tendsto (fun j => (K : ℝ) * |dpar| / (m j : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((K : ℝ) * |dpar|)).comp hm
  have hA1 : Tendsto (fun j => ((ℓ j : ℝ) - K) / (m j : ℝ)) atTop (𝓝 μ) := by
    have := hratio.sub hK0
    rw [sub_zero] at this
    exact this.congr (fun j => (sub_div _ _ _).symm)
  have hA2 : Tendsto (fun j => ((m j : ℝ) - ℓ j) / (m j : ℝ)) atTop (𝓝 (1 - μ)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
    refine this.congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with j hj
    have : (m j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    rw [sub_div, div_self this]
  have hG : Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ) * dpar - (K : ℝ) * |dpar| / (m j : ℝ) +
      2 * ((K : ℝ) / (K + 1)) *
        Real.sqrt (((ℓ j : ℝ) - K) / (m j : ℝ) * (((m j : ℝ) - ℓ j) / (m j : ℝ)))) atTop
      (𝓝 (μ * dpar - 0 + 2 * ((K : ℝ) / (K + 1)) * Real.sqrt (μ * (1 - μ)))) :=
    ((hratio.mul_const dpar).sub hKd).add ((hA1.mul hA2).sqrt.const_mul _)
  have hev := hG.eventually (lt_mem_nhds (show μ * dpar + 2 * Real.sqrt (μ * (1 - μ)) - ε <
      μ * dpar - 0 + 2 * ((K : ℝ) / (K + 1)) * Real.sqrt (μ * (1 - μ)) by linarith))
  -- ℓ j ≥ K eventually
  have hℓK : ∀ᶠ j in atTop, K ≤ ℓ j := by
    have h1 := hratio.eventually (lt_mem_nhds (show μ / 2 < μ by linarith))
    have h2 := hmR.eventually_gt_atTop (2 * K / μ)
    filter_upwards [h1, h2] with j hj1 hj2
    have hmpos : (0 : ℝ) < m j :=
      lt_of_le_of_lt (div_nonneg (by positivity) hμ.le) hj2
    rw [lt_div_iff₀ hmpos] at hj1
    have : (K : ℝ) ≤ ℓ j := by
      rw [div_lt_iff₀ hμ] at hj2
      linarith
    exact_mod_cast this
  filter_upwards [hev, hℓK, hm.eventually_gt_atTop 0] with j hj hjK hjm
  have hmpos : (0 : ℝ) < m j := by exact_mod_cast hjm
  -- Rayleigh lower bound
  have hq := quad_lb (m j) (ℓ j) K dpar hjK (hℓm j)
  have hr := rayleigh (Atri (m j) (ℓ j) dpar) (atri_herm _ _ _)
    (fun i : Fin (ℓ j + 1) => if ℓ j - K ≤ (i : ℕ) then (1 : ℝ) else 0)
  have hvv : (fun i : Fin (ℓ j + 1) => if ℓ j - K ≤ (i : ℕ) then (1 : ℝ) else 0) ⬝ᵥ
      (fun i : Fin (ℓ j + 1) => if ℓ j - K ≤ (i : ℕ) then (1 : ℝ) else 0) = (K : ℝ) + 1 := by
    calc _ = ∑ i : Fin (ℓ j + 1), (fun n : ℕ => if ℓ j - K ≤ n then (1 : ℝ) else 0) (i : ℕ) := by
          simp only [dotProduct]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> norm_num
      _ = ∑ n ∈ Finset.range (ℓ j + 1), (fun n : ℕ => if ℓ j - K ≤ n then (1 : ℝ) else 0) n :=
          Fin.sum_univ_eq_sum_range (fun n : ℕ => if ℓ j - K ≤ n then (1 : ℝ) else 0) (ℓ j + 1)
      _ = (K : ℝ) + 1 := by
          simp only []
          rw [Finset.sum_boole]
          have : (Finset.range (ℓ j + 1)).filter (fun n => ℓ j - K ≤ n) =
              Finset.Ico (ℓ j - K) (ℓ j + 1) := by
            ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
          rw [this, Nat.card_Ico, show ℓ j + 1 - (ℓ j - K) = K + 1 by omega]
          push_cast
          ring
  rw [hvv] at hr
  have hlam : ((K : ℝ) + 1) * (ℓ j * dpar - K * |dpar|) +
      2 * K * Real.sqrt (((ℓ j : ℝ) - K) * ((m j : ℝ) - ℓ j)) ≤
      lamMax (Atri (m j) (ℓ j) dpar) * ((K : ℝ) + 1) := by
    unfold lamMax
    linarith
  -- divide by (K+1) m
  have hsqrt : Real.sqrt (((ℓ j : ℝ) - K) / (m j : ℝ) * (((m j : ℝ) - ℓ j) / (m j : ℝ))) =
      Real.sqrt (((ℓ j : ℝ) - K) * ((m j : ℝ) - ℓ j)) / m j := by
    rw [div_mul_div_comm, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hmpos.le]
  rw [hsqrt] at hj
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have e : (ℓ j : ℝ) / (m j) * dpar - K * |dpar| / m j +
      2 * ((K : ℝ) / (K + 1)) * (Real.sqrt (((ℓ j : ℝ) - K) * ((m j : ℝ) - ℓ j)) / m j) =
      (((K : ℝ) + 1) * (ℓ j * dpar - K * |dpar|) +
        2 * K * Real.sqrt (((ℓ j : ℝ) - K) * ((m j : ℝ) - ℓ j))) / ((K + 1) * m j) := by
    have h1 : (K : ℝ) + 1 ≠ 0 := hK1.ne'
    have h2 : (m j : ℝ) ≠ 0 := hmpos.ne'
    field_simp <;> ring
  have hfin : (((K : ℝ) + 1) * (ℓ j * dpar - K * |dpar|) +
        2 * K * Real.sqrt (((ℓ j : ℝ) - K) * ((m j : ℝ) - ℓ j))) / ((K + 1) * m j) ≤
      lamMax (Atri (m j) (ℓ j) dpar) / m j := by
    rw [div_le_div_iff₀ (mul_pos hK1 hmpos) hmpos]
    have := mul_le_mul_of_nonneg_right hlam hmpos.le
    nlinarith
  linarith

end Aux_DQI_Semicircle_lemma_9_3_B

open Aux_DQI_Semicircle_lemma_9_3_A Aux_DQI_Semicircle_lemma_9_3_B in
open DQI.Semicircle Filter Topology in
theorem solution (μ dpar : ℝ) (hμ : 0 < μ) (m ℓ : ℕ → ℕ)
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) (hℓm : ∀ j, 2 * ℓ j ≤ m j)
    (hd : ∀ j, 0 < ℓ j → -((m j : ℝ) - 2 * ℓ j) / Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j)) ≤ dpar) :
    Filter.Tendsto (fun j => lamMax (Atri (m j) (ℓ j) dpar) / m j) Filter.atTop
      (nhds (μ * dpar + 2 * Real.sqrt (μ * (1 - μ)))) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have h := eq114 μ dpar hμ m ℓ hratio hm hℓm ((μ * dpar + 2 * Real.sqrt (μ * (1 - μ)) - a) / 2)
      (by linarith)
    filter_upwards [h] with j hj
    linarith
  · intro a ha
    have hmR : Tendsto (fun j => (m j : ℝ)) atTop atTop := tendsto_natCast_atTop_iff.mpr hm
    have h1 : Tendsto (fun j => Real.sqrt (1 / (m j : ℝ))) atTop (𝓝 (Real.sqrt 0)) :=
      ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hm).sqrt
    have hA2 : Tendsto (fun j => ((m j : ℝ) - ℓ j) / (m j : ℝ)) atTop (𝓝 (1 - μ)) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
      refine this.congr' ?_
      filter_upwards [hm.eventually_gt_atTop 0] with j hj
      have : (m j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
      rw [sub_div, div_self this]
    have hU : Tendsto (fun j => 2 * Real.sqrt (1 / (m j : ℝ)) + (ℓ j : ℝ) / (m j : ℝ) * dpar +
        2 * Real.sqrt ((ℓ j : ℝ) / (m j : ℝ) * (((m j : ℝ) - ℓ j) / (m j : ℝ)))) atTop
        (𝓝 (2 * Real.sqrt 0 + μ * dpar + 2 * Real.sqrt (μ * (1 - μ)))) :=
      ((h1.const_mul 2).add (hratio.mul_const dpar)).add ((hratio.mul hA2).sqrt.const_mul 2)
    rw [Real.sqrt_zero, mul_zero, zero_add] at hU
    have hev := hU.eventually (gt_mem_nhds ha)
    have hℓ1 : ∀ᶠ j in atTop, 1 ≤ ℓ j := by
      have e1 := hratio.eventually (lt_mem_nhds (show μ / 2 < μ by linarith))
      have e2 := hmR.eventually_gt_atTop (2 / μ)
      filter_upwards [e1, e2] with j hj1 hj2
      have hmpos : (0 : ℝ) < m j := lt_of_le_of_lt (div_nonneg (by norm_num) hμ.le) hj2
      rw [lt_div_iff₀ hmpos] at hj1
      rw [div_lt_iff₀ hμ] at hj2
      have : (1 : ℝ) ≤ ℓ j := by nlinarith
      exact_mod_cast this
    filter_upwards [hev, hℓ1, hm.eventually_gt_atTop 0] with j hj hj1 hjm
    have hmpos : (0 : ℝ) < m j := by exact_mod_cast hjm
    have hup := eq129 (m j) (ℓ j) dpar hj1 (hℓm j) (hd j (by omega))
    have hne : (spectrum ℝ (Atri (m j) (ℓ j) dpar)).Nonempty :=
      ⟨_, (atri_herm (m j) (ℓ j) dpar).eigenvalues_mem_spectrum_real ⟨0, by omega⟩⟩
    have hlam : lamMax (Atri (m j) (ℓ j) dpar) ≤
        2 * Real.sqrt (m j) + ℓ j * dpar + 2 * Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j)) :=
      csSup_le hne hup
    have e1 : Real.sqrt (1 / (m j : ℝ)) = Real.sqrt (m j) / m j := by
      rw [Real.sqrt_div' _ hmpos.le, Real.sqrt_one,
        div_eq_div_iff (Real.sqrt_pos.mpr hmpos).ne' hmpos.ne', one_mul,
        Real.mul_self_sqrt hmpos.le]
    have e2 : Real.sqrt ((ℓ j : ℝ) / (m j : ℝ) * (((m j : ℝ) - ℓ j) / (m j : ℝ))) =
        Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j)) / m j := by
      rw [div_mul_div_comm, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hmpos.le]
    rw [e1, e2] at hj
    have hform : (2 * Real.sqrt (m j) + ℓ j * dpar + 2 * Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j))) /
        m j = 2 * (Real.sqrt (m j) / m j) + (ℓ j : ℝ) / (m j : ℝ) * dpar +
          2 * (Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j)) / m j) := by ring
    calc lamMax (Atri (m j) (ℓ j) dpar) / m j
        ≤ (2 * Real.sqrt (m j) + ℓ j * dpar + 2 * Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j))) / m j :=
          div_le_div_of_nonneg_right hlam hmpos.le
      _ < a := by rw [hform]; exact hj
