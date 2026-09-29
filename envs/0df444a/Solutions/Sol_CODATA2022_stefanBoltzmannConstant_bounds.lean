-- Prove2me | solution 1 for CODATA2022.stefanBoltzmannConstant_bounds
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T20:01:29.100359+00:00
-- url     : https://prove2.me/submissions/8a788e14-3428-426a-847c-12cd886c5d09

import Mathlib
import Definitions.Def_CODATA2022_least_squares
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants

open CODATA2022 Matrix MeasureTheory

theorem W2p_CODATA2022_stefanBoltzmannConstant_eq_planck_form :
    stefanBoltzmannConstant
      = 2 * Real.pi ^ 5 * boltzmannConstant ^ 4 /
          (15 * planckConstant ^ 3 * speedOfLight ^ 2) := by
  unfold stefanBoltzmannConstant reducedPlanckConstant
  have hπ := Real.pi_pos.ne'
  have hh : planckConstant ≠ 0 := by unfold planckConstant; norm_num
  have hc : speedOfLight ≠ 0 := by unfold speedOfLight; norm_num
  field_simp <;> ring

theorem solution :
    5.670374419e-8 < stefanBoltzmannConstant ∧ stefanBoltzmannConstant < 5.670374420e-8 := by
  have lo : (3.14159265358979323846 : ℝ) ^ 5 < Real.pi ^ 5 :=
    pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
  have hi : Real.pi ^ 5 < (3.14159265358979323847 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ Real.pi_lt_d20 Real.pi_pos.le (by norm_num)
  rw [W2p_CODATA2022_stefanBoltzmannConstant_eq_planck_form]
  unfold boltzmannConstant planckConstant speedOfLight
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    have h1 : (5.670374419e-8 : ℝ) * (15 * (6.62607015e-34 : ℝ) ^ 3 * (299792458 : ℝ) ^ 2) <
        2 * (3.14159265358979323846 : ℝ) ^ 5 * (1.380649e-23 : ℝ) ^ 4 := by norm_num
    have h2 : 2 * (3.14159265358979323846 : ℝ) ^ 5 * (1.380649e-23 : ℝ) ^ 4 <
        2 * Real.pi ^ 5 * (1.380649e-23 : ℝ) ^ 4 := by gcongr
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    have h1 : 2 * (3.14159265358979323847 : ℝ) ^ 5 * (1.380649e-23 : ℝ) ^ 4 <
        (5.670374420e-8 : ℝ) * (15 * (6.62607015e-34 : ℝ) ^ 3 * (299792458 : ℝ) ^ 2) := by
      norm_num
    have h2 : 2 * Real.pi ^ 5 * (1.380649e-23 : ℝ) ^ 4 <
        2 * (3.14159265358979323847 : ℝ) ^ 5 * (1.380649e-23 : ℝ) ^ 4 := by gcongr
    linarith

theorem W2p_CODATA2022_symm {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (hW : W.PosDef) :
    Wᵀ = W := by
  have h := hW.1
  unfold Matrix.IsHermitian at h
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem W2p_CODATA2022_expand {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hWs : Wᵀ = W) (z : Fin N → ℝ) (xhat d : Fin M → ℝ) :
    chiSquare A W z (xhat + d) = chiSquare A W z xhat
      - 2 * (d ⬝ᵥ (Aᵀ * W) *ᵥ (z - A *ᵥ xhat)) + (A *ᵥ d) ⬝ᵥ W *ᵥ (A *ᵥ d) := by
  have key1 : ∀ u v : Fin N → ℝ, u ⬝ᵥ W *ᵥ v = v ⬝ᵥ W *ᵥ u := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hWs]
    exact dotProduct_comm _ _
  have key2 : ∀ u : Fin N → ℝ, (A *ᵥ d) ⬝ᵥ u = d ⬝ᵥ Aᵀ *ᵥ u := by
    intro u
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  unfold chiSquare
  have hr : z - A *ᵥ (xhat + d) = (z - A *ᵥ xhat) - A *ᵥ d := by
    rw [Matrix.mulVec_add]; abel
  rw [hr]
  generalize z - A *ᵥ xhat = r
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, key1 r (A *ᵥ d),
    key2 (W *ᵥ r), Matrix.mulVec_mulVec r Aᵀ W]
  ring

theorem W2p_CODATA2022_chiSquare_min_iff_normal_equations {N M : ℕ}
    (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : W.PosDef) (z : Fin N → ℝ) (xhat : Fin M → ℝ) :
    (∀ x : Fin M → ℝ, chiSquare A W z xhat ≤ chiSquare A W z x)
      ↔ (Aᵀ * W * A).mulVec xhat = (Aᵀ * W).mulVec z := by
  have hWs := W2p_CODATA2022_symm W hW
  have hPSD : ∀ v : Fin N → ℝ, 0 ≤ v ⬝ᵥ W *ᵥ v := fun v => by
    simpa using hW.posSemidef.dotProduct_mulVec_nonneg v
  have hNE : (Aᵀ * W * A) *ᵥ xhat = (Aᵀ * W) *ᵥ z ↔
      (Aᵀ * W) *ᵥ (z - A *ᵥ xhat) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec xhat (Aᵀ * W) A, sub_eq_zero, eq_comm]
  rw [hNE]
  constructor
  · intro hmin
    obtain ⟨g, hgdef⟩ : ∃ g, g = (Aᵀ * W) *ᵥ (z - A *ᵥ xhat) := ⟨_, rfl⟩
    rw [← hgdef]
    by_contra hne
    have hn0 : 0 ≤ g ⬝ᵥ g := Finset.sum_nonneg (fun i _ => mul_self_nonneg (g i))
    have hn2 : 0 < g ⬝ᵥ g :=
      lt_of_le_of_ne hn0 (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
    have hc := hPSD (A *ᵥ g)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (g ⬝ᵥ g) / ((A *ᵥ g) ⬝ᵥ W *ᵥ (A *ᵥ g) + 1) := ⟨_, rfl⟩
    have e1 : (t • g) ⬝ᵥ g = t * (g ⬝ᵥ g) := by
      simp only [smul_dotProduct, smul_eq_mul]
    have e2 : (A *ᵥ (t • g)) ⬝ᵥ W *ᵥ (A *ᵥ (t • g)) =
        t * t * ((A *ᵥ g) ⬝ᵥ W *ᵥ (A *ᵥ g)) := by
      simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] <;> ring
    have h := hmin (xhat + t • g)
    rw [W2p_CODATA2022_expand A W hWs z xhat (t • g), ← hgdef, e1, e2] at h
    generalize g ⬝ᵥ g = n at h ht hn2
    generalize (A *ᵥ g) ⬝ᵥ W *ᵥ (A *ᵥ g) = c at h ht hc
    have hc1 : (0 : ℝ) < c + 1 := by linarith
    have ht0 : 0 < t := by rw [ht]; exact div_pos hn2 hc1
    have htc : t * n = t * t * (c + 1) := by
      have hc1' := hc1.ne'
      rw [ht]; field_simp <;> ring
    nlinarith [mul_pos (mul_pos ht0 ht0) (by linarith : (0 : ℝ) < c + 2)]
  · intro hg0 x
    have h := W2p_CODATA2022_expand A W hWs z xhat (x - xhat)
    have hx : xhat + (x - xhat) = x := by abel
    rw [hx, hg0, dotProduct_zero] at h
    rw [h]
    linarith [hPSD (A *ᵥ (x - xhat))]

theorem W2p_CODATA2022_lsa_unique_minimizer {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℝ)
    (W : Matrix (Fin N) (Fin N) ℝ) (hW : W.PosDef) (z : Fin N → ℝ)
    (hinv : IsUnit (Aᵀ * W * A).det) :
    (∀ x : Fin M → ℝ,
        chiSquare A W z ((Aᵀ * W * A)⁻¹.mulVec ((Aᵀ * W).mulVec z)) ≤ chiSquare A W z x) ∧
      ∀ y : Fin M → ℝ, (∀ x : Fin M → ℝ, chiSquare A W z y ≤ chiSquare A W z x) →
        y = (Aᵀ * W * A)⁻¹.mulVec ((Aᵀ * W).mulVec z) := by
  constructor
  · apply (W2p_CODATA2022_chiSquare_min_iff_normal_equations A W hW z _).mpr
    rw [Matrix.mulVec_mulVec ((Aᵀ * W) *ᵥ z) (Aᵀ * W * A) (Aᵀ * W * A)⁻¹,
      Matrix.mul_nonsing_inv _ hinv, Matrix.one_mulVec]
  · intro y hy
    have hne := (W2p_CODATA2022_chiSquare_min_iff_normal_equations A W hW z y).mp hy
    rw [← hne, Matrix.mulVec_mulVec y (Aᵀ * W * A)⁻¹ (Aᵀ * W * A),
      Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]
