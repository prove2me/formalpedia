-- Prove2me | solution 1 for EinsteinFieldEquations.schwarzschild_vacuum_solution
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T06:51:54.386018+00:00
-- url     : https://prove2.me/submissions/b73e4930-04f8-4ff4-80f6-3fe5923d5d5d

import Mathlib
import Definitions.Def_efe_geometry
import Definitions.Def_efe_metrics

open EinsteinFieldEquations

theorem W7a_EinsteinFieldEquations_pd_prod (A B : ℝ → ℝ) (i j k : Fin 4) (x : Coord)
    (hA : DifferentiableAt ℝ A (x i)) (hB : DifferentiableAt ℝ B (x j)) :
    partialD (fun y => A (y i) * B (y j)) k x =
      (if k = i then deriv A (x i) * B (x j) else 0) +
      (if k = j then A (x i) * deriv B (x j) else 0) := by
  have h1 : HasFDerivAt (fun y : Coord => A (y i))
      (deriv A (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x :=
    hA.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply i x)
  have h2 : HasFDerivAt (fun y : Coord => B (y j))
      (deriv B (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j) x :=
    hB.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_apply j x)
  have h3 : HasFDerivAt (fun y : Coord => A (y i) * B (y j)) _ x := h1.mul h2
  unfold partialD
  rw [h3.fderiv]
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [hi, hj, Pi.single_apply, eq_comm] <;> ring

theorem W7a_EinsteinFieldEquations_chr_diag (h : Fin 4 → Coord → ℝ) (x : Coord)
    (hx : ∀ i, h i x ≠ 0) (a b c : Fin 4) :
    christoffel (fun y => Matrix.diagonal (fun i => h i y)) a b c x =
      (1 / 2 : ℝ) * (h a x)⁻¹ * ((if a = c then partialD (h a) b x else 0)
        + (if a = b then partialD (h a) c x else 0)
        - (if b = c then partialD (h b) a x else 0)) := by
  have hinv : (Matrix.diagonal (fun i => h i x))⁻¹ = Matrix.diagonal (fun i => (h i x)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hx i)
  have hp : ∀ (i j k : Fin 4), partialD (fun y => if i = j then h i y else 0) k x
      = if i = j then partialD (h i) k x else 0 := by
    intro i j k
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, partialD]
  unfold christoffel
  simp only [hinv, Matrix.diagonal_apply, hp, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring

noncomputable def W7a_EinsteinFieldEquations_sA (M : ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun r => -(1 - 2 * M / r), fun r => (1 - 2 * M / r)⁻¹, fun r => r ^ 2, fun r => r ^ 2]

noncomputable def W7a_EinsteinFieldEquations_sA' (M : ℝ) : Fin 4 → ℝ → ℝ :=
  ![fun r => -(2 * M / r ^ 2), fun r => -(2 * M / r ^ 2) / (1 - 2 * M / r) ^ 2,
    fun r => 2 * r, fun r => 2 * r]

noncomputable def W7a_EinsteinFieldEquations_sB : Fin 4 → ℝ → ℝ :=
  ![fun _ => 1, fun _ => 1, fun _ => 1, fun t => Real.sin t ^ 2]

noncomputable def W7a_EinsteinFieldEquations_sB' : Fin 4 → ℝ → ℝ :=
  ![fun _ => 0, fun _ => 0, fun _ => 0, fun t => 2 * Real.sin t * Real.cos t]

theorem W7a_EinsteinFieldEquations_schw_eq (M : ℝ) :
    schwarzschild M = fun y => Matrix.diagonal (fun i =>
      W7a_EinsteinFieldEquations_sA M i (y 1) * W7a_EinsteinFieldEquations_sB i (y 2)) := by
  funext y
  show Matrix.diagonal _ = Matrix.diagonal _
  congr 1; funext i
  fin_cases i <;> simp [W7a_EinsteinFieldEquations_sA, W7a_EinsteinFieldEquations_sB]

theorem W7a_EinsteinFieldEquations_lapse_hd (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun r => 1 - 2 * M / r) (2 * M / r ^ 2) r := by
  have := ((hasDerivAt_inv hr).const_mul (2 * M)).const_sub 1
  have e : (fun r => 1 - 2 * M / r) = fun x => 1 - 2 * M * x⁻¹ := by funext y; ring
  rw [e]
  exact this.congr_deriv (by ring)

theorem W7a_EinsteinFieldEquations_lapse_ne (M r : ℝ) (hr : r ≠ 0) (hf : r - 2 * M ≠ 0) :
    1 - 2 * M / r ≠ 0 := by
  rw [one_sub_div hr]; exact div_ne_zero hf hr

theorem W7a_EinsteinFieldEquations_hdA (M r : ℝ) (hr : r ≠ 0) (hf : r - 2 * M ≠ 0)
    (i : Fin 4) :
    HasDerivAt (W7a_EinsteinFieldEquations_sA M i) (W7a_EinsteinFieldEquations_sA' M i r) r := by
  have h0 := W7a_EinsteinFieldEquations_lapse_hd M r hr
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
    exact (hasDerivAt_pow 2 r).congr_deriv (by norm_num)
  fin_cases i
  · exact h0.neg
  · exact h0.inv (W7a_EinsteinFieldEquations_lapse_ne M r hr hf)
  · exact h2
  · exact h2

theorem W7a_EinsteinFieldEquations_hdB (t : ℝ) (i : Fin 4) :
    HasDerivAt (W7a_EinsteinFieldEquations_sB i) (W7a_EinsteinFieldEquations_sB' i t) t := by
  fin_cases i
  · exact hasDerivAt_const t (1 : ℝ)
  · exact hasDerivAt_const t (1 : ℝ)
  · exact hasDerivAt_const t (1 : ℝ)
  · show HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t
    exact ((Real.hasDerivAt_sin t).pow 2).congr_deriv (by norm_num)

theorem W7a_EinsteinFieldEquations_schw_chr (M : ℝ) (y : Coord) (hr : y 1 ≠ 0)
    (hf : y 1 - 2 * M ≠ 0) (hs : Real.sin (y 2) ≠ 0) (a b c : Fin 4) :
    christoffel (schwarzschild M) a b c y =
      (1 / 2 : ℝ) * (W7a_EinsteinFieldEquations_sA M a (y 1) * W7a_EinsteinFieldEquations_sB a (y 2))⁻¹ *
        ((if a = c then (if b = 1 then W7a_EinsteinFieldEquations_sA' M a (y 1) * W7a_EinsteinFieldEquations_sB a (y 2) else 0)
            + (if b = 2 then W7a_EinsteinFieldEquations_sA M a (y 1) * W7a_EinsteinFieldEquations_sB' a (y 2) else 0) else 0)
        + (if a = b then (if c = 1 then W7a_EinsteinFieldEquations_sA' M a (y 1) * W7a_EinsteinFieldEquations_sB a (y 2) else 0)
            + (if c = 2 then W7a_EinsteinFieldEquations_sA M a (y 1) * W7a_EinsteinFieldEquations_sB' a (y 2) else 0) else 0)
        - (if b = c then (if a = 1 then W7a_EinsteinFieldEquations_sA' M b (y 1) * W7a_EinsteinFieldEquations_sB b (y 2) else 0)
            + (if a = 2 then W7a_EinsteinFieldEquations_sA M b (y 1) * W7a_EinsteinFieldEquations_sB' b (y 2) else 0) else 0)) := by
  have hne : ∀ i, W7a_EinsteinFieldEquations_sA M i (y 1) * W7a_EinsteinFieldEquations_sB i (y 2) ≠ 0 := by
    have hl := W7a_EinsteinFieldEquations_lapse_ne M (y 1) hr hf
    have hl' : 2 * M / y 1 - 1 ≠ 0 := by intro h; apply hl; linarith
    intro i; fin_cases i <;>
      simp [W7a_EinsteinFieldEquations_sA, W7a_EinsteinFieldEquations_sB, hr, hs, hl, hl']
  have hp : ∀ i k, partialD (fun z => W7a_EinsteinFieldEquations_sA M i (z 1) * W7a_EinsteinFieldEquations_sB i (z 2)) k y =
      (if k = 1 then W7a_EinsteinFieldEquations_sA' M i (y 1) * W7a_EinsteinFieldEquations_sB i (y 2) else 0)
        + (if k = 2 then W7a_EinsteinFieldEquations_sA M i (y 1) * W7a_EinsteinFieldEquations_sB' i (y 2) else 0) := by
    intro i k
    rw [W7a_EinsteinFieldEquations_pd_prod _ _ 1 2 k y
      (W7a_EinsteinFieldEquations_hdA M (y 1) hr hf i).differentiableAt
      (W7a_EinsteinFieldEquations_hdB (y 2) i).differentiableAt,
      (W7a_EinsteinFieldEquations_hdA M (y 1) hr hf i).deriv,
      (W7a_EinsteinFieldEquations_hdB (y 2) i).deriv]
  rw [W7a_EinsteinFieldEquations_schw_eq M]
  rw [W7a_EinsteinFieldEquations_chr_diag
    (fun i z => W7a_EinsteinFieldEquations_sA M i (z 1) * W7a_EinsteinFieldEquations_sB i (z 2)) y hne]
  simp only [hp]

theorem W7a_EinsteinFieldEquations_schwarzschild_christoffel (M : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    christoffel (schwarzschild M) 0 0 1 x = M / (x 1 * (x 1 - 2 * M)) ∧
    christoffel (schwarzschild M) 0 1 0 x = M / (x 1 * (x 1 - 2 * M)) ∧
    christoffel (schwarzschild M) 1 0 0 x = M * (x 1 - 2 * M) / (x 1) ^ 3 ∧
    christoffel (schwarzschild M) 1 1 1 x = -(M / (x 1 * (x 1 - 2 * M))) ∧
    christoffel (schwarzschild M) 1 2 2 x = -(x 1 - 2 * M) ∧
    christoffel (schwarzschild M) 1 3 3 x = -(x 1 - 2 * M) * Real.sin (x 2) ^ 2 ∧
    christoffel (schwarzschild M) 2 1 2 x = 1 / x 1 ∧
    christoffel (schwarzschild M) 2 3 3 x = -(Real.sin (x 2) * Real.cos (x 2)) ∧
    christoffel (schwarzschild M) 3 1 3 x = 1 / x 1 ∧
    christoffel (schwarzschild M) 3 2 3 x = Real.cos (x 2) / Real.sin (x 2) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hr : x 1 ≠ 0 := by intro h; linarith
  have hf : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h2 h3).ne'
  simp only [W7a_EinsteinFieldEquations_schw_chr M x hr hf hs]
  simp [W7a_EinsteinFieldEquations_sA, W7a_EinsteinFieldEquations_sA',
    W7a_EinsteinFieldEquations_sB, W7a_EinsteinFieldEquations_sB']
  have hf2 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have hf3 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have hf4 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  and_intros
  all_goals first | (field_simp; ring) | field_simp | ring

noncomputable def W7a_EinsteinFieldEquations_GA (M : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let O : ℝ → ℝ := fun _ => 1
  let a1 : ℝ → ℝ := fun r => M / (r * (r - 2 * M))
  let a2 : ℝ → ℝ := fun r => M * (r - 2 * M) / r ^ 3
  let a3 : ℝ → ℝ := fun r => -(M / (r * (r - 2 * M)))
  let a4 : ℝ → ℝ := fun r => -(r - 2 * M)
  let a5 : ℝ → ℝ := fun r => 1 / r
  ![![![Z, a1, Z, Z], ![a1, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![a2, Z, Z, Z], ![Z, a3, Z, Z], ![Z, Z, a4, Z], ![Z, Z, Z, a4]],
    ![![Z, Z, Z, Z], ![Z, Z, a5, Z], ![Z, a5, Z, Z], ![Z, Z, Z, O]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, a5], ![Z, Z, Z, O], ![Z, a5, O, Z]]]

noncomputable def W7a_EinsteinFieldEquations_GA' (M : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let a1 : ℝ → ℝ := fun r => -(M * (2 * r - 2 * M)) / (r * (r - 2 * M)) ^ 2
  let a2 : ℝ → ℝ := fun r => M * (6 * M - 2 * r) / r ^ 4
  let a3 : ℝ → ℝ := fun r => M * (2 * r - 2 * M) / (r * (r - 2 * M)) ^ 2
  let a4 : ℝ → ℝ := fun _ => -1
  let a5 : ℝ → ℝ := fun r => -1 / r ^ 2
  ![![![Z, a1, Z, Z], ![a1, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![a2, Z, Z, Z], ![Z, a3, Z, Z], ![Z, Z, a4, Z], ![Z, Z, Z, a4]],
    ![![Z, Z, Z, Z], ![Z, Z, a5, Z], ![Z, a5, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, a5], ![Z, Z, Z, Z], ![Z, a5, Z, Z]]]

noncomputable def W7a_EinsteinFieldEquations_GB : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let O : ℝ → ℝ := fun _ => 1
  let b1 : ℝ → ℝ := fun t => Real.sin t ^ 2
  let b2 : ℝ → ℝ := fun t => -(Real.sin t * Real.cos t)
  let b3 : ℝ → ℝ := fun t => Real.cos t / Real.sin t
  ![![![Z, O, Z, Z], ![O, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![O, Z, Z, Z], ![Z, O, Z, Z], ![Z, Z, O, Z], ![Z, Z, Z, b1]],
    ![![Z, Z, Z, Z], ![Z, Z, O, Z], ![Z, O, Z, Z], ![Z, Z, Z, b2]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, O], ![Z, Z, Z, b3], ![Z, O, b3, Z]]]

noncomputable def W7a_EinsteinFieldEquations_GB' : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  let Z : ℝ → ℝ := fun _ => 0
  let b1 : ℝ → ℝ := fun t => 2 * Real.sin t * Real.cos t
  let b2 : ℝ → ℝ := fun t => Real.sin t ^ 2 - Real.cos t ^ 2
  let b3 : ℝ → ℝ := fun t => -1 / Real.sin t ^ 2
  ![![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, b1]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, b2]],
    ![![Z, Z, Z, Z], ![Z, Z, Z, Z], ![Z, Z, Z, b3], ![Z, Z, b3, Z]]]

theorem W7a_EinsteinFieldEquations_GA_hd (M r : ℝ) (hr : r ≠ 0) (hf : r - 2 * M ≠ 0)
    (a b c : Fin 4) :
    HasDerivAt (W7a_EinsteinFieldEquations_GA M a b c) (W7a_EinsteinFieldEquations_GA' M a b c r) r := by
  have hq : HasDerivAt (fun r => r * (r - 2 * M)) (1 * (r - 2 * M) + r * 1) r :=
    (hasDerivAt_id' r).mul ((hasDerivAt_id' r).sub_const (2 * M))
  have hq0 : r * (r - 2 * M) ≠ 0 := mul_ne_zero hr hf
  have h1 : HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * r - 2 * M)) / (r * (r - 2 * M)) ^ 2) r :=
    ((hasDerivAt_const r M).div hq hq0).congr_deriv (by ring)
  have h3 : HasDerivAt (fun r => -(M / (r * (r - 2 * M))))
      (M * (2 * r - 2 * M) / (r * (r - 2 * M)) ^ 2) r :=
    h1.neg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun r => M * (r - 2 * M) / r ^ 3) (M * (6 * M - 2 * r) / r ^ 4) r := by
    have hc : HasDerivAt (fun r : ℝ => r ^ 3) (3 * r ^ 2) r := by
      exact (hasDerivAt_pow 3 r).congr_deriv (by norm_num)
    exact ((((hasDerivAt_id' r).sub_const (2 * M)).const_mul M).div hc
      (pow_ne_zero 3 hr)).congr_deriv (by field_simp; ring)
  have h4 : HasDerivAt (fun r => -(r - 2 * M)) (-1) r :=
    ((hasDerivAt_id' r).sub_const (2 * M)).neg
  have h5 : HasDerivAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) r :=
    ((hasDerivAt_const r (1 : ℝ)).div (hasDerivAt_id' r) hr).congr_deriv (by ring)
  have hZ : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 r := hasDerivAt_const r 0
  have hO : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const r 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact hZ | exact hO | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

theorem W7a_EinsteinFieldEquations_GB_hd (t : ℝ) (hs : Real.sin t ≠ 0) (a b c : Fin 4) :
    HasDerivAt (W7a_EinsteinFieldEquations_GB a b c) (W7a_EinsteinFieldEquations_GB' a b c t) t := by
  have h1 : HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t := by
    exact ((Real.hasDerivAt_sin t).pow 2).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun t => -(Real.sin t * Real.cos t)) (Real.sin t ^ 2 - Real.cos t ^ 2) t :=
    ((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).neg.congr_deriv (by ring)
  have h3 : HasDerivAt (fun t => Real.cos t / Real.sin t) (-1 / Real.sin t ^ 2) t :=
    ((Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs).congr_deriv (by
      rw [div_eq_div_iff (pow_ne_zero 2 hs) (pow_ne_zero 2 hs)]
      nlinarith [Real.sin_sq_add_cos_sq t])
  have hZ : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have hO : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first | exact hZ | exact hO | exact h1 | exact h2 | exact h3

theorem W7a_EinsteinFieldEquations_chr_tab (M : ℝ) (y : Coord) (hr : y 1 ≠ 0)
    (hf : y 1 - 2 * M ≠ 0) (hs : Real.sin (y 2) ≠ 0) (a b c : Fin 4) :
    christoffel (schwarzschild M) a b c y =
      W7a_EinsteinFieldEquations_GA M a b c (y 1) * W7a_EinsteinFieldEquations_GB a b c (y 2) := by
  have hl := W7a_EinsteinFieldEquations_lapse_ne M (y 1) hr hf
  have n1 : 2 * M - y 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - y 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : y 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + y 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + y 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -y 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -y 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  rw [W7a_EinsteinFieldEquations_schw_chr M y hr hf hs]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [W7a_EinsteinFieldEquations_sA, W7a_EinsteinFieldEquations_sA',
      W7a_EinsteinFieldEquations_sB, W7a_EinsteinFieldEquations_sB',
      W7a_EinsteinFieldEquations_GA, W7a_EinsteinFieldEquations_GB] <;>
    field_simp <;> ring

theorem W7a_EinsteinFieldEquations_pd_chr (M : ℝ) (x : Coord) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (a b c k : Fin 4) :
    partialD (fun y => christoffel (schwarzschild M) a b c y) k x =
      (if k = 1 then W7a_EinsteinFieldEquations_GA' M a b c (x 1) * W7a_EinsteinFieldEquations_GB a b c (x 2) else 0) +
      (if k = 2 then W7a_EinsteinFieldEquations_GA M a b c (x 1) * W7a_EinsteinFieldEquations_GB' a b c (x 2) else 0) := by
  have hΩ : IsOpen {y : Coord | y 1 ≠ 0 ∧ y 1 - 2 * M ≠ 0 ∧ Real.sin (y 2) ≠ 0} := by
    refine (isOpen_ne_fun (continuous_apply 1) continuous_const).inter
      ((isOpen_ne_fun ((continuous_apply 1).sub continuous_const) continuous_const).inter
        (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 2)) continuous_const))
  have hev : (fun y => christoffel (schwarzschild M) a b c y) =ᶠ[nhds x]
      (fun y => W7a_EinsteinFieldEquations_GA M a b c (y 1) * W7a_EinsteinFieldEquations_GB a b c (y 2)) :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds ⟨hr, hf, hs⟩)
      (fun y hy => W7a_EinsteinFieldEquations_chr_tab M y hy.1 hy.2.1 hy.2.2 a b c)
  have hA := W7a_EinsteinFieldEquations_GA_hd M (x 1) hr hf a b c
  have hB := W7a_EinsteinFieldEquations_GB_hd (x 2) hs a b c
  unfold partialD
  rw [hev.fderiv_eq]
  have := W7a_EinsteinFieldEquations_pd_prod _ _ 1 2 k x hA.differentiableAt hB.differentiableAt
  unfold partialD at this
  rw [this, hA.deriv, hB.deriv]

theorem W7a_EinsteinFieldEquations_ricci_zero (M : ℝ) (x : Coord) (hr : x 1 ≠ 0)
    (hf : x 1 - 2 * M ≠ 0) (hs : Real.sin (x 2) ≠ 0) (b d : Fin 4) :
    ricci (schwarzschild M) b d x = 0 := by
  have hc4 : Real.cos (x 2) ^ 4 = (1 - Real.sin (x 2) ^ 2) ^ 2 := by
    rw [← Real.cos_sq']; ring
  have n1 : 2 * M - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n2 : M * 2 - x 1 ≠ 0 := by intro h; apply hf; linarith
  have n3 : x 1 - M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n4 : -(M * 2) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n5 : -(2 * M) + x 1 ≠ 0 := by intro h; apply hf; linarith
  have n6 : -x 1 + M * 2 ≠ 0 := by intro h; apply hf; linarith
  have n7 : -x 1 + 2 * M ≠ 0 := by intro h; apply hf; linarith
  unfold ricci riemann
  simp only [W7a_EinsteinFieldEquations_pd_chr M x hr hf hs,
    W7a_EinsteinFieldEquations_chr_tab M x hr hf hs]
  fin_cases b <;> fin_cases d <;>
    simp [Fin.sum_univ_four, W7a_EinsteinFieldEquations_GA, W7a_EinsteinFieldEquations_GB,
      W7a_EinsteinFieldEquations_GA', W7a_EinsteinFieldEquations_GB'] <;>
    field_simp <;> ring_nf <;> (try simp only [Real.cos_sq', hc4]) <;> ring_nf

theorem W7a_EinsteinFieldEquations_schwarzschild_ricci_flat (M : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    ∀ a b : Fin 4, ricci (schwarzschild M) a b x = 0 := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hr : x 1 ≠ 0 := by intro h; linarith
  have hf : x 1 - 2 * M ≠ 0 := by intro h; linarith
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi h2 h3).ne'
  exact W7a_EinsteinFieldEquations_ricci_zero M x hr hf hs

theorem solution (M : ℝ) (kappa : ℝ) (x : Coord) (hM : 0 < M)
    (hx : SchwarzschildExterior M x) :
    SatisfiesEFE (schwarzschild M) 0 kappa (fun _ => 0) x := by
  have h := W7a_EinsteinFieldEquations_schwarzschild_ricci_flat M x hM hx
  intro a b
  unfold einsteinTensor scalarCurvature metricTrace
  simp [h]
