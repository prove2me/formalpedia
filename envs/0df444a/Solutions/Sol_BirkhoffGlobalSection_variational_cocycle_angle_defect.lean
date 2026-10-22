-- Prove2me | solution 1 for BirkhoffGlobalSection.variational_cocycle_angle_defect
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T21:01:56.114989+00:00
-- url     : https://prove2.me/submissions/56606a24-15c5-4aee-9595-5bf8e9eb570b

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_product_slit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# The period cocycle shifts the ambient angle by less than a turn

Write `d t = ambientRotationDet (Y t)`. The proof has three steps.

1. **The coefficient is infinitesimally symplectic, for any `F`.** If the totalized
   coordinate gradient of `F` is differentiable at `p`, its derivative `L` is symmetric
   (`grad_deriv_symm`). Points where `F` is not differentiable have zero gradient, so they
   accumulate at `p` only in directions where `L` vanishes. Small loops in the plane of
   `e i, e j`, offset in a direction where `L` does not vanish, therefore consist of
   differentiability points. `F` returns to its value around such a loop, while the affine
   model of the gradient contributes `π ε² ρ² (L e_i j - L e_j i)`, up to `o(ε²)` by a
   mean-value bound. Hence `D X_F = qI ∘ L` is infinitesimally symplectic, or zero where
   `X_F` is not differentiable.
2. **`Y t` is symplectic**, since `ω (Y u, Y v)` has zero derivative.
3. **Slit argument.** By the cocycle identity and the accepted theorem
   `ambient_rotation_product_slit`, `Q a = d (a + T) · conj (d a) · conj (d T)` lies in the
   slit plane. Its continuous argument starts at `0` at `a = 0`, so
   `α (a + T) - α a - α T + α 0 = arg (Q a) ≤ π`.

The coordinate, determinant and angle lemmas are copied from the accepted proofs of
`ambient_rotation_angle_exists` and `transported_closed_winding_above_one`.
-/

open BirkhoffGlobalSection
open scoped Topology Matrix

set_option autoImplicit false

/-! ### Coordinates -/

/-- The symplectic pairing `x ⬝ᵥ qI y` in coordinates. -/
private lemma omegaQ (x y : Phase) :
    x ⬝ᵥ TangentialHessian.qI.mulVec y = x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

private lemma qI_apply (w : Phase) :
    TangentialHessian.qI.mulVec w = ![w 2, w 3, -w 0, -w 1] := by
  funext i; fin_cases i <;> simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The ambient determinant in terms of the matrix entries. -/
private lemma ambientRotationDet_eq (M : Phase →L[ℝ] Phase) :
    ambientRotationDet M =
      (⟨(M (coordinateVector 0) 0 + M (coordinateVector 2) 2) / 2,
          (M (coordinateVector 2) 0 - M (coordinateVector 0) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 1) 1 + M (coordinateVector 3) 3) / 2,
          (M (coordinateVector 3) 1 - M (coordinateVector 1) 3) / 2⟩ -
      (⟨(M (coordinateVector 1) 0 + M (coordinateVector 3) 2) / 2,
          (M (coordinateVector 3) 0 - M (coordinateVector 1) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 0) 1 + M (coordinateVector 2) 3) / 2,
          (M (coordinateVector 2) 1 - M (coordinateVector 0) 3) / 2⟩ := by
  unfold ambientRotationDet
  rw [Matrix.det_fin_two]
  rfl

private lemma continuous_mk' {X : Type*} [TopologicalSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (⟨f x, g x⟩ : ℂ)) := by
  have : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => (f x : ℂ) + (g x : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp
  rw [this]
  exact (Complex.continuous_ofReal.comp hf).add
    ((Complex.continuous_ofReal.comp hg).mul continuous_const)

/-- The ambient determinant is continuous on the space of linear maps. -/
private lemma continuous_det :
    Continuous (fun M : Phase →L[ℝ] Phase => ambientRotationDet M) := by
  have hc : ∀ k i : Fin 4, Continuous fun M : Phase →L[ℝ] Phase => M (coordinateVector k) i :=
    fun k i => (continuous_apply i).comp (continuous_id.clm_apply continuous_const)
  simp only [ambientRotationDet_eq]
  refine ((continuous_mk' ?_ ?_).mul (continuous_mk' ?_ ?_)).sub
    ((continuous_mk' ?_ ?_).mul (continuous_mk' ?_ ?_)) <;>
    first
    | exact ((hc _ _).add (hc _ _)).div_const _
    | exact ((hc _ _).sub (hc _ _)).div_const _

private lemma det_id : ambientRotationDet (ContinuousLinearMap.id ℝ Phase) = 1 := by
  rw [ambientRotationDet_eq]
  apply Complex.ext <;> simp (config := { decide := true }) [coordinateVector]

private lemma const_of_two_pi_int {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b))
    (hint : ∀ t ∈ Set.Icc a b, ∃ k : ℤ, g t = k * (2 * Real.pi)) :
    g b = g a := by
  obtain ⟨k₁, hk₁⟩ := hint a ⟨le_rfl, hab⟩
  obtain ⟨k₂, hk₂⟩ := hint b ⟨hab, le_rfl⟩
  have hπ := Real.pi_pos
  have hodd : ∀ m n : ℤ, (m : ℝ) * (2 * Real.pi) ≠ n * (2 * Real.pi) + Real.pi := by
    intro m n h
    have h' : ((2 * (m - n) : ℤ) : ℝ) * Real.pi = 1 * Real.pi := by
      push_cast; linarith
    have h'' : ((2 * (m - n) : ℤ) : ℝ) = 1 := mul_right_cancel₀ hπ.ne' h'
    have : 2 * (m - n) = 1 := by exact_mod_cast h''
    omega
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · exfalso
    have hk : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast h
    have hmem : (k₁ : ℝ) * (2 * Real.pi) + Real.pi ∈ Set.Icc (g a) (g b) := by
      rw [hk₁, hk₂]
      constructor <;> nlinarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hab hg hmem
    obtain ⟨m, hm⟩ := hint t ht
    exact hodd m k₁ (hm ▸ hgt)
  · rw [hk₁, hk₂, h]
  · exfalso
    have hk : (k₂ : ℝ) + 1 ≤ k₁ := by exact_mod_cast h
    have hmem : (k₂ : ℝ) * (2 * Real.pi) + Real.pi ∈ Set.Icc (g b) (g a) := by
      rw [hk₁, hk₂]
      constructor <;> nlinarith
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hab hg hmem
    obtain ⟨m, hm⟩ := hint t ht
    exact hodd m k₂ (hm ▸ hgt)


/-! ### The totalized gradient -/

private lemma dot_cv (g : Phase) (k : Fin 4) : g ⬝ᵥ coordinateVector k = g k := by
  simp [dotProduct, coordinateVector]

private lemma sum_coord (w : Phase) : w = ∑ j, w j • coordinateVector j := by
  funext k
  fin_cases k <;> simp [coordinateVector]

private lemma fderiv_eq_dot (F : Phase → ℝ) (p w : Phase) :
    fderiv ℝ F p w = TangentialHessian.grad F p ⬝ᵥ w := by
  conv_lhs => rw [sum_coord w]
  simp [map_smul, TangentialHessian.grad, partialDerivative, dotProduct,
    Fin.sum_univ_four, mul_comm]

/-- Where the totalized gradient is nonzero, the function is differentiable. -/
private lemma differentiableAt_of_grad_ne_zero {F : Phase → ℝ} {s : Phase}
    (h : TangentialHessian.grad F s ≠ 0) : DifferentiableAt ℝ F s := by
  by_contra hd
  apply h
  funext i
  simp [TangentialHessian.grad, partialDerivative, fderiv_zero_of_not_differentiableAt hd]

private lemma norm_cv_le (k : Fin 4) : ‖coordinateVector k‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun m => ?_
  by_cases h : m = k <;> simp [coordinateVector, h]

private lemma norm_circle_le {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    ‖Real.cos t • coordinateVector i + Real.sin t • coordinateVector j‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun m => ?_
  by_cases hi : m = i
  · subst hi
    simp [coordinateVector, hij, Real.abs_cos_le_one]
  · by_cases hj : m = j
    · subst hj
      simp [coordinateVector, hi, Real.abs_sin_le_one]
    · simp [coordinateVector, hi, hj]

set_option maxHeartbeats 2000000 in
/-- **Symmetry of the derivative of a totalized gradient.** If the coordinate
gradient of an arbitrary function is differentiable at `p`, its derivative is
symmetric. Small loops in the plane of `e i, e j`, offset from `p` in a direction
where `L` does not vanish, consist of points where the gradient is nonzero, hence of
differentiability points; the function returns to its value around the loop, while the
affine model of the gradient contributes `π ε² ρ² (L e_i j - L e_j i)`. -/
theorem grad_deriv_symm {F : Phase → ℝ} {p : Phase} {L : Phase →L[ℝ] Phase}
    (hG : HasFDerivAt (TangentialHessian.grad F) L p) (i j : Fin 4) :
    L (coordinateVector j) i = L (coordinateVector i) j := by
  by_contra hne
  set G := TangentialHessian.grad F with hGdef
  set Δ := L (coordinateVector j) i - L (coordinateVector i) j with hΔ
  have hΔ0 : 0 < |Δ| := abs_pos.2 (sub_ne_zero.2 hne)
  have hij : i ≠ j := by rintro rfl; exact hne rfl
  -- a direction in which `L` does not vanish
  obtain ⟨d0, hd0n, hLd0⟩ : ∃ d0 : Phase, ‖d0‖ ≤ 1 ∧ L d0 ≠ 0 := by
    by_cases h1 : L (coordinateVector j) = 0
    · refine ⟨coordinateVector i, norm_cv_le i, fun h2 => hne ?_⟩
      rw [h1, h2]; rfl
    · exact ⟨coordinateVector j, norm_cv_le j, h1⟩
  set a := ‖L d0‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 hLd0
  set ρ := min 1 (a / (2 * (‖L‖ + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρL : ρ * ‖L‖ ≤ a / 2 := by
    have h1 : ρ ≤ a / (2 * (‖L‖ + 1)) := min_le_right _ _
    have h2 : a / (2 * (‖L‖ + 1)) * ‖L‖ ≤ a / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg L]
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans h2
  set η := min (|Δ| * ρ / 16) (a / 8) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηΔ : η ≤ |Δ| * ρ / 16 := min_le_left _ _
  have hηa : η ≤ a / 8 := min_le_right _ _
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 (hG.isLittleO.def hη0)
  -- the loop radius
  obtain ⟨ε, hε0, hεδ, hεG⟩ : ∃ ε : ℝ, 0 < ε ∧ 2 * ε < δ ∧
      (G p ≠ 0 → 2 * ε * (‖L‖ + η) < ‖G p‖) := by
    by_cases hGp : G p = 0
    · exact ⟨δ / 4, by positivity, by linarith, fun h => absurd hGp h⟩
    · have hGpos : 0 < ‖G p‖ := norm_pos_iff.2 hGp
      set N := ‖L‖ + η with hN
      have hN0 : 0 ≤ N := by positivity
      refine ⟨min (δ / 4) (‖G p‖ / (4 * (N + 1))), lt_min (by positivity) (by positivity),
        ?_, fun _ => ?_⟩
      · have := min_le_left (δ / 4) (‖G p‖ / (4 * (N + 1))); linarith
      · have h1 := min_le_right (δ / 4) (‖G p‖ / (4 * (N + 1)))
        have h2 : 2 * (‖G p‖ / (4 * (N + 1))) * N < ‖G p‖ := by
          rw [show 2 * (‖G p‖ / (4 * (N + 1))) * N = ‖G p‖ * (N / (2 * (N + 1))) by
            field_simp; ring]
          have h3 : N / (2 * (N + 1)) < 1 := by
            rw [div_lt_one (by positivity)]; linarith
          nlinarith
        calc 2 * min (δ / 4) (‖G p‖ / (4 * (N + 1))) * N
            ≤ 2 * (‖G p‖ / (4 * (N + 1))) * N := by gcongr
          _ < ‖G p‖ := h2
  -- the loop
  set w : ℝ → Phase := fun t => Real.cos t • coordinateVector i + Real.sin t • coordinateVector j
    with hw
  set c : ℝ → Phase := fun t => p + ε • (d0 + ρ • w t) with hc
  have hwn : ∀ t, ‖w t‖ ≤ 1 := fun t => norm_circle_le hij t
  have hcp : ∀ t, c t - p = ε • (d0 + ρ • w t) := fun t => by simp [hc]
  have hcn : ∀ t, ‖c t - p‖ ≤ 2 * ε := by
    intro t
    rw [hcp, norm_smul, Real.norm_of_nonneg hε0.le]
    have : ‖d0 + ρ • w t‖ ≤ 2 := by
      calc ‖d0 + ρ • w t‖ ≤ ‖d0‖ + ‖ρ • w t‖ := norm_add_le _ _
        _ = ‖d0‖ + ρ * ‖w t‖ := by rw [norm_smul, Real.norm_of_nonneg hρ0.le]
        _ ≤ 1 + 1 * 1 := by gcongr; exact hwn t
        _ = 2 := by norm_num
    nlinarith
  set R : ℝ → Phase := fun t => G (c t) - G p - L (c t - p) with hRdef
  have hR : ∀ t, ‖R t‖ ≤ η * (2 * ε) := by
    intro t
    have h := hδ (show dist (c t) p < δ by rw [dist_eq_norm]; linarith [hcn t])
    exact h.trans (by gcongr; exact hcn t)
  have hLc : ∀ t, L (c t - p) = ε • (L d0 + ρ • (Real.cos t • L (coordinateVector i) +
      Real.sin t • L (coordinateVector j))) := by
    intro t
    rw [hcp]
    simp [hw, map_add, map_smul]
  -- the gradient does not vanish on the loop
  have hGne : ∀ t, G (c t) ≠ 0 := by
    intro t h0
    have hsum : G p + L (c t - p) = -R t := by simp only [hRdef, h0]; abel
    have hRt := hR t
    by_cases hGp : G p = 0
    · rw [hGp, zero_add] at hsum
      have hlow : ε * (a / 2) ≤ ‖L (c t - p)‖ := by
        rw [hcp, map_smul, norm_smul, Real.norm_of_nonneg hε0.le]
        have : a / 2 ≤ ‖L (d0 + ρ • w t)‖ := by
          rw [map_add, map_smul]
          have h1 : ‖ρ • L (w t)‖ ≤ a / 2 := by
            rw [norm_smul, Real.norm_of_nonneg hρ0.le]
            calc ρ * ‖L (w t)‖ ≤ ρ * (‖L‖ * ‖w t‖) := by gcongr; exact L.le_opNorm _
              _ ≤ ρ * (‖L‖ * 1) := by gcongr; exact hwn t
              _ = ρ * ‖L‖ := by ring
              _ ≤ a / 2 := hρL
          have h2 := norm_sub_norm_le (L d0) (-(ρ • L (w t)))
          rw [sub_neg_eq_add, norm_neg] at h2
          linarith
        nlinarith
      rw [hsum, norm_neg] at hlow
      nlinarith
    · have h1 : ‖G p‖ ≤ ‖R t‖ + ‖L (c t - p)‖ := by
        have : G p = -R t - L (c t - p) := by rw [← hsum]; abel
        rw [this]
        calc ‖-R t - L (c t - p)‖ ≤ ‖-R t‖ + ‖L (c t - p)‖ := norm_sub_le _ _
          _ = ‖R t‖ + ‖L (c t - p)‖ := by rw [norm_neg]
      have h2 : ‖L (c t - p)‖ ≤ ‖L‖ * (2 * ε) :=
        (L.le_opNorm _).trans (by gcongr; exact hcn t)
      have h3 := hεG hGp
      nlinarith
  -- derivative of the loop
  have hcd : ∀ t, HasDerivAt c (ε • (ρ • (-Real.sin t • coordinateVector i +
      Real.cos t • coordinateVector j))) t := by
    intro t
    have h := (((((Real.hasDerivAt_cos t).smul_const (coordinateVector i)).add
      ((Real.hasDerivAt_sin t).smul_const (coordinateVector j))).const_smul ρ).const_add d0
      |>.const_smul ε).const_add p
    exact h
  -- derivative of `F ∘ c`
  have hfd : ∀ t, HasDerivAt (fun t => F (c t))
      (ε * (ρ * (-Real.sin t * G (c t) i + Real.cos t * G (c t) j))) t := by
    intro t
    have h := ((differentiableAt_of_grad_ne_zero (hGne t)).hasFDerivAt).comp_hasDerivAt t (hcd t)
    refine h.congr_deriv ?_
    rw [fderiv_eq_dot]
    simp [dotProduct_add, dotProduct_smul, dot_cv, smul_eq_mul]
    ring
  -- the affine model and its antiderivative
  set Hii := L (coordinateVector i) i with hHii
  set Hij := L (coordinateVector j) i with hHij
  set Hji := L (coordinateVector i) j with hHji
  set Hjj := L (coordinateVector j) j with hHjj
  set ai := G p i + ε * L d0 i with hai
  set aj := G p j + ε * L d0 j with haj
  set M : ℝ → ℝ := fun t => ε * ρ * (ai * Real.cos t + aj * Real.sin t)
    + ε ^ 2 * ρ ^ 2 * ((Hjj - Hii) * (Real.sin t * Real.sin t / 2)
      - Hij * (t / 2 - Real.sin t * Real.cos t / 2)
      + Hji * (t / 2 + Real.sin t * Real.cos t / 2)) with hM
  have hMd : ∀ t, HasDerivAt M (ε * ρ * (-Real.sin t * (G p i + L (c t - p) i)
      + Real.cos t * (G p j + L (c t - p) j))) t := by
    intro t
    have hs := Real.hasDerivAt_sin t
    have hcs := Real.hasDerivAt_cos t
    have hid := hasDerivAt_id t
    have h := ((((hcs.const_mul ai).add (hs.const_mul aj)).const_mul (ε * ρ)).add
      ((((hs.mul hs).div_const 2).const_mul (Hjj - Hii)).sub
        (((hid.div_const 2).sub ((hs.mul hcs).div_const 2)).const_mul Hij) |>.add
        (((hid.div_const 2).add ((hs.mul hcs).div_const 2)).const_mul Hji)
        |>.const_mul (ε ^ 2 * ρ ^ 2)))
    refine h.congr_deriv ?_
    rw [hLc t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hai, haj, hHii, hHij, hHji, hHjj]
    linear_combination (ε ^ 2 * ρ ^ 2 * (L (coordinateVector j) i - L (coordinateVector i) j) / 2) *
      Real.sin_sq_add_cos_sq t
  -- the remainder and the mean value bound
  set h : ℝ → ℝ := fun t => F (c t) - M t with hh
  have hhd : ∀ t, HasDerivAt h (ε * ρ * (-Real.sin t * R t i + Real.cos t * R t j)) t := by
    intro t
    refine ((hfd t).sub (hMd t)).congr_deriv ?_
    simp only [hRdef, Pi.sub_apply]
    ring
  have hbound : ∀ t, ‖ε * ρ * (-Real.sin t * R t i + Real.cos t * R t j)‖ ≤
      ε * ρ * (2 * (η * (2 * ε))) := by
    intro t
    have hi := (norm_le_pi_norm (R t) i).trans (hR t)
    have hj := (norm_le_pi_norm (R t) j).trans (hR t)
    rw [Real.norm_eq_abs] at hi hj ⊢
    rw [abs_mul, abs_of_pos (by positivity : 0 < ε * ρ)]
    gcongr
    calc |-Real.sin t * R t i + Real.cos t * R t j|
        ≤ |Real.sin t| * |R t i| + |Real.cos t| * |R t j| := by
          rw [show -Real.sin t * R t i = -(Real.sin t * R t i) by ring]
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_mul, abs_mul]
      _ ≤ 1 * (η * (2 * ε)) + 1 * (η * (2 * ε)) := by
          gcongr
          · exact Real.abs_sin_le_one t
          · exact Real.abs_cos_le_one t
      _ = 2 * (η * (2 * ε)) := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := h) (a := 0) (b := 2 * Real.pi)
    (fun t _ => (hhd t).hasDerivWithinAt) (fun t _ => hbound t) (2 * Real.pi)
    ⟨by positivity, le_rfl⟩
  -- evaluate the loop increment
  have hc2 : c (2 * Real.pi) = c 0 := by simp [hc, hw]
  have hval : h (2 * Real.pi) - h 0 = -(ε ^ 2 * ρ ^ 2 * Real.pi * (Hji - Hij)) := by
    simp only [hh, hM, hc2]
    simp
    ring
  rw [hval, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity :
    0 < ε ^ 2 * ρ ^ 2 * Real.pi)] at hmv
  have habs : |Hji - Hij| = |Δ| := by rw [hΔ, abs_sub_comm]
  rw [habs] at hmv
  have hπ := Real.pi_pos
  have key : ε ^ 2 * ρ * Real.pi * (ρ * |Δ|) ≤ ε ^ 2 * ρ * Real.pi * (8 * η) := by
    nlinarith
  have key2 : ρ * |Δ| ≤ 8 * η := le_of_mul_le_mul_left key (by positivity)
  nlinarith

/-! ### The derivative of a Hamiltonian field is infinitesimally symplectic -/

private lemma qI_qI (v : Phase) :
    TangentialHessian.qI.mulVec (TangentialHessian.qI.mulVec v) = -v := by
  rw [qI_apply, qI_apply]
  funext k
  fin_cases k <;> simp

private lemma qI_dot (x y : Phase) :
    TangentialHessian.qI.mulVec x ⬝ᵥ TangentialHessian.qI.mulVec y = x ⬝ᵥ y := by
  rw [qI_apply, qI_apply]
  simp [dotProduct, Fin.sum_univ_four]
  ring

private lemma hvf_eq_qI (F : Phase → ℝ) (s : Phase) :
    hamiltonianVectorField F s =
      TangentialHessian.qI.mulVec (TangentialHessian.grad F s) := by
  rw [qI_apply]
  funext i
  fin_cases i <;> rfl

/-- Multiplication by `qI` as a continuous linear map. -/
private noncomputable def qIL : Phase →L[ℝ] Phase :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3,
    -ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 1]

private lemma qIL_apply (v : Phase) : qIL v = TangentialHessian.qI.mulVec v := by
  rw [qI_apply]
  funext k
  fin_cases k <;> simp [qIL]

/-- For an arbitrary function `F`, the derivative of its Hamiltonian field (when it
exists; otherwise it is zero) is infinitesimally symplectic. -/
private lemma hvf_hamiltonian (F : Phase → ℝ) (p a b : Phase) :
    fderiv ℝ (hamiltonianVectorField F) p a ⬝ᵥ TangentialHessian.qI.mulVec b +
      a ⬝ᵥ TangentialHessian.qI.mulVec (fderiv ℝ (hamiltonianVectorField F) p b) = 0 := by
  by_cases hd : DifferentiableAt ℝ (hamiltonianVectorField F) p
  · set A := fderiv ℝ (hamiltonianVectorField F) p with hA
    have hgrad : TangentialHessian.grad F = fun s => (-qIL) (hamiltonianVectorField F s) := by
      funext s
      rw [ContinuousLinearMap.neg_apply, qIL_apply, hvf_eq_qI, qI_qI, neg_neg]
    have hG : HasFDerivAt (TangentialHessian.grad F) ((-qIL).comp A) p := by
      rw [hgrad]
      exact (-qIL).hasFDerivAt.comp p hd.hasFDerivAt
    set L := (-qIL).comp A with hL
    have hAL : ∀ w, A w = TangentialHessian.qI.mulVec (L w) := by
      intro w
      rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, qIL_apply,
        Matrix.mulVec_neg, qI_qI, neg_neg]
    have hsym := grad_deriv_symm hG
    have hexp : ∀ w, L w = fun k => ∑ l, w l * L (coordinateVector l) k := by
      intro w
      funext k
      conv_lhs => rw [sum_coord w]
      simp [map_sum, map_smul, Finset.sum_apply]
    rw [hAL a, hAL b, qI_dot, qI_qI, dotProduct_neg, hexp a, hexp b]
    have h01 := hsym 0 1
    have h02 := hsym 0 2
    have h03 := hsym 0 3
    have h12 := hsym 1 2
    have h13 := hsym 1 3
    have h23 := hsym 2 3
    simp only [dotProduct, Fin.sum_univ_four]
    rw [h01, h02, h03, h12, h13, h23]
    ring
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

/-! ### The variational flow is symplectic -/

private lemma symp_flow {F : Phase → ℝ} {x : ℝ → Phase} {Y : ℝ → (Phase →L[ℝ] Phase)}
    (hY : IsHamiltonianVariationalSolution F x Y) :
    ∀ t : ℝ, ∀ u v : Phase,
      Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = u ⬝ᵥ TangentialHessian.qI.mulVec v := by
  obtain ⟨hY0, hYd⟩ := hY
  have hvd : ∀ s w, HasDerivAt (fun τ => Y τ w)
      (fderiv ℝ (hamiltonianVectorField F) (x s) (Y s w)) s := by
    intro s w
    have h := (hYd s).clm_apply (hasDerivAt_const s w)
    refine h.congr_deriv ?_
    simp
  intro t u v
  set f : ℝ → ℝ := fun τ => Y τ u ⬝ᵥ TangentialHessian.qI.mulVec (Y τ v) with hf
  have hderiv : ∀ s, HasDerivAt f 0 s := by
    intro s
    have hc := hasDerivAt_pi.mp (hvd s u)
    have hd := hasDerivAt_pi.mp (hvd s v)
    have h := ((((hc 0).mul (hd 2)).add ((hc 1).mul (hd 3))).sub ((hc 2).mul (hd 0))).sub
      ((hc 3).mul (hd 1))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => ?_)
    · have hH := hvf_hamiltonian F (x s) (Y s u) (Y s v)
      rw [omegaQ, omegaQ] at hH
      linear_combination hH
    · simp only [hf, omegaQ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hc := is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0
  rw [show Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = f t from rfl, hc]
  simp [hf, hY0]

/-! ### Angles -/

private lemma same_angle_c {ρ ρ' θ θ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (h : (⟨ρ * Real.cos θ, ρ * Real.sin θ⟩ : ℂ) = ⟨ρ' * Real.cos θ', ρ' * Real.sin θ'⟩) :
    ∃ n : ℤ, θ - θ' = n * (2 * Real.pi) := by
  have h0 : ρ * Real.cos θ = ρ' * Real.cos θ' := congrArg Complex.re h
  have h1 : ρ * Real.sin θ = ρ' * Real.sin θ' := congrArg Complex.im h
  have a := Real.cos_sq_add_sin_sq θ
  have b := Real.cos_sq_add_sin_sq θ'
  have hsq : ρ ^ 2 = ρ' ^ 2 := by
    calc ρ ^ 2 = (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 := by
          linear_combination (-ρ ^ 2) * a
      _ = (ρ' * Real.cos θ') ^ 2 + (ρ' * Real.sin θ') ^ 2 := by rw [h0, h1]
      _ = ρ' ^ 2 := by linear_combination ρ' ^ 2 * b
  have hρρ : ρ = ρ' := by nlinarith
  subst hρρ
  have hc : Real.cos θ = Real.cos θ' := mul_left_cancel₀ hρ.ne' h0
  have hs : Real.sin θ = Real.sin θ' := mul_left_cancel₀ hρ.ne' h1
  have hcos : Real.cos (θ - θ') = 1 := by
    rw [Real.cos_sub, hc, hs]; linear_combination b
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
  exact ⟨n, hn.symm⟩

private lemma polar_self (z : ℂ) (hz : z ≠ 0) :
    z = ⟨‖z‖ * Real.cos (Complex.arg z), ‖z‖ * Real.sin (Complex.arg z)⟩ := by
  apply Complex.ext
  · simp [Complex.norm_mul_cos_arg]
  · simp [Complex.norm_mul_sin_arg]

/-! ### The defect bound -/

theorem solution
    (F : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hper : ∀ t : ℝ, x (t + T) = x t)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (hcocycle : ∀ t : ℝ, Y (t + T) = (Y t).comp (Y T))
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ a : ℝ, α (a + T) - α a ≤ α T - α 0 + 2 * Real.pi := by
  have hsymp := symp_flow hY
  obtain ⟨hY0, hYd⟩ := hY
  obtain ⟨hαc, hαp⟩ := hα
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun t => (hYd t).continuousAt
  set d : ℝ → ℂ := fun t => ambientRotationDet (Y t) with hd
  have hdc : Continuous d := continuous_det.comp hYc
  set Q : ℝ → ℂ := fun a => d (a + T) * (starRingEnd ℂ) (d a) * (starRingEnd ℂ) (d T) with hQ
  have hQslit : ∀ a, Q a ∈ Complex.slitPlane := by
    intro a
    have h := ambient_rotation_product_slit (Y a) (Y T) (hsymp a) (hsymp T)
    simpa [hQ, hd, hcocycle a] using h
  have hQc : Continuous Q := by
    simp only [hQ]
    exact ((hdc.comp (continuous_add_const T)).mul (Complex.continuous_conj.comp hdc)).mul
      continuous_const
  have hd0 : d 0 = 1 := by simp [hd, hY0, det_id]
  -- the angle relation, up to multiples of `2π`
  have hint : ∀ a, ∃ k : ℤ,
      (α (a + T) - α a - α T + α 0) - Complex.arg (Q a) = k * (2 * Real.pi) := by
    intro a
    obtain ⟨ρ1, hρ1, h1⟩ := hαp (a + T)
    obtain ⟨ρ2, hρ2, h2⟩ := hαp a
    obtain ⟨ρ3, hρ3, h3⟩ := hαp T
    obtain ⟨ρ0, hρ0, h0⟩ := hαp 0
    have hQa : Q a = ⟨ρ1 * ρ2 * ρ3 * Real.cos (α (a + T) - α a - α T),
        ρ1 * ρ2 * ρ3 * Real.sin (α (a + T) - α a - α T)⟩ := by
      simp only [hQ, hd]
      rw [h1, h2, h3]
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, Real.cos_sub, Real.sin_sub] <;> ring
    have hne : Q a ≠ 0 := Complex.slitPlane_ne_zero (hQslit a)
    obtain ⟨k, hk⟩ := same_angle_c (by positivity) (norm_pos_iff.2 hne)
      (hQa.symm.trans (polar_self (Q a) hne))
    have h00 : (⟨ρ0 * Real.cos (α 0), ρ0 * Real.sin (α 0)⟩ : ℂ) =
        ⟨1 * Real.cos 0, 1 * Real.sin 0⟩ := by
      rw [← h0, show ambientRotationDet (Y 0) = 1 from hd0]
      apply Complex.ext <;> simp
    obtain ⟨m, hm⟩ := same_angle_c hρ0 one_pos h00
    refine ⟨k + m, ?_⟩
    push_cast
    linarith
  -- the difference is continuous and integer-valued, hence zero
  set g : ℝ → ℝ := fun a => (α (a + T) - α a - α T + α 0) - Complex.arg (Q a) with hg
  have hgc : Continuous g := by
    simp only [hg]
    have harg : Continuous fun a => Complex.arg (Q a) :=
      continuous_iff_continuousAt.2 fun a =>
        (Complex.continuousAt_arg (hQslit a)).comp hQc.continuousAt
    exact ((((hαc.comp (continuous_add_const T)).sub hαc).sub continuous_const).add
      continuous_const).sub harg
  have hg0 : g 0 = 0 := by
    have hQ0 : Q 0 = ((Complex.normSq (d T) : ℝ) : ℂ) := by
      simp only [hQ, zero_add, hd0, map_one, mul_one]
      exact Complex.mul_conj (d T)
    simp only [hg, zero_add, hQ0, Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg _)]
    ring
  intro a
  have hga : g a = 0 := by
    rcases le_total 0 a with ha | ha
    · have h := const_of_two_pi_int (g := g) ha hgc.continuousOn (fun t _ => hint t)
      rw [h, hg0]
    · have h := const_of_two_pi_int (g := g) ha hgc.continuousOn (fun t _ => hint t)
      rw [← h, hg0]
  have hle := Complex.arg_le_pi (Q a)
  have hga' : (α (a + T) - α a - α T + α 0) - Complex.arg (Q a) = 0 := hga
  linarith [Real.pi_pos]
