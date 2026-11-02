-- Prove2me | solution 1 for FiniteEnergyPlane.exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T23:07:17.800293+00:00
-- url     : https://prove2.me/submissions/b72c7530-65ea-465d-931d-28f48ff3fab4

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_eigenEq_fundamentalSolution_apply
import Theorems.Thm_FiniteEnergyPlane_eq_one_of_im_conj_mul_apply_le_zero
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_of_fundamentalSolution_apply_one
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_ne_zero_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_im_conj_mul_of_eigenEq
import Mathlib



namespace FiniteEnergyPlane

open Matrix Filter Topology ComplexConjugate
open scoped Real ContDiff

/-- `ℂ → ℝ²`, the inverse of `vecToC`. -/
noncomputable def wmOfC (z : ℂ) : CauchyRiemannIndex.Vec 1 :=
  z.re • EuclideanSpace.single (Sum.inl 0) 1 + z.im • EuclideanSpace.single (Sum.inr 0) 1

theorem wm_vecToC_ofC (z : ℂ) : vecToC (wmOfC z) = z := by
  apply Complex.ext <;> simp [vecToC, wmOfC, EuclideanSpace.single_apply]

theorem wm_vecToC_inj {v w : CauchyRiemannIndex.Vec 1} (h : vecToC v = vecToC w) : v = w := by
  have h1 : v (Sum.inl 0) = w (Sum.inl 0) := congrArg Complex.re h
  have h2 : v (Sum.inr 0) = w (Sum.inr 0) := congrArg Complex.im h
  ext i
  rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> assumption

theorem wm_vecToC_add (v w : CauchyRiemannIndex.Vec 1) : vecToC (v + w) = vecToC v + vecToC w :=
  Complex.ext (by simp [vecToC]) (by simp [vecToC])

theorem wm_vecToC_smul (c : ℝ) (v : CauchyRiemannIndex.Vec 1) :
    vecToC (c • v) = (c : ℂ) * vecToC v :=
  Complex.ext (by simp [vecToC]) (by simp [vecToC])

/-- `vecToC` as a continuous `ℝ`-linear map. -/
noncomputable def wmVecToCL : CauchyRiemannIndex.Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := wm_vecToC_add
      map_smul' := fun c v => by rw [wm_vecToC_smul, RingHom.id_apply, Complex.real_smul] }

/-- An extremal angle displacement `2πk` gives an eigenfunction of winding `k`. -/
theorem exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) Ψ)
    (θ : ℝ → ℝ → ℝ)
    (hne : ∀ (t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (Ψ t) v ≠ 0)
    (hθc : ∀ α, Continuous (θ α)) (hθ0 : ∀ α, θ α 0 = α)
    (hrep : ∀ (α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) →
      ∀ t, vecToC (Matrix.toEuclideanLin (Ψ t) v) =
        (‖vecToC (Matrix.toEuclideanLin (Ψ t) v)‖ : ℂ) * Complex.exp (θ α t * Complex.I))
    (hD : Continuous fun α => θ α 1) (k : ℤ) (α₀ : ℝ) (hα : θ α₀ 1 - α₀ = 2 * π * k)
    (hext : (∀ β, θ β 1 - β ≤ 2 * π * k) ∨ (∀ β, 2 * π * k ≤ θ β 1 - β)) :
    ∃ e, IsLoopEigen Sinf μ e ∧ HasLoopEigenWind Sinf μ k ∧
      vecToC (e 0) = Complex.exp (α₀ * Complex.I) := by
  have hpi := Real.pi_pos
  have hvne : ∀ v : CauchyRiemannIndex.Vec 1, vecToC v ≠ 0 → v ≠ 0 := by
    intro v hv h; apply hv; rw [h]; exact Complex.ext (by simp [vecToC]) (by simp [vecToC])
  have hCne : ∀ v : CauchyRiemannIndex.Vec 1, v ≠ 0 → vecToC v ≠ 0 := by
    intro v hv h; apply hv; apply wm_vecToC_inj; rw [h]
    exact Complex.ext (by simp [vecToC]) (by simp [vecToC])
  set u := Complex.exp (α₀ * Complex.I) with hudef
  set v := wmOfC u with hvdef
  have hvu : vecToC v = u := wm_vecToC_ofC u
  have hv0 : v ≠ 0 := hvne v (by rw [hvu]; exact Complex.exp_ne_zero _)
  -- the time-one map on `ℂ`
  have hofC_add : ∀ z w, wmOfC (z + w) = wmOfC z + wmOfC w := fun z w =>
    wm_vecToC_inj (by rw [wm_vecToC_add, wm_vecToC_ofC, wm_vecToC_ofC, wm_vecToC_ofC])
  have hofC_smul : ∀ (c : ℝ) z, wmOfC (c • z) = c • wmOfC z := fun c z =>
    wm_vecToC_inj (by rw [wm_vecToC_smul, wm_vecToC_ofC, wm_vecToC_ofC, Complex.real_smul])
  let L : ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun z => vecToC (Matrix.toEuclideanLin (Ψ 1) (wmOfC z))
      map_add' := fun z w => by rw [hofC_add, map_add, wm_vecToC_add]
      map_smul' := fun c z => by
        rw [hofC_smul, map_smul, wm_vecToC_smul, RingHom.id_apply, Complex.real_smul] }
  have hLapp : ∀ z, L z = vecToC (Matrix.toEuclideanLin (Ψ 1) (wmOfC z)) := fun z => rfl
  -- `L` preserves `ω`
  have hω : ∀ z w, (conj (L z) * L w).im = (conj z * w).im := by
    intro z w
    obtain ⟨hdz, hez⟩ := eigenEq_fundamentalSolution_apply Sinf μ Ψ hΨ (wmOfC z)
    obtain ⟨hdw, hew⟩ := eigenEq_fundamentalSolution_apply Sinf μ Ψ hΨ (wmOfC w)
    have hd := fun t => hasDerivAt_im_conj_mul_of_eigenEq Sinf hSinf.2.2 hdz hez hdw hew t
    simp only [sub_self, zero_mul] at hd
    have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) 1 0
    simp only [hΨ.1, Matrix.toLpLin_one, LinearMap.id_apply, wm_vecToC_ofC] at hc
    rw [hLapp, hLapp]
    exact hc
  -- `L u = c u`
  set c := ‖vecToC (Matrix.toEuclideanLin (Ψ 1) v)‖ with hcdef
  have hc : 0 < c := norm_pos_iff.2 (hCne _ (hne 1 v hv0))
  have hθ1 : θ α₀ 1 = α₀ + (k : ℝ) * (2 * π) := by linarith
  have hexpk : Complex.exp (θ α₀ 1 * Complex.I) = u := by
    rw [hθ1, hudef]
    have h1 : Complex.exp ((((k : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I) = 1 :=
      Complex.exp_eq_one_iff.2 ⟨k, by push_cast; ring⟩
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, h1, mul_one]
  have hLu : L u = c * u := by
    rw [hLapp, ← hvdef, hrep α₀ v hvu 1, hexpk]
  -- sign of `ω(e^{iβ}, L e^{iβ})` near `α₀`
  have hform : ∀ β : ℝ, (conj (Complex.exp ((β : ℂ) * Complex.I)) *
      L (Complex.exp ((β : ℂ) * Complex.I))).im =
        ‖L (Complex.exp ((β : ℂ) * Complex.I))‖ * Real.sin (θ β 1 - β) := by
    intro β
    have h := hrep β (wmOfC (Complex.exp (β * Complex.I))) (wm_vecToC_ofC _) 1
    rw [← hLapp] at h
    conv_lhs => rw [h]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_left_comm,
      ← Complex.exp_add, Complex.im_ofReal_mul]
    congr 1
    rw [show (β : ℂ) * -Complex.I + (θ β 1 : ℂ) * Complex.I = ((θ β 1 - β : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.exp_ofReal_mul_I_im _
  have hDα : ContinuousAt (fun β => θ β 1 - β) α₀ := (hD.sub continuous_id).continuousAt
  have hsign : (∀ᶠ β : ℝ in 𝓝 α₀, (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im ≤ 0) ∨
      (∀ᶠ β : ℝ in 𝓝 α₀, 0 ≤ (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im) := by
    rcases hext with hmax | hmin
    · left
      have hev : ∀ᶠ β in 𝓝 α₀, 2 * π * k - π < θ β 1 - β :=
        continuousAt_const.eventually_lt hDα (by rw [hα]; linarith)
      filter_upwards [hev] with β hβ
      rw [hform]
      refine mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) ?_
      have h1 := hmax β
      rw [← Real.sin_sub_int_mul_two_pi (θ β 1 - β) k]
      have : 0 ≤ Real.sin (-(θ β 1 - β - k * (2 * π))) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
      rw [Real.sin_neg] at this
      linarith
    · right
      have hev : ∀ᶠ β in 𝓝 α₀, θ β 1 - β < 2 * π * k + π :=
        hDα.eventually_lt continuousAt_const (by rw [hα]; linarith)
      filter_upwards [hev] with β hβ
      rw [hform]
      refine mul_nonneg (norm_nonneg _) ?_
      have h1 := hmin β
      rw [← Real.sin_sub_int_mul_two_pi (θ β 1 - β) k]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  have hc1 : c = 1 := eq_one_of_im_conj_mul_apply_le_zero hω hc hLu hsign
  have hfix : Matrix.toEuclideanLin (Ψ 1) v = v := by
    apply wm_vecToC_inj
    have := hLu
    rw [hLapp, ← hvdef, hc1, Complex.ofReal_one, one_mul] at this
    rw [this, hvu]
  -- the eigenfunction
  have he := isLoopEigen_of_fundamentalSolution_apply_one Sinf hSinf hSinf' μ Ψ hΨ v hv0 hfix
  set e := fun t => Matrix.toEuclideanLin (Ψ t) v with hedef
  have hwind : HasLoopWind (fun t => vecToC (e t)) k := by
    refine ⟨wmVecToCL.continuous.comp he.1.continuous, fun t => ?_,
      fun t => hCne _ (hne t v hv0), θ α₀, hθc α₀, hrep α₀ v hvu, ?_⟩
    · show vecToC (e (t + 1)) = vecToC (e t)
      rw [he.2.1 t]
    · rw [hθ0]; linarith
  obtain ⟨-, k', hk'⟩ := isLoopEigen_ne_zero_hasLoopEigenWind Sinf hSinf hSinf' μ e he
  have hkk : k' = k := hasLoopWind_unique (hk'.2 e he) hwind
  subst hkk
  refine ⟨e, he, hk', ?_⟩
  simp only [hedef, hΨ.1, Matrix.toLpLin_one, LinearMap.id_apply, hvu]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology
open scoped Real ContDiff

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) Ψ)
    (θ : ℝ → ℝ → ℝ)
    (hne : ∀ (t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (Ψ t) v ≠ 0)
    (hθc : ∀ α, Continuous (θ α)) (hθ0 : ∀ α, θ α 0 = α)
    (hrep : ∀ (α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) →
      ∀ t, vecToC (Matrix.toEuclideanLin (Ψ t) v) =
        (‖vecToC (Matrix.toEuclideanLin (Ψ t) v)‖ : ℂ) * Complex.exp (θ α t * Complex.I))
    (hD : Continuous fun α => θ α 1) (k : ℤ) (α₀ : ℝ) (hα : θ α₀ 1 - α₀ = 2 * π * k)
    (hext : (∀ β, θ β 1 - β ≤ 2 * π * k) ∨ (∀ β, 2 * π * k ≤ θ β 1 - β)) :
    ∃ e, IsLoopEigen Sinf μ e ∧ HasLoopEigenWind Sinf μ k ∧
      vecToC (e 0) = Complex.exp (α₀ * Complex.I) :=
  exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle_aux Sinf hSinf hSinf' μ Ψ hΨ θ hne hθc hθ0 hrep hD k α₀ hα hext
