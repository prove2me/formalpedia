-- Prove2me | solution 1 for CarrollGR.metric_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T19:15:56.14476+00:00
-- url     : https://prove2.me/submissions/c6f4f58f-c935-42a0-bf73-0568c6430526

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! ff699ea8 CarrollGR.metric_compatibility.
g symmetric near x (Lorentzian ⇒ symmetric), so ∂_c g_{ab} = ∂_c g_{ba}; det g ≠ 0.
Lower: Σ_l Γ^l_{σμ} g_{lν} = ½(∂_σ g_{μν} + ∂_μ g_{νσ} - ∂_ν g_{σμ}) by g g⁻¹ = 1 (lower_alg).
Upper: g⁻¹ = det⁻¹·adj is differentiable at x; differentiating g⁻¹ g = 1 (constant near x)
gives ∂g⁻¹ = -g⁻¹ (∂g) g⁻¹ (pd_inv); the two Γ·g⁻¹ terms sum to g⁻¹ (∂g) g⁻¹ (upper_alg). -/

set_option autoImplicit false

open scoped ContDiff

namespace CGRBuild

open CarrollGR Matrix

theorem lor_det_ne {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) : M.det ≠ 0 := by
  obtain ⟨P, _, h⟩ := hM
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  intro h0
  rw [h0] at h2
  simp [minkowskiEta, Matrix.det_diagonal, Fin.prod_univ_four] at h2

theorem lor_symm {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) : Mᵀ = M := by
  obtain ⟨P, hP, h⟩ := hM
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  have hPtu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det Pᵀ).mpr (by rw [Matrix.det_transpose]; exact hP)
  have ht : Pᵀ * Mᵀ * P = minkowskiEta := by
    have h' := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
    rw [Matrix.mul_assoc, h']
    simp [minkowskiEta, Matrix.diagonal_transpose]
  have e : Pᵀ * Mᵀ * P = Pᵀ * M * P := by rw [ht, h]
  exact hPtu.mul_left_cancel (hPu.mul_right_cancel e)

theorem lor_symm' {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) (a b : Fin 4) :
    M a b = M b a := by
  have h := congrFun (congrFun (lor_symm hM) b) a
  rw [Matrix.transpose_apply] at h
  exact h

theorem lor_inv_symm' {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) (a b : Fin 4) :
    M⁻¹ a b = M⁻¹ b a := by
  have hs : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, lor_symm hM]
  have h := congrFun (congrFun hs b) a
  rw [Matrix.transpose_apply] at h
  exact h

theorem pd_symm {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (ρ a b : Fin 4) :
    partialD ρ (fun y => g y a b) x = partialD ρ (fun y => g y b a) x := by
  have hev : (fun y => g y a b) =ᶠ[nhds x] (fun y => g y b a) := by
    filter_upwards [hg.1.mem_nhds hx] with y hy
    exact lor_symm' (hg.2.2 y hy) a b
  unfold partialD
  rw [hev.fderiv_eq]

theorem pd_mul {f h : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    partialD i (fun y => f y * h y) x = partialD i f x * h x + f x * partialD i h x := by
  simp [partialD, fderiv_fun_mul hf hh]
  ring

theorem pd_sum {F : Fin 4 → Coord → ℝ} {x : Coord} (h : ∀ k, DifferentiableAt ℝ (F k) x)
    (i : Fin 4) :
    partialD i (fun y => ∑ k, F k y) x = ∑ k, partialD i (F k) x := by
  simp [partialD, fderiv_fun_sum (fun k _ => h k)]

theorem gdiff {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (a b : Fin 4) : DifferentiableAt ℝ (fun y => g y a b) x :=
  ((hg.2.1 a b).contDiffAt (hg.1.mem_nhds hx)).differentiableAt (by simp)

theorem dAt_det {A : Coord → Matrix (Fin 4) (Fin 4) ℝ} {x : Coord}
    (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    DifferentiableAt ℝ (fun y => (A y).det) x := by
  simp_rw [Matrix.det_apply']
  fun_prop

theorem dAt_inv {A : Coord → Matrix (Fin 4) (Fin 4) ℝ} {x : Coord}
    (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (hd : (A x).det ≠ 0) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹ i j) x := by
  have hadj : DifferentiableAt ℝ (fun y => (A y).adjugate i j) x := by
    simp_rw [Matrix.adjugate_apply]
    apply dAt_det
    intro a b
    by_cases hab : a = j
    · subst hab; simp only [Matrix.updateRow_self]; exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hab]; exact h a b
  have e : (fun y => (A y)⁻¹ i j) = fun y => ((A y).det)⁻¹ * (A y).adjugate i j := by
    funext y
    simp [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [e]
  exact ((dAt_det h).inv hd).mul hadj

theorem pd_inv {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (μ ρ a : Fin 4) :
    partialD μ (fun y => (g y)⁻¹ ρ a) x
      = -∑ σ, (∑ b, (g x)⁻¹ ρ b * partialD μ (fun y => g y b σ) x) * (g x)⁻¹ σ a := by
  have hu : ∀ y ∈ U, IsUnit (g y).det :=
    fun y hy => isUnit_iff_ne_zero.mpr (lor_det_ne (hg.2.2 y hy))
  have hgd := gdiff hg hx
  have hid : ∀ i j, DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x :=
    dAt_inv hgd (lor_det_ne (hg.2.2 x hx))
  have hcon : ∀ D : Fin 4 → ℝ, ∑ σ, (∑ b, D b * g x b σ) * (g x)⁻¹ σ a = D a := by
    intro D
    have e : ((D ᵥ* g x) ᵥ* (g x)⁻¹) a = ∑ σ, (∑ b, D b * g x b σ) * (g x)⁻¹ σ a := rfl
    rw [← e, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hu x hx), Matrix.vecMul_one]
  have hD : ∀ σ, ∑ b, partialD μ (fun y => (g y)⁻¹ ρ b) x * g x b σ
      = -∑ b, (g x)⁻¹ ρ b * partialD μ (fun y => g y b σ) x := by
    intro σ
    have hconst : (fun y => ∑ b, (g y)⁻¹ ρ b * g y b σ)
        =ᶠ[nhds x] fun _ => (1 : Matrix (Fin 4) (Fin 4) ℝ) ρ σ := by
      filter_upwards [hg.1.mem_nhds hx] with y hy
      have e : ∑ b, (g y)⁻¹ ρ b * g y b σ = ((g y)⁻¹ * g y) ρ σ := rfl
      rw [e, Matrix.nonsing_inv_mul _ (hu y hy)]
    have h0 : partialD μ (fun y => ∑ b, (g y)⁻¹ ρ b * g y b σ) x = 0 := by
      unfold partialD
      rw [hconst.fderiv_eq]
      simp
    rw [pd_sum (F := fun b y => (g y)⁻¹ ρ b * g y b σ) (fun b => (hid ρ b).mul (hgd b σ))] at h0
    have h1 : ∀ b, partialD μ (fun y => (g y)⁻¹ ρ b * g y b σ) x
        = partialD μ (fun y => (g y)⁻¹ ρ b) x * g x b σ
          + (g x)⁻¹ ρ b * partialD μ (fun y => g y b σ) x :=
      fun b => pd_mul (hid ρ b) (hgd b σ) μ
    simp only [h1, Finset.sum_add_distrib] at h0
    linarith
  rw [← hcon (fun b => partialD μ (fun y => (g y)⁻¹ ρ b) x), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hD σ]
  ring

theorem lower_alg (G Gi : Matrix (Fin 4) (Fin 4) ℝ) (hGG : G * Gi = 1)
    (hG : ∀ a b, G a b = G b a) (D : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hD : ∀ c a b, D c a b = D c b a) (σ μ ν : Fin 4) :
    D σ μ ν - ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi l ρ * (D σ μ ρ + D μ ρ σ - D ρ σ μ)) * G l ν
      - ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi l ρ * (D σ ν ρ + D ν ρ σ - D ρ σ ν)) * G μ l = 0 := by
  have hc : ∀ (E : Fin 4 → ℝ) (a : Fin 4),
      ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi l ρ * E ρ) * G a l = (1 / 2 : ℝ) * E a := by
    intro E a
    have h : (G *ᵥ (Gi *ᵥ E)) a = ∑ e, G a e * ∑ d, Gi e d * E d := rfl
    rw [Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec] at h
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have h1 : ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi l ρ * (D σ μ ρ + D μ ρ σ - D ρ σ μ)) * G l ν
      = ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi l ρ * (D σ μ ρ + D μ ρ σ - D ρ σ μ)) * G ν l :=
    Finset.sum_congr rfl fun l _ => by rw [hG l ν]
  rw [h1, hc (fun ρ => D σ μ ρ + D μ ρ σ - D ρ σ μ) ν,
    hc (fun ρ => D σ ν ρ + D ν ρ σ - D ρ σ ν) μ]
  rw [hD σ ν μ, hD ν μ σ, hD μ ν σ]
  ring

theorem upper_alg (Gi : Matrix (Fin 4) (Fin 4) ℝ) (D : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hG : ∀ a b, Gi a b = Gi b a) (hD : ∀ c a b, D c a b = D c b a) (σ μ ν : Fin 4) :
    -∑ ρ, (∑ b, Gi μ b * D σ b ρ) * Gi ρ ν
      + ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi μ ρ * (D σ l ρ + D l ρ σ - D ρ σ l)) * Gi l ν
      + ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi ν ρ * (D σ l ρ + D l ρ σ - D ρ σ l)) * Gi μ l = 0 := by
  have e1 : ∑ ρ, (∑ b, Gi μ b * D σ b ρ) * Gi ρ ν
      = ∑ a, ∑ b, Gi μ a * D σ a b * Gi b ν := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  have e2 : ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi μ ρ * (D σ l ρ + D l ρ σ - D ρ σ l)) * Gi l ν
      = ∑ a, ∑ b, (1 / 2 : ℝ) * (Gi μ a * (D σ b a + D b a σ - D a σ b)) * Gi b ν := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have e3 : ∑ l, (1 / 2 : ℝ) * (∑ ρ, Gi ν ρ * (D σ l ρ + D l ρ σ - D ρ σ l)) * Gi μ l
      = ∑ a, ∑ b, (1 / 2 : ℝ) * (Gi ν b * (D σ a b + D a b σ - D b σ a)) * Gi μ a := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [e1, e2, e3, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hG ν b, hD σ b a, hD b a σ, hD a b σ]
  ring

theorem mc_main (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    covDerivLower2 g g σ μ ν x = 0 ∧ covDerivUpper2 g (invMetric g) σ μ ν x = 0 := by
  have hL := hg.2.2 x hx
  have hGG : g x * (g x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (lor_det_ne hL))
  have hD : ∀ c a b, partialD c (fun y => g y a b) x = partialD c (fun y => g y b a) x :=
    fun c a b => pd_symm hg hx c a b
  constructor
  · unfold covDerivLower2 christoffel invMetric
    exact lower_alg (g x) (g x)⁻¹ hGG (lor_symm' hL)
      (fun c a b => partialD c (fun y => g y a b) x) hD σ μ ν
  · unfold covDerivUpper2 christoffel
    simp only [invMetric]
    rw [pd_inv hg hx σ μ ν]
    exact upper_alg (g x)⁻¹ (fun c a b => partialD c (fun y => g y a b) x)
      (lor_inv_symm' hL) hD σ μ ν

end CGRBuild

open CarrollGR in open scoped ContDiff in
theorem solution (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    covDerivLower2 g g σ μ ν x = 0 ∧ covDerivUpper2 g (invMetric g) σ μ ν x = 0 := by
  exact CGRBuild.mc_main g U hg x hx σ μ ν
