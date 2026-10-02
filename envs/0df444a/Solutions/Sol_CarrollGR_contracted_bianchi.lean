-- Prove2me | solution 1 for CarrollGR.contracted_bianchi
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:19:44.677985+00:00
-- url     : https://prove2.me/submissions/3b9d16f0-5e9b-4df0-b674-47333af106e0

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 52eaf064 CarrollGR.contracted_bianchi (built on the 6a74678a Bianchi lemmas).
Pair symmetry R_{μνρσ} = R_{ρσμν} on U turns the target into the antisymmetrized derivative
of R_{ρσ·· } in the last pair; by metric compatibility ∇_l R_{ρσμν} = g_{ρk} B^k_{σ l μ ν},
where B is the (1,3) covariant derivative of the Riemann tensor, and the cyclic sum of B
vanishes (symmetric second derivatives of Γ, torsion-freeness, Jacobi). -/

set_option autoImplicit false

open scoped ContDiff

namespace CBBuild

open CarrollGR Matrix

/-! ### Algebraic cores -/

set_option maxHeartbeats 4000000 in
theorem core_alg (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (dG : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ddG : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hΓ : ∀ k a b, Γ k a b = Γ k b a) (hdG : ∀ l k a b, dG l k a b = dG l k b a)
    (hdd1 : ∀ l m k a b, ddG l m k a b = ddG m l k a b)
    (hdd2 : ∀ l m k a b, ddG l m k a b = ddG l m k b a)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ k s m n, R k s m n = dG m k s n - dG n k s m
      + ∑ a, (Γ k m a * Γ a s n - Γ k n a * Γ a s m))
    (dR : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdR : ∀ l k s m n, dR l k s m n = ddG l m k s n - ddG l n k s m
      + ∑ a, (dG l k m a * Γ a s n + Γ k m a * dG l a s n
        - (dG l k n a * Γ a s m + Γ k n a * dG l a s m)))
    (B : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hB : ∀ l k s m n, B l k s m n = dR l k s m n + ∑ a, Γ k l a * R a s m n
      - ∑ a, Γ a l s * R k a m n - ∑ a, Γ a l m * R k s a n - ∑ a, Γ a l n * R k s m a)
    (l k s m n : Fin 4) : B l k s m n + B m k s n l + B n k s l m = 0 := by
  simp only [hB, hdR, hR, Fin.sum_univ_four]
  simp only [hΓ, hdG, hdd1, hdd2]
  ring

set_option maxHeartbeats 4000000 in
theorem anti_alg (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (dG : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ddG : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ k s m n, R k s m n = dG m k s n - dG n k s m
      + ∑ a, (Γ k m a * Γ a s n - Γ k n a * Γ a s m))
    (dR : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdR : ∀ l k s m n, dR l k s m n = ddG l m k s n - ddG l n k s m
      + ∑ a, (dG l k m a * Γ a s n + Γ k m a * dG l a s n
        - (dG l k n a * Γ a s m + Γ k n a * dG l a s m)))
    (B : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hB : ∀ l k s m n, B l k s m n = dR l k s m n + ∑ a, Γ k l a * R a s m n
      - ∑ a, Γ a l s * R k a m n - ∑ a, Γ a l m * R k s a n - ∑ a, Γ a l n * R k s m a)
    (l k s m n : Fin 4) : B l k s n m = -B l k s m n := by
  simp only [hB, hdR, hR, Fin.sum_univ_four]
  ring

theorem step2_alg (G : Matrix (Fin 4) (Fin 4) ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (dR : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → ℝ) (l ρ σ μ ν : Fin 4)
    (hdg : ∀ k, dg k = ∑ a, Γ a l ρ * G a k + ∑ a, Γ a l k * G ρ a) :
    ∑ k, (dg k * R k σ μ ν + G ρ k * dR k σ μ ν)
      - ∑ k, Γ k l ρ * (∑ a, G k a * R a σ μ ν)
      - ∑ k, Γ k l σ * (∑ a, G ρ a * R a k μ ν)
      - ∑ k, Γ k l μ * (∑ a, G ρ a * R a σ k ν)
      - ∑ k, Γ k l ν * (∑ a, G ρ a * R a σ μ k)
      = ∑ k, G ρ k * (dR k σ μ ν + ∑ a, Γ k l a * R a σ μ ν
        - ∑ a, Γ a l σ * R k a μ ν - ∑ a, Γ a l μ * R k σ a ν - ∑ a, Γ a l ν * R k σ μ a) := by
  simp only [hdg, Fin.sum_univ_four]
  ring

set_option maxHeartbeats 4000000 in
theorem pair_alg (G Gi : Fin 4 → Fin 4 → ℝ) (L : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (DD : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (dΓ : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hΓ : ∀ k a b, Γ k a b = ∑ r, Gi k r * L r a b)
    (hGΓ : ∀ μ a b, ∑ k, G μ k * Γ k a b = L μ a b)
    (hdΓ : ∀ ρ μ ν σ, ∑ k, G μ k * dΓ ρ k ν σ
      = (1 / 2 : ℝ) * (DD ρ ν σ μ + DD ρ σ μ ν - DD ρ μ ν σ)
        - ∑ k, (L μ ρ k + L k ρ μ) * Γ k ν σ)
    (hGi : ∀ a b, Gi a b = Gi b a) (hL : ∀ r a b, L r a b = L r b a)
    (hDD1 : ∀ d c a b, DD d c a b = DD c d a b) (hDD2 : ∀ d c a b, DD d c a b = DD d c b a)
    (μ ν ρ σ : Fin 4) :
    ∑ k, G μ k * (dΓ ρ k ν σ - dΓ σ k ν ρ + ∑ a, (Γ k ρ a * Γ a ν σ - Γ k σ a * Γ a ν ρ))
      = ∑ k, G ρ k * (dΓ μ k σ ν - dΓ ν k σ μ + ∑ a, (Γ k μ a * Γ a σ ν - Γ k ν a * Γ a σ μ)) := by
  have key : ∀ μ ν ρ σ : Fin 4,
      ∑ k, G μ k * (dΓ ρ k ν σ - dΓ σ k ν ρ + ∑ a, (Γ k ρ a * Γ a ν σ - Γ k σ a * Γ a ν ρ))
        = (1 / 2 : ℝ) * (DD ρ ν σ μ + DD ρ σ μ ν - DD ρ μ ν σ)
          - (1 / 2 : ℝ) * (DD σ ν ρ μ + DD σ ρ μ ν - DD σ μ ν ρ)
          - ∑ k, L k ρ μ * Γ k ν σ + ∑ k, L k σ μ * Γ k ν ρ := by
    intro μ ν ρ σ
    have e1 : ∑ k, G μ k * (dΓ ρ k ν σ - dΓ σ k ν ρ
          + ∑ a, (Γ k ρ a * Γ a ν σ - Γ k σ a * Γ a ν ρ))
        = ∑ k, G μ k * dΓ ρ k ν σ - ∑ k, G μ k * dΓ σ k ν ρ
          + ∑ a, (∑ k, G μ k * Γ k ρ a) * Γ a ν σ
          - ∑ a, (∑ k, G μ k * Γ k σ a) * Γ a ν ρ := by
      simp only [Fin.sum_univ_four]
      ring
    rw [e1, hdΓ, hdΓ]
    simp only [hGΓ, Fin.sum_univ_four]
    ring
  rw [key, key]
  simp only [hΓ, Fin.sum_univ_four]
  simp only [hGi, hL, hDD1, hDD2]
  ring

/-! ### Lorentzian facts and derivative helpers -/

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
  have hPtu : IsUnit Pᵀ :=
    (Matrix.isUnit_iff_isUnit_det Pᵀ).mpr (by rw [Matrix.det_transpose]; exact hP)
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

theorem pd_congr {f h : Coord → ℝ} {y : Coord} (hev : f =ᶠ[nhds y] h) (μ : Fin 4) :
    partialD μ f y = partialD μ h y := by
  unfold partialD
  rw [hev.fderiv_eq]

theorem pd_ev {f h : Coord → ℝ} {y : Coord} (hev : f =ᶠ[nhds y] h) (μ : Fin 4) :
    partialD μ f =ᶠ[nhds y] partialD μ h := by
  filter_upwards [hev.fderiv (𝕜 := ℝ)] with z hz
  unfold partialD
  rw [hz]

theorem pd_symm {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (ρ a b : Fin 4) :
    partialD ρ (fun y => g y a b) x = partialD ρ (fun y => g y b a) x := by
  have hev : (fun y => g y a b) =ᶠ[nhds x] (fun y => g y b a) := by
    filter_upwards [hg.1.mem_nhds hx] with y hy
    exact lor_symm' (hg.2.2 y hy) a b
  exact pd_congr hev ρ

theorem christoffel_symm' (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) :
    christoffel g σ μ ν x = christoffel g σ ν μ x := by
  unfold christoffel
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [pd_symm hg hx μ ν ρ, pd_symm hg hx ν ρ μ, pd_symm hg hx ρ μ ν]
  ring

theorem pd_mul {f h : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    partialD i (fun y => f y * h y) x = partialD i f x * h x + f x * partialD i h x := by
  simp [partialD, fderiv_fun_mul hf hh]
  ring

theorem pd_sum {F : Fin 4 → Coord → ℝ} {x : Coord} (h : ∀ k, DifferentiableAt ℝ (F k) x)
    (i : Fin 4) :
    partialD i (fun y => ∑ k, F k y) x = ∑ k, partialD i (F k) x := by
  simp [partialD, fderiv_fun_sum (fun k _ => h k)]

theorem pd_add {f h : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    partialD i (fun y => f y + h y) x = partialD i f x + partialD i h x := by
  simp [partialD, fderiv_fun_add hf hh]

theorem pd_sub {f h : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (i : Fin 4) :
    partialD i (fun y => f y - h y) x = partialD i f x - partialD i h x := by
  simp [partialD, fderiv_fun_sub hf hh]

theorem pd_cmul {f : Coord → ℝ} {x : Coord} (c : ℝ) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    partialD i (fun y => c * f y) x = c * partialD i f x := by
  rw [pd_mul (differentiableAt_const c) hf]
  simp [partialD]

theorem dA {f : Coord → ℝ} {y : Coord} (h : ContDiffAt ℝ ∞ f y) : DifferentiableAt ℝ f y :=
  h.differentiableAt (by simp)

theorem cd_pd {f : Coord → ℝ} {y : Coord} (hf : ContDiffAt ℝ ∞ f y) (μ : Fin 4) :
    ContDiffAt ℝ ∞ (partialD μ f) y := by
  have h1 : ContDiffAt ℝ ∞ (fderiv ℝ f) y := hf.fderiv_right (m := ∞) (by simp)
  exact h1.clm_apply contDiffAt_const

theorem pd_pd_comm {f : Coord → ℝ} {y : Coord} (hf : ContDiffAt ℝ ∞ f y) (a b : Fin 4) :
    partialD a (partialD b f) y = partialD b (partialD a f) y := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have key : ∀ c d : Fin 4, partialD c (partialD d f) y
      = fderiv ℝ (fderiv ℝ f) y (Pi.single c 1) (Pi.single d 1) := by
    intro c d
    unfold partialD
    rw [fderiv_clm_apply hdf (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hf.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) _ _

theorem cdg {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (a b : Fin 4) : ContDiffAt ℝ ∞ (fun z => g z a b) y :=
  (hg.2.1 a b).contDiffAt (hg.1.mem_nhds hy)

theorem gdiff {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (a b : Fin 4) : DifferentiableAt ℝ (fun y => g y a b) x :=
  dA (cdg hg hx a b)

theorem cd_det {A : Coord → Matrix (Fin 4) (Fin 4) ℝ} {x : Coord}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => A y i j) x) :
    ContDiffAt ℝ ∞ (fun y => (A y).det) x := by
  simp_rw [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  exact contDiffAt_prod fun i _ => h _ _

theorem cd_inv {A : Coord → Matrix (Fin 4) (Fin 4) ℝ} {x : Coord}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => A y i j) x) (hd : (A x).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => (A y)⁻¹ i j) x := by
  have hadj : ContDiffAt ℝ ∞ (fun y => (A y).adjugate i j) x := by
    simp_rw [Matrix.adjugate_apply]
    apply cd_det
    intro a b
    by_cases hab : a = j
    · subst hab; simp only [Matrix.updateRow_self]; exact contDiffAt_const
    · simp only [Matrix.updateRow_ne hab]; exact h a b
  have e : (fun y => (A y)⁻¹ i j) = fun y => ((A y).det)⁻¹ * (A y).adjugate i j := by
    funext y
    simp [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [e]
  exact ((cd_det h).inv hd).mul hadj

theorem cd_chr {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (k a b : Fin 4) : ContDiffAt ℝ ∞ (christoffel g k a b) y := by
  show ContDiffAt ℝ ∞ (fun z => christoffel g k a b z) y
  simp only [christoffel, invMetric]
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro r _
  exact (cd_inv (cdg hg hy) (lor_det_ne (hg.2.2 y hy)) k r).mul
    (((cd_pd (cdg hg hy b r) a).add (cd_pd (cdg hg hy r a) b)).sub (cd_pd (cdg hg hy a b) r))

theorem cd_riem {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (k s m n : Fin 4) : ContDiffAt ℝ ∞ (fun z => riemann g k s m n z) y := by
  simp only [riemann]
  exact ((cd_pd (cd_chr hg hy k s n) m).sub (cd_pd (cd_chr hg hy k s m) n)).add
    (ContDiffAt.sum fun a _ => ((cd_chr hg hy k m a).mul (cd_chr hg hy a s n)).sub
      ((cd_chr hg hy k n a).mul (cd_chr hg hy a s m)))

/-! ### Pair symmetry of the lowered Riemann tensor on U -/

/-- Christoffel symbol of the first kind. -/
noncomputable def Lf (g : TensorField2) (μ ν σ : Fin 4) (z : Coord) : ℝ :=
  (1 / 2 : ℝ) * (partialD ν (fun w => g w σ μ) z + partialD σ (fun w => g w μ ν) z
    - partialD μ (fun w => g w ν σ) z)

theorem chr_eq_L (g : TensorField2) (z : Coord) (k a b : Fin 4) :
    christoffel g k a b z = ∑ r, (g z)⁻¹ k r * Lf g r a b z := by
  simp only [christoffel, invMetric, Lf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem G_chr {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {z : Coord}
    (hz : z ∈ U) (μ a b : Fin 4) :
    ∑ k, g z μ k * christoffel g k a b z = Lf g μ a b z := by
  have hGG : g z * (g z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (lor_det_ne (hg.2.2 z hz)))
  simp only [chr_eq_L]
  have h : (g z *ᵥ ((g z)⁻¹ *ᵥ fun r => Lf g r a b z)) μ
      = ∑ k, g z μ k * ∑ r, (g z)⁻¹ k r * Lf g r a b z := rfl
  rw [← h, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]

theorem L_symm {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {z : Coord}
    (hz : z ∈ U) (r a b : Fin 4) : Lf g r a b z = Lf g r b a z := by
  simp only [Lf]
  rw [pd_symm hg hz a r b, pd_symm hg hz b a r, pd_symm hg hz r a b]
  ring

theorem dg_L {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {z : Coord}
    (hz : z ∈ U) (ρ μ k : Fin 4) :
    partialD ρ (fun w => g w μ k) z = Lf g μ ρ k z + Lf g k ρ μ z := by
  simp only [Lf]
  rw [pd_symm hg hz ρ k μ, pd_symm hg hz k μ ρ, pd_symm hg hz μ ρ k]
  ring

theorem pd_L {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (ρ μ ν σ : Fin 4) :
    partialD ρ (Lf g μ ν σ) y = (1 / 2 : ℝ) * (partialD ρ (partialD ν (fun w => g w σ μ)) y
      + partialD ρ (partialD σ (fun w => g w μ ν)) y
      - partialD ρ (partialD μ (fun w => g w ν σ)) y) := by
  have e : Lf g μ ν σ = fun z => (1 / 2 : ℝ) * ((partialD ν (fun w => g w σ μ) z
      + partialD σ (fun w => g w μ ν) z) - partialD μ (fun w => g w ν σ) z) := rfl
  have d1 := dA (cd_pd (cdg hg hy σ μ) ν)
  have d2 := dA (cd_pd (cdg hg hy μ ν) σ)
  have d3 := dA (cd_pd (cdg hg hy ν σ) μ)
  have d12 : DifferentiableAt ℝ (fun z => partialD ν (fun w => g w σ μ) z
      + partialD σ (fun w => g w μ ν) z) y := d1.add d2
  have d123 : DifferentiableAt ℝ (fun z => (partialD ν (fun w => g w σ μ) z
      + partialD σ (fun w => g w μ ν) z) - partialD μ (fun w => g w ν σ) z) y := d12.sub d3
  rw [e, pd_cmul _ d123, pd_sub d12 d3, pd_add d1 d2]

theorem G_dchr {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (ρ μ ν σ : Fin 4) :
    ∑ k, g y μ k * partialD ρ (christoffel g k ν σ) y
      = partialD ρ (Lf g μ ν σ) y
        - ∑ k, partialD ρ (fun w => g w μ k) y * christoffel g k ν σ y := by
  have hev : (fun z => ∑ k, g z μ k * christoffel g k ν σ z) =ᶠ[nhds y] Lf g μ ν σ := by
    filter_upwards [hg.1.mem_nhds hy] with z hz
    exact G_chr hg hz μ ν σ
  have h := pd_congr hev ρ
  rw [pd_sum (F := fun k z => g z μ k * christoffel g k ν σ z)
    (fun k => (gdiff hg hy μ k).mul (dA (cd_chr hg hy k ν σ)))] at h
  have h1 : ∀ k, partialD ρ (fun z => g z μ k * christoffel g k ν σ z) y
      = partialD ρ (fun w => g w μ k) y * christoffel g k ν σ y
        + g y μ k * partialD ρ (christoffel g k ν σ) y :=
    fun k => pd_mul (gdiff hg hy μ k) (dA (cd_chr hg hy k ν σ)) ρ
  simp only [h1, Finset.sum_add_distrib] at h
  linarith

theorem pair_sym {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (μ ν ρ σ : Fin 4) :
    riemannLower g y μ ν ρ σ = riemannLower g y ρ σ μ ν := by
  have hDD2 : ∀ d c a b : Fin 4, partialD d (partialD c (fun w => g w a b)) y
      = partialD d (partialD c (fun w => g w b a)) y := by
    intro d c a b
    have hev : (fun w => g w a b) =ᶠ[nhds y] (fun w => g w b a) := by
      filter_upwards [hg.1.mem_nhds hy] with w hw
      exact lor_symm' (hg.2.2 w hw) a b
    exact pd_congr (pd_ev hev c) d
  have hdΓ : ∀ ρ μ ν σ : Fin 4, ∑ k, g y μ k * partialD ρ (christoffel g k ν σ) y
      = (1 / 2 : ℝ) * (partialD ρ (partialD ν (fun w => g w σ μ)) y
          + partialD ρ (partialD σ (fun w => g w μ ν)) y
          - partialD ρ (partialD μ (fun w => g w ν σ)) y)
        - ∑ k, (Lf g μ ρ k y + Lf g k ρ μ y) * christoffel g k ν σ y := by
    intro ρ μ ν σ
    rw [G_dchr hg hy, pd_L hg hy]
    simp only [dg_L hg hy]
  exact pair_alg (fun a b => g y a b) (fun a b => (g y)⁻¹ a b) (fun r a b => Lf g r a b y)
    (fun d c a b => partialD d (partialD c (fun w => g w a b)) y)
    (fun ρ k ν σ => partialD ρ (christoffel g k ν σ) y)
    (fun k a b => christoffel g k a b y)
    (fun k a b => chr_eq_L g y k a b) (fun μ a b => G_chr hg hy μ a b) hdΓ
    (lor_inv_symm' (hg.2.2 y hy)) (fun r a b => L_symm hg hy r a b)
    (fun d c a b => pd_pd_comm (cdg hg hy a b) d c) hDD2 μ ν ρ σ

/-! ### Assembly at x -/

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

theorem mc_lower (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (σ μ ν : Fin 4) : covDerivLower2 g g σ μ ν x = 0 := by
  have hL := hg.2.2 x hx
  have hGG : g x * (g x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (lor_det_ne hL))
  have hD : ∀ c a b, partialD c (fun y => g y a b) x = partialD c (fun y => g y b a) x :=
    fun c a b => pd_symm hg hx c a b
  unfold covDerivLower2 christoffel invMetric
  exact lower_alg (g x) (g x)⁻¹ hGG (lor_symm' hL)
    (fun c a b => partialD c (fun y => g y a b) x) hD σ μ ν

/-- The (1,3) covariant derivative `∇_l R^k_{s m n}`. -/
noncomputable def Bfun (g : TensorField2) (x : Coord) (l k s m n : Fin 4) : ℝ :=
  partialD l (fun y => riemann g k s m n y) x + ∑ a, christoffel g k l a x * riemann g a s m n x
    - ∑ a, christoffel g a l s x * riemann g k a m n x
    - ∑ a, christoffel g a l m x * riemann g k s a n x
    - ∑ a, christoffel g a l n x * riemann g k s m a x

theorem d_riem {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l k s m n : Fin 4) :
    partialD l (fun y => riemann g k s m n y) x
      = partialD l (partialD m (christoffel g k s n)) x
        - partialD l (partialD n (christoffel g k s m)) x
        + ∑ a, (partialD l (christoffel g k m a) x * christoffel g a s n x
            + christoffel g k m a x * partialD l (christoffel g a s n) x
          - (partialD l (christoffel g k n a) x * christoffel g a s m x
            + christoffel g k n a x * partialD l (christoffel g a s m) x)) := by
  have e : (fun y => riemann g k s m n y) = fun y =>
      (partialD m (christoffel g k s n) y - partialD n (christoffel g k s m) y)
        + ∑ a, (christoffel g k m a y * christoffel g a s n y
          - christoffel g k n a y * christoffel g a s m y) := rfl
  have c := fun k a b => dA (cd_chr hg hx k a b)
  have d1 := dA (cd_pd (cd_chr hg hx k s n) m)
  have d2 := dA (cd_pd (cd_chr hg hx k s m) n)
  have dS : ∀ a, DifferentiableAt ℝ (fun y => christoffel g k m a y * christoffel g a s n y
      - christoffel g k n a y * christoffel g a s m y) x :=
    fun a => ((c k m a).mul (c a s n)).sub ((c k n a).mul (c a s m))
  have d12 : DifferentiableAt ℝ (fun y => partialD m (christoffel g k s n) y
      - partialD n (christoffel g k s m) y) x := d1.sub d2
  have dsum : DifferentiableAt ℝ (fun y => ∑ a, (christoffel g k m a y * christoffel g a s n y
      - christoffel g k n a y * christoffel g a s m y)) x :=
    DifferentiableAt.fun_sum fun a _ => dS a
  rw [e, pd_add d12 dsum, pd_sub d1 d2,
    pd_sum (F := fun a y => christoffel g k m a y * christoffel g a s n y
      - christoffel g k n a y * christoffel g a s m y) dS]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have dm1 : DifferentiableAt ℝ (fun y => christoffel g k m a y * christoffel g a s n y) x :=
    (c k m a).mul (c a s n)
  have dm2 : DifferentiableAt ℝ (fun y => christoffel g k n a y * christoffel g a s m y) x :=
    (c k n a).mul (c a s m)
  rw [pd_sub dm1 dm2,
    pd_mul (c k m a) (c a s n), pd_mul (c k n a) (c a s m)]

theorem cyc_B {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l k s m n : Fin 4) :
    Bfun g x l k s m n + Bfun g x m k s n l + Bfun g x n k s l m = 0 := by
  have hchr : ∀ k a b, christoffel g k a b =ᶠ[nhds x] christoffel g k b a := by
    intro k a b
    filter_upwards [hg.1.mem_nhds hx] with z hz
    exact christoffel_symm' g U hg z hz k a b
  exact core_alg (fun k a b => christoffel g k a b x)
    (fun l k a b => partialD l (christoffel g k a b) x)
    (fun l m k a b => partialD l (partialD m (christoffel g k a b)) x)
    (fun k a b => christoffel_symm' g U hg x hx k a b)
    (fun l k a b => pd_congr (hchr k a b) l)
    (fun l m k a b => pd_pd_comm (cd_chr hg hx k a b) l m)
    (fun l m k a b => pd_congr (pd_ev (hchr k a b) m) l)
    (fun k s m n => riemann g k s m n x) (fun k s m n => rfl)
    (fun l k s m n => partialD l (fun y => riemann g k s m n y) x)
    (fun l k s m n => d_riem hg hx l k s m n)
    (Bfun g x) (fun l k s m n => rfl) l k s m n

theorem anti_B {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l k s m n : Fin 4) :
    Bfun g x l k s n m = -Bfun g x l k s m n :=
  anti_alg (fun k a b => christoffel g k a b x)
    (fun l k a b => partialD l (christoffel g k a b) x)
    (fun l m k a b => partialD l (partialD m (christoffel g k a b)) x)
    (fun k s m n => riemann g k s m n x) (fun k s m n => rfl)
    (fun l k s m n => partialD l (fun y => riemann g k s m n y) x)
    (fun l k s m n => d_riem hg hx l k s m n)
    (Bfun g x) (fun l k s m n => rfl) l k s m n

theorem cov_eq {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l ρ σ μ ν : Fin 4) :
    covDerivLower4 g (riemannLower g) l ρ σ μ ν x = ∑ k, g x ρ k * Bfun g x l k σ μ ν := by
  have hb4 : partialD l (fun y => riemannLower g y ρ σ μ ν) x
      = ∑ k, (partialD l (fun y => g y ρ k) x * riemann g k σ μ ν x
        + g x ρ k * partialD l (fun y => riemann g k σ μ ν y) x) := by
    show partialD l (fun y => ∑ k, g y ρ k * riemann g k σ μ ν y) x = _
    rw [pd_sum (F := fun k y => g y ρ k * riemann g k σ μ ν y)
      (fun k => (gdiff hg hx ρ k).mul (dA (cd_riem hg hx k σ μ ν)))]
    exact Finset.sum_congr rfl fun k _ => pd_mul (gdiff hg hx ρ k) (dA (cd_riem hg hx k σ μ ν)) l
  have hdg : ∀ k, partialD l (fun y => g y ρ k) x
      = ∑ a, christoffel g a l ρ x * g x a k + ∑ a, christoffel g a l k x * g x ρ a := by
    intro k
    have h := mc_lower g U hg x hx l ρ k
    unfold covDerivLower2 at h
    linarith
  unfold covDerivLower4
  rw [hb4]
  exact step2_alg (g x) (fun k a b => christoffel g k a b x) (fun k s m n => riemann g k s m n x)
    (fun k s m n => partialD l (fun y => riemann g k s m n y) x)
    (fun k => partialD l (fun y => g y ρ k) x) l ρ σ μ ν hdg

theorem cov_pair {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l μ ν ρ σ : Fin 4) :
    covDerivLower4 g (riemannLower g) l μ ν ρ σ x
      = covDerivLower4 g (riemannLower g) l ρ σ μ ν x := by
  have hev : (fun y => riemannLower g y μ ν ρ σ) =ᶠ[nhds x]
      (fun y => riemannLower g y ρ σ μ ν) := by
    filter_upwards [hg.1.mem_nhds hx] with z hz
    exact pair_sym hg hz μ ν ρ σ
  have hp : ∀ a b c d, riemannLower g x a b c d = riemannLower g x c d a b :=
    fun a b c d => pair_sym hg hx a b c d
  unfold covDerivLower4
  rw [pd_congr hev l]
  simp only [hp]
  ring


/-! ### Contracted Bianchi identity -/

theorem pd_inv {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (μ ρ a : Fin 4) :
    partialD μ (fun y => (g y)⁻¹ ρ a) x
      = -∑ σ, (∑ b, (g x)⁻¹ ρ b * partialD μ (fun y => g y b σ) x) * (g x)⁻¹ σ a := by
  have hu : ∀ y ∈ U, IsUnit (g y).det :=
    fun y hy => isUnit_iff_ne_zero.mpr (lor_det_ne (hg.2.2 y hy))
  have hgd := gdiff hg hx
  have hid : ∀ i j, DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x :=
    fun i j => dA (cd_inv (cdg hg hx) (lor_det_ne (hg.2.2 x hx)) i j)
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

theorem dH_alg (G Hm : Matrix (Fin 4) (Fin 4) ℝ) (hGH : G * Hm = 1) (hHG : Hm * G = 1)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (c : Fin 4) (dg : Fin 4 → Fin 4 → ℝ)
    (hdg : ∀ p q, dg p q = ∑ l, Γ l c p * G l q + ∑ l, Γ l c q * G p l) (a b : Fin 4) :
    -∑ σ, (∑ p, Hm a p * dg p σ) * Hm σ b
      = -∑ l, Γ a c l * Hm l b - ∑ l, Γ b c l * Hm a l := by
  let Gc : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun l p => Γ l c p
  have hM : Matrix.of dg = Gcᵀ * G + G * Gc := by
    ext p q
    simp only [Matrix.of_apply, hdg, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Gc]
    congr 1
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hP : Hm * Matrix.of dg * Hm = Hm * Gcᵀ + Gc * Hm := by
    rw [hM, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc Hm Gcᵀ G,
      Matrix.mul_assoc (Hm * Gcᵀ) G Hm, hGH, Matrix.mul_one, ← Matrix.mul_assoc Hm G Gc, hHG,
      Matrix.one_mul]
  have e := congrFun (congrFun hP a) b
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply,
    Gc] at e
  rw [e]
  simp only [Fin.sum_univ_four]
  ring

theorem dH_eq {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (c a b : Fin 4) :
    partialD c (fun y => (g y)⁻¹ a b) x
      = -∑ l, christoffel g a c l x * (g x)⁻¹ l b - ∑ l, christoffel g b c l x * (g x)⁻¹ a l := by
  rw [pd_inv hg hx c a b]
  have hu := isUnit_iff_ne_zero.mpr (lor_det_ne (hg.2.2 x hx))
  refine dH_alg (g x) (g x)⁻¹ (Matrix.mul_nonsing_inv _ hu) (Matrix.nonsing_inv_mul _ hu)
    (fun k a b => christoffel g k a b x) c (fun p q => partialD c (fun y => g y p q) x) ?_ a b
  intro p q
  have h := mc_lower g U hg x hx c p q
  unfold covDerivLower2 at h
  linarith

theorem cd_H {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (a b : Fin 4) : ContDiffAt ℝ ∞ (fun z => (g z)⁻¹ a b) y :=
  cd_inv (cdg hg hy) (lor_det_ne (hg.2.2 y hy)) a b

theorem cd_ric {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (a b : Fin 4) : ContDiffAt ℝ ∞ (fun z => ricci g a b z) y := by
  simp only [ricci]
  exact ContDiffAt.sum fun l _ => cd_riem hg hy l a l b

theorem cd_R {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) : ContDiffAt ℝ ∞ (fun z => ricciScalar g z) y := by
  simp only [ricciScalar, invMetric]
  exact ContDiffAt.sum fun μ _ => ContDiffAt.sum fun ν _ => (cd_H hg hy μ ν).mul (cd_ric hg hy μ ν)

theorem cd_E {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (a b : Fin 4) : ContDiffAt ℝ ∞ (fun z => einstein g a b z) y := by
  simp only [einstein]
  exact (cd_ric hg hy a b).sub ((contDiffAt_const.mul (cd_R hg hy)).mul (cdg hg hy a b))

theorem d_R {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (c : Fin 4) :
    partialD c (fun y => ricciScalar g y) x = ∑ a, ∑ b, (partialD c (fun y => (g y)⁻¹ a b) x
      * ricci g a b x + (g x)⁻¹ a b * partialD c (fun y => ricci g a b y) x) := by
  show partialD c (fun y => ∑ a, ∑ b, (g y)⁻¹ a b * ricci g a b y) x = _
  rw [pd_sum (F := fun a y => ∑ b, (g y)⁻¹ a b * ricci g a b y)
    (fun a => DifferentiableAt.fun_sum fun b _ =>
      (dA (cd_H hg hx a b)).mul (dA (cd_ric hg hx a b)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pd_sum (F := fun b y => (g y)⁻¹ a b * ricci g a b y)
    (fun b => (dA (cd_H hg hx a b)).mul (dA (cd_ric hg hx a b)))]
  exact Finset.sum_congr rfl fun b _ => pd_mul (dA (cd_H hg hx a b)) (dA (cd_ric hg hx a b)) c

theorem d_E {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (c a b : Fin 4) :
    partialD c (fun y => einstein g a b y) x = partialD c (fun y => ricci g a b y) x
      - (1 / 2 : ℝ) * (partialD c (fun y => ricciScalar g y) x * g x a b
        + ricciScalar g x * partialD c (fun y => g y a b) x) := by
  have e : (fun y => einstein g a b y)
      = fun y => ricci g a b y - ((1 / 2 : ℝ) * ricciScalar g y) * g y a b := rfl
  have d1 := dA (cd_ric hg hx a b)
  have d2 : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * ricciScalar g y) x :=
    (differentiableAt_const _).mul (dA (cd_R hg hx))
  have d3 := gdiff hg hx a b
  have d23 : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * ricciScalar g y * g y a b) x :=
    d2.mul d3
  rw [e, pd_sub d1 d23, pd_mul d2 d3, pd_cmul _ (dA (cd_R hg hx))]
  ring

theorem d_EU {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (c μ ν : Fin 4) :
    partialD c (fun y => einsteinUpper g y μ ν) x
      = ∑ α, ∑ β, (partialD c (fun y => (g y)⁻¹ μ α) x * (g x)⁻¹ ν β * einstein g α β x
        + (g x)⁻¹ μ α * partialD c (fun y => (g y)⁻¹ ν β) x * einstein g α β x
        + (g x)⁻¹ μ α * (g x)⁻¹ ν β * partialD c (fun y => einstein g α β y) x) := by
  show partialD c (fun y => ∑ α, ∑ β, (g y)⁻¹ μ α * (g y)⁻¹ ν β * einstein g α β y) x = _
  have hH := fun a b => dA (cd_H hg hx a b)
  have hE := fun a b => dA (cd_E hg hx a b)
  rw [pd_sum (F := fun α y => ∑ β, (g y)⁻¹ μ α * (g y)⁻¹ ν β * einstein g α β y)
    (fun α => DifferentiableAt.fun_sum fun β _ => ((hH μ α).mul (hH ν β)).mul (hE α β))]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [pd_sum (F := fun β y => (g y)⁻¹ μ α * (g y)⁻¹ ν β * einstein g α β y)
    (fun β => ((hH μ α).mul (hH ν β)).mul (hE α β))]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hHH : DifferentiableAt ℝ (fun y => (g y)⁻¹ μ α * (g y)⁻¹ ν β) x :=
    (hH μ α).mul (hH ν β)
  rw [pd_mul hHH (hE α β), pd_mul (hH μ α) (hH ν β)]
  ring

set_option maxHeartbeats 4000000 in
theorem up_alg (H : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (E : Fin 4 → Fin 4 → ℝ)
    (dH : Fin 4 → Fin 4 → Fin 4 → ℝ) (dE : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdH : ∀ c a b, dH c a b = -∑ l, Γ a c l * H l b - ∑ l, Γ b c l * H a l) (c μ ν : Fin 4) :
    ∑ α, ∑ β, (dH c μ α * H ν β * E α β + H μ α * dH c ν β * E α β
        + H μ α * H ν β * dE c α β)
      + ∑ l, Γ μ c l * (∑ α, ∑ β, H l α * H ν β * E α β)
      + ∑ l, Γ ν c l * (∑ α, ∑ β, H μ α * H l β * E α β)
      = ∑ α, ∑ β, H μ α * H ν β * (dE c α β - ∑ l, Γ l c α * E l β - ∑ l, Γ l c β * E α l) := by
  simp only [hdH, Fin.sum_univ_four]
  ring

theorem ce_alg (G : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Ric : Fin 4 → Fin 4 → ℝ) (R : ℝ) (dRic : Fin 4 → Fin 4 → ℝ) (dR : ℝ)
    (dg : Fin 4 → Fin 4 → ℝ) (c α β : Fin 4)
    (hdg : ∀ p q, dg p q = ∑ l, Γ l c p * G l q + ∑ l, Γ l c q * G p l) :
    (dRic α β - (1 / 2 : ℝ) * (dR * G α β + R * dg α β))
      - ∑ l, Γ l c α * (Ric l β - (1 / 2 : ℝ) * R * G l β)
      - ∑ l, Γ l c β * (Ric α l - (1 / 2 : ℝ) * R * G α l)
      = (dRic α β - ∑ l, Γ l c α * Ric l β - ∑ l, Γ l c β * Ric α l)
        - (1 / 2 : ℝ) * dR * G α β := by
  rw [hdg α β]
  simp only [Fin.sum_univ_four]
  ring

theorem dR_alg (H : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (c : Fin 4)
    (Ric dRic dH : Fin 4 → Fin 4 → ℝ)
    (hdH : ∀ a b, dH a b = -∑ l, Γ a c l * H l b - ∑ l, Γ b c l * H a l) :
    ∑ a, ∑ b, (dH a b * Ric a b + H a b * dRic a b)
      = ∑ a, ∑ b, H a b * (dRic a b - ∑ l, Γ l c a * Ric l b - ∑ l, Γ l c b * Ric a l) := by
  simp only [hdH, Fin.sum_univ_four]
  ring

/-- Covariant derivative of the Ricci tensor, `∇_c R_{ab}`. -/
noncomputable def CRic (g : TensorField2) (x : Coord) (c a b : Fin 4) : ℝ :=
  partialD c (fun y => ricci g a b y) x - ∑ l, christoffel g l c a x * ricci g l b x
    - ∑ l, christoffel g l c b x * ricci g a l x

/-- The lowered derivative `∇_l R_{ρσmn} = g_{ρk} ∇_l R^k_{σmn}`. -/
noncomputable def Dt (g : TensorField2) (x : Coord) (l ρ σ m n : Fin 4) : ℝ :=
  ∑ k, g x ρ k * Bfun g x l k σ m n

theorem cric_B {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (c a b : Fin 4) : CRic g x c a b = ∑ k, Bfun g x c k a k b := by
  have h : partialD c (fun y => ricci g a b y) x
      = ∑ k, partialD c (fun y => riemann g k a k b y) x := by
    show partialD c (fun y => ∑ k, riemann g k a k b y) x = _
    exact pd_sum (F := fun k y => riemann g k a k b y) (fun k => dA (cd_riem hg hx k a k b)) c
  unfold CRic Bfun
  rw [h]
  simp only [ricci, Fin.sum_univ_four]
  ring

theorem B_D {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l k s m n : Fin 4) :
    Bfun g x l k s m n = ∑ p, (g x)⁻¹ k p * Dt g x l p s m n := by
  have hu := isUnit_iff_ne_zero.mpr (lor_det_ne (hg.2.2 x hx))
  have h : ((g x)⁻¹ *ᵥ (g x *ᵥ fun q => Bfun g x l q s m n)) k
      = ∑ p, (g x)⁻¹ k p * ∑ q, g x p q * Bfun g x l q s m n := rfl
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  unfold Dt
  rw [← h]

theorem Dt_cyc {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l ρ σ m n : Fin 4) :
    Dt g x l ρ σ m n + Dt g x m ρ σ n l + Dt g x n ρ σ l m = 0 := by
  unfold Dt
  simp only [Fin.sum_univ_four]
  linear_combination g x ρ 0 * cyc_B hg hx l 0 σ m n + g x ρ 1 * cyc_B hg hx l 1 σ m n
    + g x ρ 2 * cyc_B hg hx l 2 σ m n + g x ρ 3 * cyc_B hg hx l 3 σ m n

theorem Dt_anti {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l ρ σ m n : Fin 4) : Dt g x l ρ σ n m = -Dt g x l ρ σ m n := by
  unfold Dt
  simp only [Fin.sum_univ_four]
  linear_combination g x ρ 0 * anti_B hg hx l 0 σ m n + g x ρ 1 * anti_B hg hx l 1 σ m n
    + g x ρ 2 * anti_B hg hx l 2 σ m n + g x ρ 3 * anti_B hg hx l 3 σ m n

theorem Dt_eq {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l ρ σ m n : Fin 4) :
    Dt g x l ρ σ m n = covDerivLower4 g (riemannLower g) l ρ σ m n x :=
  (cov_eq hg hx l ρ σ m n).symm

theorem Dt_pair {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l ρ σ m n : Fin 4) : Dt g x l ρ σ m n = Dt g x l m n ρ σ := by
  rw [Dt_eq hg hx, Dt_eq hg hx]
  exact cov_pair hg hx l ρ σ m n

theorem Dt_first {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {x : Coord}
    (hx : x ∈ U) (l ρ σ m n : Fin 4) : Dt g x l σ ρ m n = -Dt g x l ρ σ m n := by
  rw [Dt_pair hg hx l σ ρ m n, Dt_anti hg hx l m n ρ σ, ← Dt_pair hg hx l ρ σ m n]

set_option maxHeartbeats 4000000 in
theorem contr_alg (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ a b, H a b = H b a)
    (D : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hcyc : ∀ l r s m n, D l r s m n + D m r s n l + D n r s l m = 0)
    (hanti : ∀ l r s m n, D l r s n m = -D l r s m n)
    (hfirst : ∀ l r s m n, D l s r m n = -D l r s m n) (β : Fin 4) :
    ∑ μ, ∑ α, H μ α * ∑ k, ∑ p, H k p * D μ p α k β
      = (1 / 2 : ℝ) * ∑ a, ∑ b, H a b * ∑ k, ∑ p, H k p * D β p a k b := by
  have e1 : ∑ μ, ∑ α, H μ α * ∑ k, ∑ p, H k p * D μ p α k β
      = ∑ μ, ∑ α, H μ α * ∑ k, ∑ p, (-(H k p * D k α p μ β) - H k p * D β p α μ k) := by
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
    have h1 := hcyc μ p α k β
    have h2 := hfirst k α p β μ
    have h3 := hanti k α p μ β
    linear_combination H k p * h1 + H k p * h3 - H k p * h2
  have e2 : ∑ μ, ∑ α, H μ α * ∑ k, ∑ p, (-(H k p * D k α p μ β) - H k p * D β p α μ k)
      = -(∑ μ, ∑ α, H μ α * ∑ k, ∑ p, H k p * D μ p α k β)
        - ∑ μ, ∑ α, H μ α * ∑ k, ∑ p, H k p * D β p α μ k := by
    simp only [Fin.sum_univ_four]
    ring
  have e3 : ∑ μ, ∑ α, H μ α * ∑ k, ∑ p, H k p * D β p α μ k
      = -∑ a, ∑ b, H a b * ∑ k, ∑ p, H k p * D β p a k b := by
    have hS : ∑ a, ∑ b, H a b * ∑ k, ∑ p, H k p * D β p a k b
        = ∑ a, ∑ b, H a b * ∑ k, ∑ p, -(H k p * D β p a b k) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
      rw [hanti β p a b k]
      ring
    rw [hS]
    simp only [Fin.sum_univ_four]
    simp only [hH]
    ring
  have := e1.trans e2
  rw [e3] at this
  linarith

theorem final_alg (H G : Matrix (Fin 4) (Fin 4) ℝ) (hHG : H * G = 1)
    (CR : Fin 4 → Fin 4 → Fin 4 → ℝ) (dR : Fin 4 → ℝ)
    (hF : ∀ β, ∑ μ, ∑ α, H μ α * CR μ α β = (1 / 2 : ℝ) * dR β) (ν : Fin 4) :
    ∑ μ, ∑ α, ∑ β, H μ α * H ν β * (CR μ α β - (1 / 2 : ℝ) * dR μ * G α β) = 0 := by
  have h2 : ∀ μ β, ∑ α, H μ α * G α β = if μ = β then 1 else 0 := by
    intro μ β
    have := congrFun (congrFun hHG μ) β
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have e : ∑ μ, ∑ α, ∑ β, H μ α * H ν β * (CR μ α β - (1 / 2 : ℝ) * dR μ * G α β)
      = ∑ β, H ν β * (∑ μ, ∑ α, H μ α * CR μ α β)
        - (1 / 2 : ℝ) * ∑ β, H ν β * ∑ μ, dR μ * ∑ α, H μ α * G α β := by
    simp only [Fin.sum_univ_four]
    ring
  rw [e]
  simp only [h2, hF, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Fin.sum_univ_four]
  ring

theorem main_cb {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (ν : Fin 4) :
    ∑ μ, covDerivUpper2 g (einsteinUpper g) μ μ ν x = 0 := by
  have hstep : ∀ μ, covDerivUpper2 g (einsteinUpper g) μ μ ν x
      = ∑ α, ∑ β, (g x)⁻¹ μ α * (g x)⁻¹ ν β * (CRic g x μ α β
        - (1 / 2 : ℝ) * partialD μ (fun y => ricciScalar g y) x * g x α β) := by
    intro μ
    have hc : covDerivUpper2 g (einsteinUpper g) μ μ ν x
        = ∑ α, ∑ β, (partialD μ (fun y => (g y)⁻¹ μ α) x * (g x)⁻¹ ν β * einstein g α β x
          + (g x)⁻¹ μ α * partialD μ (fun y => (g y)⁻¹ ν β) x * einstein g α β x
          + (g x)⁻¹ μ α * (g x)⁻¹ ν β * partialD μ (fun y => einstein g α β y) x)
        + ∑ l, christoffel g μ μ l x * (∑ α, ∑ β, (g x)⁻¹ l α * (g x)⁻¹ ν β * einstein g α β x)
        + ∑ l, christoffel g ν μ l x
          * (∑ α, ∑ β, (g x)⁻¹ μ α * (g x)⁻¹ l β * einstein g α β x) := by
      unfold covDerivUpper2
      rw [d_EU hg hx μ μ ν]
      rfl
    rw [hc]
    refine (up_alg (fun a b => (g x)⁻¹ a b) (fun k a b => christoffel g k a b x)
      (fun a b => einstein g a b x) (fun c a b => partialD c (fun y => (g y)⁻¹ a b) x)
      (fun c a b => partialD c (fun y => einstein g a b y) x)
      (fun c a b => dH_eq hg hx c a b) μ μ ν).trans ?_
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    congr 1
    rw [d_E hg hx μ α β]
    have hdg : ∀ p q, partialD μ (fun y => g y p q) x
        = ∑ l, christoffel g l μ p x * g x l q + ∑ l, christoffel g l μ q x * g x p l := by
      intro p q
      have h := mc_lower g U hg x hx μ p q
      unfold covDerivLower2 at h
      linarith
    exact ce_alg (fun a b => g x a b) (fun k a b => christoffel g k a b x)
      (fun a b => ricci g a b x) (ricciScalar g x)
      (fun a b => partialD μ (fun y => ricci g a b y) x)
      (partialD μ (fun y => ricciScalar g y) x) (fun p q => partialD μ (fun y => g y p q) x)
      μ α β hdg
  have hE : ∀ c, partialD c (fun y => ricciScalar g y) x
      = ∑ a, ∑ b, (g x)⁻¹ a b * CRic g x c a b := by
    intro c
    rw [d_R hg hx c]
    exact dR_alg (fun a b => (g x)⁻¹ a b) (fun k a b => christoffel g k a b x) c
      (fun a b => ricci g a b x) (fun a b => partialD c (fun y => ricci g a b y) x)
      (fun a b => partialD c (fun y => (g y)⁻¹ a b) x) (fun a b => dH_eq hg hx c a b)
  have hF : ∀ β, ∑ μ, ∑ α, (g x)⁻¹ μ α * CRic g x μ α β
      = (1 / 2 : ℝ) * partialD β (fun y => ricciScalar g y) x := by
    intro β
    rw [hE β]
    simp only [cric_B hg hx, B_D hg hx]
    exact contr_alg (fun a b => (g x)⁻¹ a b) (lor_inv_symm' (hg.2.2 x hx)) (Dt g x)
      (Dt_cyc hg hx) (Dt_anti hg hx) (Dt_first hg hx) β
  rw [Finset.sum_congr rfl fun μ _ => hstep μ]
  exact final_alg (g x)⁻¹ (g x)
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (lor_det_ne (hg.2.2 x hx))))
    (CRic g x) (fun c => partialD c (fun y => ricciScalar g y) x) hF ν

end CBBuild

open CarrollGR in open scoped ContDiff in
theorem solution (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (ν : Fin 4) :
    ∑ μ : Fin 4, covDerivUpper2 g (einsteinUpper g) μ μ ν x = 0 := by
  exact CBBuild.main_cb hg x hx ν
