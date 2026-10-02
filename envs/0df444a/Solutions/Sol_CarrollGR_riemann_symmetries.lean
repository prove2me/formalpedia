-- Prove2me | solution 1 for CarrollGR.riemann_symmetries
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:50:50.263502+00:00
-- url     : https://prove2.me/submissions/f1919367-483c-4c64-8716-e72f8c86ce5b

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 93e9ad0d CarrollGR.riemann_symmetries.
Closed form R_{mnrs} = (1/2)(second derivatives of g) - g^{-1} L L with L the Christoffel symbol
of the first kind (lemmas from 6a74678a / 65c665bf); every symmetry is then index algebra. -/

set_option autoImplicit false

open scoped ContDiff

namespace RSymBuild

open CarrollGR Matrix

set_option maxHeartbeats 8000000 in
theorem all_alg (G Gi : Fin 4 → Fin 4 → ℝ) (L : Fin 4 → Fin 4 → Fin 4 → ℝ)
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
    let RL := fun μ ν ρ σ : Fin 4 =>
      ∑ k, G μ k * (dΓ ρ k ν σ - dΓ σ k ν ρ + ∑ a, (Γ k ρ a * Γ a ν σ - Γ k σ a * Γ a ν ρ))
    RL μ ν ρ σ = -RL μ ν σ ρ ∧ RL μ ν ρ σ = -RL ν μ ρ σ ∧ RL μ ν ρ σ = RL ρ σ μ ν ∧
      RL μ ν ρ σ + RL μ ρ σ ν + RL μ σ ν ρ = 0 := by
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
  intro RL
  have hk : ∀ μ ν ρ σ : Fin 4, RL μ ν ρ σ = (1 / 2 : ℝ) * (DD ρ ν σ μ + DD ρ σ μ ν - DD ρ μ ν σ)
          - (1 / 2 : ℝ) * (DD σ ν ρ μ + DD σ ρ μ ν - DD σ μ ν ρ)
          - ∑ k, L k ρ μ * Γ k ν σ + ∑ k, L k σ μ * Γ k ν ρ :=
    fun μ ν ρ σ => key μ ν ρ σ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hk, hk]
    simp only [hΓ, Fin.sum_univ_four]
    simp only [hGi, hL, hDD1, hDD2]
    ring
  · rw [hk, hk]
    simp only [hΓ, Fin.sum_univ_four]
    simp only [hGi, hL, hDD1, hDD2]
    ring
  · rw [hk, hk]
    simp only [hΓ, Fin.sum_univ_four]
    simp only [hGi, hL, hDD1, hDD2]
    ring
  · rw [hk, hk, hk]
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


theorem all_sym {g : TensorField2} {U : Set Coord} (hg : IsSpacetimeMetricOn g U) {y : Coord}
    (hy : y ∈ U) (μ ν ρ σ : Fin 4) :
    riemannLower g y μ ν ρ σ = -riemannLower g y μ ν σ ρ ∧
    riemannLower g y μ ν ρ σ = -riemannLower g y ν μ ρ σ ∧
    riemannLower g y μ ν ρ σ = riemannLower g y ρ σ μ ν ∧
    riemannLower g y μ ν ρ σ + riemannLower g y μ ρ σ ν + riemannLower g y μ σ ν ρ = 0 := by
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
  exact all_alg (fun a b => g y a b) (fun a b => (g y)⁻¹ a b) (fun r a b => Lf g r a b y)
    (fun d c a b => partialD d (partialD c (fun w => g w a b)) y)
    (fun ρ k ν σ => partialD ρ (christoffel g k ν σ) y)
    (fun k a b => christoffel g k a b y)
    (fun k a b => chr_eq_L g y k a b) (fun μ a b => G_chr hg hy μ a b) hdΓ
    (lor_inv_symm' (hg.2.2 y hy)) (fun r a b => L_symm hg hy r a b)
    (fun d c a b => pd_pd_comm (cdg hg hy a b) d c) hDD2 μ ν ρ σ

end RSymBuild

open CarrollGR in open scoped ContDiff in
theorem solution (g : TensorField2) (U : Set Coord) (hg : IsSpacetimeMetricOn g U)
    (x : Coord) (hx : x ∈ U) (μ ν ρ σ : Fin 4) :
    riemannLower g x μ ν ρ σ = -riemannLower g x μ ν σ ρ ∧
    riemannLower g x μ ν ρ σ = -riemannLower g x ν μ ρ σ ∧
    riemannLower g x μ ν ρ σ = riemannLower g x ρ σ μ ν ∧
    riemannLower g x μ ν ρ σ + riemannLower g x μ ρ σ ν + riemannLower g x μ σ ν ρ = 0 := by
  exact RSymBuild.all_sym hg hx μ ν ρ σ
