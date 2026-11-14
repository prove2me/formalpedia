-- Prove2me | solution 1 for BosonicLearn.cov_perturbation_gap
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:49:43.299192+00:00
-- url     : https://prove2.me/submissions/7692047e-0120-497e-9dca-d428de7092d9

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
import Theorems.Thm_BosonicLearn_displacementMatrix_prod_mul
import Theorems.Thm_BosonicLearn_displacementMatrix_unitary
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
import Theorems.Thm_BosonicLearn_gaussianAt_of_characteristic
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_BosonicLearn_traceDist_le_one
import Theorems.Thm_BosonicLearn_fugacity_isGaussianState
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_thermal_displaced_kernel
import Theorems.Thm_BosonicLearn_gaussian_bilinear_exp_bound
import Theorems.Thm_BosonicLearn_traceSize_le_of_pairing

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

open BosonicLearn

/-!
# One-sided relative covariance bound under a Loewner gap

`½‖ρ(μ, S') − ρ(μ, S)‖₁ ≤ √2 K_ν ‖S^{-1/2}(S' − S)S^{-1/2}‖_F` for `S ⪰ (½ + ν)·1`, `S' ⪰ S`,
`K_ν = (½ + ν)/√(ν(1 + ν))`.

Notation (interleaved coordinates): `a = ½ + ν`, `r = ν/(1 + ν)`, `κ = (1 − r)/√r`, `K = κa`,
`Θ` the thermal operator with Fock weights `p_w = (1 − r)ⁿ r^{|w|}` (covariance `a·1`),
`R = √(S − a)`, `L = √(S' − S)`, `H = R S⁻¹ L`, `B = a S⁻¹ L` (so `R H + B = L`),
`M = HᵀH + κ BᵀB = L S⁻¹(S − a + κa²)S⁻¹ L`.

* **Part A** (copied from the verified solution of `cov_perturbation_classical`): displacement
  operators on `ℓ²`, nuclear operators, mixtures of displaced nuclear densities.
* **Part C** (same source): Gaussian integrals and the Cameron–Martin change of variables.
* **Part T**: the thermal operator `Θ` (from `fugacity_isGaussianState` with `R = r·1`), and
  `ρ(μ, S) = ∫ D_y Θ D_y⁻¹ dN(μ, S − a)(y)`.
* **Part H**: the weighted Hilbert space `ℓ²(ℕⁿ × ℕⁿ)`: the vectors `v_b = τ^{-1/4} τ_b τ^{-1/4}` with
  `⟨v_b, v_{b'}⟩ = exp(κ⟨b, b'⟩)` (`thermal_displaced_kernel`), their continuity, and
  `Tr_F(D_c τ_b D_c⁻¹ V) = ⟨g, v_b⟩` with `‖g‖ ≤ 1` for a contraction `V` (`pairing_repr`).
* **Parts K1–K4**: exchange of sums and integrals, `exp(s|g|²)` is Gaussian-integrable for `s < ½`,
  the `χ²` identity `‖∫ w v_b − v_0‖² = ∫∫ w w' e^{κ⟨b,b'⟩} − 2∫w + 1`, the kernel integral
  `∫∫ e^{gᵀMg'} ≤ 1 + Tr M²` (`gaussian_bilinear_exp_bound`), the pairing bound
  `|Tr_F((ρ' − ρ)V)| ≤ √(Tr M²)` and `‖ρ' − ρ‖₁ ≤ √(Tr M²)` (`traceSize_le_of_pairing`).
* **Part M**: `Tr M² ≤ K² Tr(S⁻¹ΔS⁻¹Δ)`.
* **Part F**: the two mixtures as integrals over `γ ⊗ γ` and the assembly (case split on
  `K² Tr(S⁻¹ΔS⁻¹Δ) ≤ ½`, with `traceDist_le_one` in the other case).
-/

namespace CovGap

section PartA

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### `ℓ²` basics -/

open Classical in
/-- The basis vector `e_i` of `ℓ²(I)`. -/
private def bv {I : Type} (i : I) : Hilbert I := lp.single 2 i (1 : ℂ)

private lemma bv_apply_self {I : Type} (i : I) : (bv i : Hilbert I) i = 1 := by
  classical
  unfold bv
  rw [lp.single_apply]
  simp

private lemma bv_apply_ne {I : Type} {i j : I} (h : j ≠ i) : (bv i : Hilbert I) j = 0 := by
  classical
  unfold bv
  rw [lp.single_apply]
  simp [h]

private lemma inner_bv_left {I : Type} (i : I) (x : Hilbert I) : inner ℂ (bv i) x = x i := by
  classical
  unfold bv
  rw [lp.inner_single_left]
  simp

private lemma inner_bv_right {I : Type} (i : I) (x : Hilbert I) :
    inner ℂ x (bv i) = star (x i) := by
  classical
  unfold bv
  rw [lp.inner_single_right]
  simp

private lemma norm_bv {I : Type} (i : I) : ‖(bv i : Hilbert I)‖ = 1 := by
  classical
  unfold bv
  rw [lp.norm_single (by norm_num)]
  simp

private lemma hasSum_bv {I : Type} (x : Hilbert I) : HasSum (fun i => x i • (bv i : Hilbert I)) x := by
  classical
  have h := lp.hasSum_single (p := 2) (E := fun _ : I => ℂ) (by norm_num) x
  refine h.congr_fun fun i => ?_
  unfold bv
  rw [← lp.single_smul, smul_eq_mul, mul_one]

/-- Coordinates of the image of a vector under a bounded operator. -/
private lemma clm_apply_hasSum {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) (y : Hilbert I) (u : I) :
    HasSum (fun w => y w * (A (bv w)) u) ((A y) u) := by
  have h := ((innerSL ℂ (bv u)).comp A).hasSum (hasSum_bv y)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_bv_left, map_smul,
    smul_eq_mul] at h
  exact h

/-- A bounded operator on `ℓ²` is determined by its matrix. -/
private lemma clm_ext {I : Type} {A B : Hilbert I →L[ℂ] Hilbert I}
    (h : ∀ v u, (A (bv v)) u = (B (bv v)) u) : A = B := by
  ext y u
  refine (clm_apply_hasSum A y u).unique ?_
  refine (clm_apply_hasSum B y u).congr_fun fun w => ?_
  rw [h]

private lemma lp_sum_sq_le {I : Type} (l : Hilbert I) (G : Finset I) :
    ∑ u ∈ G, ‖l u‖ ^ 2 ≤ ‖l‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) l G
  simpa using h

/-- Cauchy–Schwarz in `ℓ²`, in absolute form. -/
private lemma lp_cs {I : Type} (l r : Hilbert I) :
    Summable (fun u => ‖l u‖ * ‖r u‖) ∧ ∑' u, ‖l u‖ * ‖r u‖ ≤ ‖l‖ * ‖r‖ := by
  have hb : ∀ s : Finset I, ∑ u ∈ s, ‖l u‖ * ‖r u‖ ≤ ‖l‖ * ‖r‖ := by
    intro s
    calc ∑ u ∈ s, ‖l u‖ * ‖r u‖
        ≤ √(∑ u ∈ s, ‖l u‖ ^ 2) * √(∑ u ∈ s, ‖r u‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ ≤ √(‖l‖ ^ 2) * √(‖r‖ ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt (lp_sum_sq_le l s)) (Real.sqrt_le_sqrt (lp_sum_sq_le r s))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖l‖ * ‖r‖ := by rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hs := summable_of_sum_le (fun _ => by positivity) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

/-! ### Nuclear operators on `ℓ²` -/

/-- The matrix of a bounded operator. -/
private def matOf {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) : Matrix I I ℂ :=
  fun u v => (A (bv v)) u

/-- `A = ∑ₖ |lₖ⟩⟨rₖ|` strongly, with `∑ₖ ‖lₖ‖‖rₖ‖ < ∞`. -/
private def IsNuc {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) (l r : ℕ → Hilbert I) : Prop :=
  Summable (fun k => ‖l k‖ * ‖r k‖) ∧ ∀ x, HasSum (fun k => inner ℂ (r k) x • l k) (A x)

/-- The operator `∑ₖ |lₖ⟩⟨rₖ|`. -/
private def nucOp {I : Type} (l r : ℕ → Hilbert I) : Hilbert I →L[ℂ] Hilbert I :=
  ∑' k, (innerSL ℂ (r k)).smulRight (l k)

private lemma nucOp_isNuc {I : Type} (l r : ℕ → Hilbert I)
    (h : Summable (fun k => ‖l k‖ * ‖r k‖)) : IsNuc (nucOp l r) l r := by
  refine ⟨h, fun x => ?_⟩
  have hs : Summable (fun k => (innerSL ℂ (r k)).smulRight (l k)) := by
    refine Summable.of_norm ?_
    refine h.congr fun k => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]
  have h2 := (ContinuousLinearMap.apply ℂ (Hilbert I) x).hasSum hs.hasSum
  simpa [nucOp] using h2

private lemma isNuc_entry {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I}
    (h : IsNuc A l r) (u v : I) : HasSum (fun k => l k u * star (r k v)) (matOf A u v) := by
  have h2 := (innerSL ℂ (bv u)).hasSum (h.2 (bv v))
  simp only [innerSL_apply_apply, inner_bv_left, inner_bv_right, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul] at h2
  refine h2.congr_fun fun k => ?_
  ring

/-- The nuclear expansion of the matrix of a nuclear operator. -/
private def expOf {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I}
    (h : IsNuc A l r) : NuclearExpansion (matOf A) :=
  ⟨l, r, h.1, fun i j => (isNuc_entry h i j).tsum_eq.symm⟩

/-- A nuclear expansion of the matrix of an operator is a nuclear decomposition of the operator. -/
private lemma isNuc_of_exp {I : Type} (A : Hilbert I →L[ℂ] Hilbert I)
    (e : NuclearExpansion (matOf A)) : IsNuc A e.left e.right := by
  have h := nucOp_isNuc e.left e.right e.summable
  have hA : nucOp e.left e.right = A := by
    refine clm_ext fun v u => ?_
    have h1 := (isNuc_entry h u v).tsum_eq
    rw [← e.coefficients u v] at h1
    exact h1.symm
  rwa [hA] at h

/-- Every trace-class array is the matrix of a nuclear operator. -/
private lemma exists_op {I : Type} (X : Matrix I I ℂ) (hX : IsTraceClass X) :
    ∃ (T : Hilbert I →L[ℂ] Hilbert I) (l r : ℕ → Hilbert I), IsNuc T l r ∧ matOf T = X := by
  obtain ⟨e⟩ := hX
  have h := nucOp_isNuc e.left e.right e.summable
  refine ⟨nucOp e.left e.right, e.left, e.right, h, ?_⟩
  funext u v
  rw [e.coefficients u v]
  exact (isNuc_entry h u v).tsum_eq.symm

private lemma isNuc_conj {I : Type} (V : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I} (h : IsNuc A l r) :
    IsNuc ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L (V.symm : Hilbert I →L[ℂ] Hilbert I))
      (fun k => V (l k)) (fun k => V (r k)) := by
  refine ⟨by simpa using h.1, fun x => ?_⟩
  have h2 := (V : Hilbert I →L[ℂ] Hilbert I).hasSum (h.2 (V.symm x))
  refine h2.congr_fun fun k => ?_
  simp [LinearIsometryEquiv.inner_map_eq_flip]

private lemma isNuc_comp {I : Type} (V : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I} (h : IsNuc A l r) :
    IsNuc (A ∘L (V : Hilbert I →L[ℂ] Hilbert I)) l (fun k => V.symm (r k)) := by
  refine ⟨by simpa using h.1, fun x => ?_⟩
  have h2 := h.2 (V x)
  refine h2.congr_fun fun k => ?_
  simp [LinearIsometryEquiv.inner_map_eq_flip]

/-- The trace of a nuclear operator. -/
private lemma isNuc_trace {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I}
    (h : IsNuc A l r) : HasSum (fun u => matOf A u u) (∑' k, inner ℂ (r k) (l k)) := by
  set f : ℕ × I → ℂ := fun p => l p.1 p.2 * star (r p.1 p.2) with hf
  have hfs : Summable f := by
    refine Summable.of_norm ?_
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun k => ?_, ?_⟩
    · refine (lp_cs (l k) (r k)).1.congr fun u => ?_
      simp [hf]
    · refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => norm_nonneg _) (fun k => ?_) h.1
      refine le_trans (le_of_eq ?_) (lp_cs (l k) (r k)).2
      refine tsum_congr fun u => ?_
      simp [hf]
  have h1 : ∀ k, HasSum (fun u => f (k, u)) (inner ℂ (r k) (l k)) := by
    intro k
    have h3 := lp.hasSum_inner (𝕜 := ℂ) (r k) (l k)
    refine h3.congr_fun fun u => ?_
    simp [hf]
  have h2 : ∀ u, HasSum (fun k => f (k, u)) (matOf A u u) := fun u => isNuc_entry h u u
  have h4 : HasSum (fun k => inner ℂ (r k) (l k)) (∑' p, f p) := hfs.hasSum.prod_fiberwise h1
  rw [h4.tsum_eq]
  have h5 : HasSum (fun p : I × ℕ => f p.swap) (∑' p, f p) :=
    (Equiv.prodComm I ℕ).hasSum_iff.mpr hfs.hasSum
  exact h5.prod_fiberwise h2

/-! ### Positivity and densities -/

private lemma quad_form {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) (s : Finset I) (z : I → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, star (z i) * matOf A i j * z j =
      inner ℂ (∑ i ∈ s, z i • (bv i : Hilbert I)) (A (∑ i ∈ s, z i • (bv i : Hilbert I))) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, inner_bv_left]
  unfold matOf
  rw [Complex.star_def]
  ring

/-- Positivity of the quadratic form of an operator. -/
private def IsPos {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) : Prop :=
  ∀ y : Hilbert I, (inner ℂ y (A y)).im = 0 ∧ 0 ≤ (inner ℂ y (A y)).re

private lemma isPos_of_matrix {I : Type} (A : Hilbert I →L[ℂ] Hilbert I)
    (h : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * matOf A i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * matOf A i j * z j).re) : IsPos A := by
  intro y
  have hc : Continuous (fun x : Hilbert I => inner ℂ x (A x)) := by fun_prop
  have ht : Filter.Tendsto (fun s : Finset I => inner ℂ (∑ i ∈ s, y i • (bv i : Hilbert I))
      (A (∑ i ∈ s, y i • (bv i : Hilbert I)))) Filter.atTop (nhds (inner ℂ y (A y))) :=
    (hc.tendsto y).comp (hasSum_bv y)
  have hcl : IsClosed {c : ℂ | c.im = 0 ∧ 0 ≤ c.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  rw [← quad_form]
  exact h s (fun i => y i)

private lemma matOf_isPos {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} (h : IsPos A)
    (s : Finset I) (z : I → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * matOf A i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * matOf A i j * z j).re := by
  rw [quad_form]
  exact h _

private lemma isPos_conj {I : Type} (V : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    {A : Hilbert I →L[ℂ] Hilbert I} (h : IsPos A) :
    IsPos ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L (V.symm : Hilbert I →L[ℂ] Hilbert I)) := by
  intro y
  have h1 : inner ℂ y (((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L
      (V.symm : Hilbert I →L[ℂ] Hilbert I)) y) = inner ℂ (V.symm y) (A (V.symm y)) := by
    rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
    rfl
  rw [h1]
  exact h _

/-- Unitary conjugation maps densities to densities. -/
private lemma density_conj {I : Type} (V : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    {A : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I} (hA : IsNuc A l r)
    (hd : IsDensity (matOf A)) :
    IsDensity (matOf ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L
      (V.symm : Hilbert I →L[ℂ] Hilbert I))) := by
  have hA' := isNuc_conj V hA
  refine ⟨⟨expOf hA'⟩, fun s z => matOf_isPos (isPos_conj V (isPos_of_matrix A hd.2.1)) s z, ?_⟩
  have h1 := Complex.hasSum_re (isNuc_trace hA)
  have h2 := Complex.hasSum_re (isNuc_trace hA')
  have h3 : (∑' k, inner ℂ (V (r k)) (V (l k))) = ∑' k, inner ℂ (r k) (l k) := by simp
  have h5 : (∑' k, inner ℂ (r k) (l k)).re = 1 := by
    rw [← hd.2.2.2]
    exact h1.tsum_eq.symm
  rw [h3, h5] at h2
  exact ⟨h2.summable, h2.tsum_eq⟩

/-! ### The multi-mode displacement operators -/

/-- The kernel of the multi-mode displacement `D(z)`. -/
private def Kd {n : ℕ} (z : Fin n → ℂ) (u w : Fin n → ℕ) : ℂ :=
  ∏ j, displacementMatrix (z j) (u j) (w j)

/-- The Weyl phase. -/
private def ph {n : ℕ} (a b : Fin n → ℂ) : ℂ :=
  ∏ j, Complex.exp ((a j * star (b j) - star (a j) * b j) / 2)

private lemma ph_neg_self {n : ℕ} (z : Fin n → ℂ) : ph (-z) z = 1 := by
  unfold ph
  refine Finset.prod_eq_one fun j _ => ?_
  have h : ((-z) j * star (z j) - star ((-z) j) * z j) / 2 = 0 := by
    simp only [Pi.neg_apply, star_neg]
    ring
  rw [h, Complex.exp_zero]

private lemma Kd_neg {n : ℕ} (z : Fin n → ℂ) (u w : Fin n → ℕ) :
    Kd (-z) w u = star (Kd z u w) := by
  unfold Kd
  rw [star_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (displacementMatrix_unitary (z j) (w j) (u j)).1

private lemma Kd_zero {n : ℕ} (u w : Fin n → ℕ) :
    Kd (0 : Fin n → ℂ) u w = if u = w then 1 else 0 := by
  unfold Kd
  have h : ∀ j, displacementMatrix ((0 : Fin n → ℂ) j) (u j) (w j) =
      if u j = w j then 1 else 0 := fun j => (displacementMatrix_unitary 0 (u j) (w j)).2.1
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_ite_zero]
  simp [funext_iff]

private lemma Kd_mul {n : ℕ} (a b : Fin n → ℂ) (u v : Fin n → ℕ) :
    Summable (fun w : Fin n → ℕ => ‖Kd a u w‖ * ‖Kd b w v‖) ∧
    HasSum (fun w : Fin n → ℕ => Kd a u w * Kd b w v) (ph a b * Kd (a + b) u v) := by
  obtain ⟨h1, h2⟩ := displacementMatrix_prod_mul a b u v
  refine ⟨h1, ?_⟩
  unfold ph Kd
  rw [← Finset.prod_mul_distrib]
  exact h2

private lemma Kd_col_memℓp {n : ℕ} (z : Fin n → ℂ) (w : Fin n → ℕ) :
    Memℓp (fun u : Fin n → ℕ => Kd z u w) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine (Kd_mul (-z) z w w).1.congr fun u => ?_
  rw [Kd_neg, norm_star]
  simp [sq]

/-- The `w`-th column of `D(z)`, as a vector of `ℓ²`. -/
private def colV {n : ℕ} (z : Fin n → ℂ) (w : Fin n → ℕ) : Hilbert (Fin n → ℕ) :=
  ⟨fun u => Kd z u w, Kd_col_memℓp z w⟩

private lemma colV_apply {n : ℕ} (z : Fin n → ℂ) (w u : Fin n → ℕ) : colV z w u = Kd z u w := rfl

private lemma colV_inner {n : ℕ} (z : Fin n → ℂ) (w w' : Fin n → ℕ) :
    inner ℂ (colV z w) (colV z w') = if w = w' then 1 else 0 := by
  rw [lp.inner_eq_tsum]
  have h := (Kd_mul (-z) z w w').2
  rw [neg_add_cancel, Kd_zero, ph_neg_self, one_mul] at h
  rw [← h.tsum_eq]
  refine tsum_congr fun u => ?_
  rw [Kd_neg, colV_apply, colV_apply]
  simp [mul_comm]

private lemma colV_orthonormal {n : ℕ} (z : Fin n → ℂ) : Orthonormal ℂ (colV z) := by
  classical
  rw [orthonormal_iff_ite]
  intro w w'
  convert colV_inner z w w'

/-- The displacement `D(z)` as an isometry of `ℓ²`. -/
private def Dop {n : ℕ} (z : Fin n → ℂ) : Hilbert (Fin n → ℕ) →ₗᵢ[ℂ] Hilbert (Fin n → ℕ) :=
  (colV_orthonormal z).orthogonalFamily.linearIsometry

private lemma Dop_bv {n : ℕ} (z : Fin n → ℂ) (w : Fin n → ℕ) : Dop z (bv w) = colV z w := by
  classical
  unfold Dop bv
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp

private lemma Dop_apply {n : ℕ} (z : Fin n → ℂ) (y : Hilbert (Fin n → ℕ)) (u : Fin n → ℕ) :
    HasSum (fun w => y w * Kd z u w) ((Dop z y) u) := by
  have h := clm_apply_hasSum (Dop z).toContinuousLinearMap y u
  simpa [Dop_bv, colV_apply] using h

/-- The Weyl relation for the displacement operators. -/
private lemma Dop_mul {n : ℕ} (a b : Fin n → ℂ) (x : Hilbert (Fin n → ℕ)) :
    Dop a (Dop b x) = ph a b • Dop (a + b) x := by
  have h : (Dop a).toContinuousLinearMap ∘L (Dop b).toContinuousLinearMap =
      ph a b • (Dop (a + b)).toContinuousLinearMap := by
    refine clm_ext fun v u => ?_
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, Dop_bv,
      smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    refine (Dop_apply a (colV b v) u).unique ?_
    refine (Kd_mul a b u v).2.congr_fun fun w => ?_
    exact mul_comm _ _
  exact DFunLike.congr_fun h x

private lemma colV_zero {n : ℕ} (w : Fin n → ℕ) : colV (0 : Fin n → ℂ) w = bv w := by
  ext u
  rw [colV_apply, Kd_zero]
  by_cases h : u = w
  · subst h
    simp [bv_apply_self]
  · simp [h, bv_apply_ne h]

private lemma Dop_zero {n : ℕ} (x : Hilbert (Fin n → ℕ)) : Dop (0 : Fin n → ℂ) x = x := by
  have h : (Dop (0 : Fin n → ℂ)).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (Hilbert (Fin n → ℕ)) :=
    clm_ext fun v u => by simp [Dop_bv, colV_zero]
  exact DFunLike.congr_fun h x

private lemma Dop_neg_cancel {n : ℕ} (z : Fin n → ℂ) (x : Hilbert (Fin n → ℕ)) :
    Dop (-z) (Dop z x) = x := by
  rw [Dop_mul, ph_neg_self, one_smul, neg_add_cancel, Dop_zero]

/-- The displacement `D(z)` as a unitary of `ℓ²`, with inverse `D(-z)`. -/
private def Deq {n : ℕ} (z : Fin n → ℂ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ) :=
  { toLinearEquiv :=
      { toFun := Dop z
        map_add' := (Dop z).map_add
        map_smul' := (Dop z).map_smul
        invFun := Dop (-z)
        left_inv := Dop_neg_cancel z
        right_inv := fun x => by
          have h := Dop_neg_cancel (-z) x
          rwa [neg_neg] at h }
    norm_map' := (Dop z).norm_map }

private lemma Deq_apply {n : ℕ} (z : Fin n → ℂ) (x : Hilbert (Fin n → ℕ)) :
    Deq z x = Dop z x := rfl

private lemma Deq_symm_apply {n : ℕ} (z : Fin n → ℂ) (x : Hilbert (Fin n → ℕ)) :
    (Deq z).symm x = Dop (-z) x := rfl

/-! ### The characteristic function -/

/-- The displacement amplitude of the Weyl operator `W(ξ)`. -/
private def zetaOf {n : ℕ} (ξ : Fin n × Fin 2 → ℝ) : Fin n → ℂ :=
  fun j => (-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- The displacement amplitude shifting the mean by `δ`. -/
private def zOf {n : ℕ} (δ : Fin n × Fin 2 → ℝ) : Fin n → ℂ :=
  fun j => ((δ (j, 0) : ℂ) + Complex.I * (δ (j, 1) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- The characteristic function of a nuclear operator is `∑ₖ ⟨rₖ, W(ξ) lₖ⟩`. -/
private lemma char_eq {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (matOf A) ξ = ∑' k, inner ℂ (r k) (Dop (zetaOf ξ) (l k)) := by
  have h1 : ∀ u : Fin n → ℕ, HasSum (fun v => matOf A u v * oscillatorWeylKernel ξ v u)
      (matOf (A ∘L ((Deq (zetaOf ξ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
        Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))) u u) := by
    intro u
    have h := clm_apply_hasSum A (Dop (zetaOf ξ) (bv u)) u
    have h' : matOf (A ∘L ((Deq (zetaOf ξ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
        Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))) u u = (A (Dop (zetaOf ξ) (bv u))) u := rfl
    rw [h']
    refine h.congr_fun fun v => ?_
    rw [Dop_bv, colV_apply, mul_comm]
    rfl
  unfold oscillatorCharacteristic
  rw [tsum_congr fun u => (h1 u).tsum_eq, (isNuc_trace (isNuc_comp (Deq (zetaOf ξ)) hA)).tsum_eq]
  refine tsum_congr fun k => ?_
  rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm, Deq_apply]

private lemma phase_alg (a a' c c' s : ℂ) (hs : s * s = 2) :
    (a / s * (c' / s) - a' / s * (c / s)) / 2 +
      (-(c / s) * (a' / s + c' / s) - -(c' / s) * (a / s + c / s)) / 2 = (a * c' - a' * c) / 2 := by
  have h : ∀ x y : ℂ, x / s * (y / s) = x * y / 2 := fun x y => by rw [div_mul_div_comm, hs]
  rw [show -(c / s) * (a' / s + c' / s) = -(c / s * (a' / s)) - c / s * (c' / s) by ring,
    show -(c' / s) * (a / s + c / s) = -(c' / s * (a / s)) - c' / s * (c / s) by ring,
    h, h, h, h, h, h]
  ring

private lemma phase_eq {n : ℕ} (δ ξ : Fin n × Fin 2 → ℝ) :
    ph (zetaOf ξ) (zOf δ) * ph (-zOf δ) (zetaOf ξ + zOf δ) =
      Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  unfold ph meanForm
  rw [← Finset.prod_mul_distrib, Fintype.sum_prod_type]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_add, Fin.sum_univ_two]
  congr 1
  simp only [zetaOf, zOf, Pi.neg_apply, Pi.add_apply, Complex.star_def, map_div₀, map_add, map_mul,
    map_neg, Complex.conj_ofReal, Complex.conj_I]
  rw [phase_alg _ _ _ _ _ hs]
  ring

/-- The characteristic function of the displaced operator. -/
private lemma char_conj {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (δ ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic
        (matOf (((Deq (zOf δ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
          Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) ∘L A ∘L
          (((Deq (zOf δ)).symm : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
          Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)))) ξ =
      Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) * oscillatorCharacteristic (matOf A) ξ := by
  rw [char_eq (isNuc_conj (Deq (zOf δ)) hA), char_eq hA, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h : (Deq (zOf δ)).symm (Dop (zetaOf ξ) (Deq (zOf δ) (l k))) =
      Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) • Dop (zetaOf ξ) (l k) := by
    rw [Deq_symm_apply, Deq_apply, Dop_mul (zetaOf ξ), map_smul, Dop_mul, smul_smul, phase_eq,
      neg_add_cancel_comm_assoc]
  rw [LinearIsometryEquiv.inner_map_eq_flip, h, inner_smul_right]


/-! ### Uniform bounds -/

private lemma matOf_norm_le {I : Type} (B : Hilbert I →L[ℂ] Hilbert I) (u v : I) :
    ‖matOf B u v‖ ≤ ‖B‖ := by
  unfold matOf
  calc ‖(B (bv v)) u‖ ≤ ‖B (bv v)‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖B‖ * ‖(bv v : Hilbert I)‖ := B.le_opNorm _
    _ = ‖B‖ := by rw [norm_bv, mul_one]

private lemma matOf_eq_adjoint {I : Type} (B : Hilbert I →L[ℂ] Hilbert I) (u v : I) :
    matOf B u v = star ((ContinuousLinearMap.adjoint B (bv u)) v) := by
  rw [← inner_bv_right, ContinuousLinearMap.adjoint_inner_left, inner_bv_left]
  rfl

/-- Rows of the matrix of a bounded operator are square summable, uniformly. -/
private lemma matOf_row_bound {I : Type} (B : Hilbert I →L[ℂ] Hilbert I) (y : Hilbert I) (u : I)
    (s : Finset I) : ∑ v ∈ s, ‖matOf B u v * y v‖ ≤ ‖B‖ * ‖y‖ := by
  have h := lp_cs (ContinuousLinearMap.adjoint B (bv u)) y
  calc ∑ v ∈ s, ‖matOf B u v * y v‖
      = ∑ v ∈ s, ‖(ContinuousLinearMap.adjoint B (bv u)) v‖ * ‖y v‖ := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [norm_mul, matOf_eq_adjoint, norm_star]
    _ ≤ ∑' v, ‖(ContinuousLinearMap.adjoint B (bv u)) v‖ * ‖y v‖ :=
        h.1.sum_le_tsum s fun _ _ => by positivity
    _ ≤ ‖ContinuousLinearMap.adjoint B (bv u)‖ * ‖y‖ := h.2
    _ ≤ ‖B‖ * ‖y‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖ContinuousLinearMap.adjoint B (bv u)‖
            ≤ ‖ContinuousLinearMap.adjoint B‖ * ‖(bv u : Hilbert I)‖ :=
              (ContinuousLinearMap.adjoint B).le_opNorm _
          _ = ‖B‖ := by rw [norm_bv, mul_one, LinearIsometryEquiv.norm_map]

/-- The diagonal of the matrix of a nuclear operator is absolutely summable, with the nuclear
bound. -/
private lemma isNuc_diag_bound {I : Type} {N : Hilbert I →L[ℂ] Hilbert I} {l r : ℕ → Hilbert I}
    (h : IsNuc N l r) (s : Finset I) :
    ∑ u ∈ s, ‖matOf N u u‖ ≤ ∑' k, ‖l k‖ * ‖r k‖ := by
  have hk : ∀ u, Summable (fun k => ‖l k u‖ * ‖r k u‖) := fun u =>
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
        (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)) h.1
  have h1 : ∀ u, ‖matOf N u u‖ ≤ ∑' k, ‖l k u‖ * ‖r k u‖ := by
    intro u
    rw [← (isNuc_entry h u u).tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · simpa using hk u
    · refine tsum_congr fun k => ?_
      simp
  calc ∑ u ∈ s, ‖matOf N u u‖ ≤ ∑ u ∈ s, ∑' k, ‖l k u‖ * ‖r k u‖ :=
        Finset.sum_le_sum fun u _ => h1 u
    _ = ∑' k, ∑ u ∈ s, ‖l k u‖ * ‖r k u‖ := (Summable.tsum_finsetSum fun u _ => hk u).symm
    _ ≤ ∑' k, ‖l k‖ * ‖r k‖ := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_sum fun u _ => hk u) h.1
        exact ((lp_cs (l k) (r k)).1.sum_le_tsum s (fun _ _ => by positivity)).trans
          (lp_cs (l k) (r k)).2

/-! ### Exchange of a bounded series with an integral -/

private lemma fubini_bdd {Ω : Type} [MeasurableSpace Ω] (γ : Measure Ω) [IsFiniteMeasure γ]
    {ι : Type} [Countable ι] (F : ι → Ω → ℂ) (C : ℝ) (hm : ∀ i, Measurable (F i))
    (hb : ∀ x (s : Finset ι), ∑ i ∈ s, ‖F i x‖ ≤ C) :
    Measurable (fun x => ∑' i, F i x) ∧ (∀ x, Summable (fun i => F i x)) ∧
      Integrable (fun x => ∑' i, F i x) γ ∧
      HasSum (fun i => ∫ x, F i x ∂γ) (∫ x, ∑' i, F i x ∂γ) := by
  have hsum : ∀ x, Summable (fun i => ‖F i x‖) := fun x =>
    summable_of_sum_le (fun _ => norm_nonneg _) (hb x)
  have hsum' : ∀ x, Summable (fun i => F i x) := fun x => (hsum x).of_norm
  have hle : ∀ i x, ‖F i x‖ ≤ C := fun i x => by simpa using hb x {i}
  have hint : ∀ i, Integrable (F i) γ := fun i =>
    Integrable.of_bound (hm i).aestronglyMeasurable C (Filter.Eventually.of_forall (hle i))
  have hmeas : Measurable (fun x => ∑' i, F i x) := by
    refine measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset ι) x => ∑ i ∈ s, F i x)
      (fun s => Finset.measurable_sum s fun i _ => hm i) ?_
    exact tendsto_pi_nhds.mpr fun x => (hsum' x).hasSum
  refine ⟨hmeas, hsum', ?_, ?_⟩
  · refine Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => ?_)
    exact (norm_tsum_le_tsum_norm (hsum x)).trans ((hsum x).tsum_le_of_sum_le (hb x))
  · refine hasSum_integral_of_summable_integral_norm hint ?_
    refine summable_of_sum_le (c := ∫ _, C ∂γ) (fun i => integral_nonneg fun _ => norm_nonneg _)
      fun s => ?_
    rw [← integral_finsetSum s fun i _ => (hint i).norm]
    exact integral_mono (integrable_finsetSum s fun i _ => (hint i).norm) (integrable_const C)
      fun x => hb x s

/-! ### Measurability of the displaced arrays -/

private lemma dm_continuous (m k : ℕ) : Continuous (fun z : ℂ => displacementMatrix z m k) := by
  unfold displacementMatrix
  fun_prop

private lemma Kd_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (X : Ω → Fin n × Fin 2 → ℝ)
    (hX : ∀ a, Measurable (fun ω => X ω a)) (u w : Fin n → ℕ) :
    Measurable (fun ω => Kd (zOf (X ω)) u w) := by
  unfold Kd
  refine Finset.measurable_prod _ fun j _ => ?_
  refine (dm_continuous (u j) (w j)).measurable.comp ?_
  unfold zOf
  have h0 := hX (j, 0)
  have h1 := hX (j, 1)
  fun_prop

private lemma Dop_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (X : Ω → Fin n × Fin 2 → ℝ)
    (hX : ∀ a, Measurable (fun ω => X ω a)) (y : Hilbert (Fin n → ℕ)) (u : Fin n → ℕ) :
    Measurable (fun ω => ((Dop (zOf (X ω)) y) u : ℂ)) := by
  refine measurable_of_tendsto_metrizable' Filter.atTop
    (f := fun (s : Finset (Fin n → ℕ)) ω => ∑ w ∈ s, y w * Kd (zOf (X ω)) u w)
    (fun s => Finset.measurable_sum s fun w _ => (Kd_measurable X hX u w).const_mul _) ?_
  exact tendsto_pi_nhds.mpr fun ω => Dop_apply (zOf (X ω)) y u

/-! ### The displaced operators -/

/-- The conjugate `D(z_δ) A D(z_δ)⁻¹` of an operator by the displacement shifting the mean by `δ`. -/
private def cj {n : ℕ} (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (δ : Fin n × Fin 2 → ℝ) : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ) :=
  ((Deq (zOf δ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
    Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) ∘L A ∘L
    (((Deq (zOf δ)).symm : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
      Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))

private lemma cj_isNuc {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (δ : Fin n × Fin 2 → ℝ) :
    IsNuc (cj A δ) (fun k => Deq (zOf δ) (l k)) (fun k => Deq (zOf δ) (r k)) :=
  isNuc_conj (Deq (zOf δ)) hA

private lemma cj_norm_le {n : ℕ} (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (δ : Fin n × Fin 2 → ℝ) : ‖cj A δ‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
  have h : ‖cj A δ x‖ = ‖A ((Deq (zOf δ)).symm x)‖ := by
    unfold cj
    simp
  rw [h]
  refine (A.le_opNorm _).trans (le_of_eq ?_)
  rw [LinearIsometryEquiv.norm_map]

private lemma cj_density {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (hd : IsDensity (matOf A))
    (δ : Fin n × Fin 2 → ℝ) : IsDensity (matOf (cj A δ)) :=
  density_conj (Deq (zOf δ)) hA hd

private lemma cj_char {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (δ ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (matOf (cj A δ)) ξ =
      Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) * oscillatorCharacteristic (matOf A) ξ :=
  char_conj hA δ ξ

private lemma cj_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (X : Ω → Fin n × Fin 2 → ℝ)
    (hX : ∀ a, Measurable (fun ω => X ω a)) {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (u v : Fin n → ℕ) :
    Measurable (fun ω => matOf (cj A (X ω)) u v) := by
  refine measurable_of_tendsto_metrizable' Filter.atTop
    (f := fun (s : Finset ℕ) ω => ∑ k ∈ s,
      (Dop (zOf (X ω)) (l k)) u * star ((Dop (zOf (X ω)) (r k)) v))
    (fun s => Finset.measurable_sum s fun k _ =>
      (Dop_measurable X hX (l k) u).mul
        (continuous_star.measurable.comp (Dop_measurable X hX (r k) v))) ?_
  exact tendsto_pi_nhds.mpr fun ω => isNuc_entry (cj_isNuc hA (X ω)) u v

/-- The row sums of the Weyl pairing. -/
private lemma row_hasSum {n : ℕ} (B : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (ξ : Fin n × Fin 2 → ℝ) (u : Fin n → ℕ) :
    HasSum (fun v => matOf B u v * oscillatorWeylKernel ξ v u)
      (matOf (B ∘L ((Deq (zetaOf ξ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
        Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))) u u) := by
  have h := clm_apply_hasSum B (Dop (zetaOf ξ) (bv u)) u
  have h' : matOf (B ∘L ((Deq (zetaOf ξ) : Hilbert (Fin n → ℕ) ≃ₗᵢ[ℂ] Hilbert (Fin n → ℕ)) :
      Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))) u u = (B (Dop (zetaOf ξ) (bv u))) u := rfl
  rw [h']
  refine h.congr_fun fun v => ?_
  rw [Dop_bv, colV_apply, mul_comm]
  rfl

private lemma norm_colV {n : ℕ} (z : Fin n → ℂ) (w : Fin n → ℕ) : ‖colV z w‖ = 1 :=
  (colV_orthonormal z).1 w

/-- Uniform bound for the inner series of the Weyl pairing of the displaced arrays. -/
private lemma inner_bound {n : ℕ} (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (δ ξ : Fin n × Fin 2 → ℝ) (u : Fin n → ℕ) (s : Finset (Fin n → ℕ)) :
    ∑ v ∈ s, ‖matOf (cj A δ) u v * oscillatorWeylKernel ξ v u‖ ≤ ‖A‖ := by
  have h := matOf_row_bound (cj A δ) (colV (zetaOf ξ) u) u s
  rw [norm_colV, mul_one] at h
  exact h.trans (cj_norm_le A δ)

/-- Uniform bound for the outer series of the Weyl pairing of the displaced arrays. -/
private lemma outer_bound {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (δ ξ : Fin n × Fin 2 → ℝ)
    (s : Finset (Fin n → ℕ)) :
    ∑ u ∈ s, ‖∑' v, matOf (cj A δ) u v * oscillatorWeylKernel ξ v u‖ ≤ ∑' k, ‖l k‖ * ‖r k‖ := by
  have h := isNuc_diag_bound (isNuc_comp (Deq (zetaOf ξ)) (cj_isNuc hA δ)) s
  simp only [LinearIsometryEquiv.norm_map] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [(row_hasSum (cj A δ) ξ u).tsum_eq]

/-- Uniform bound for the diagonal of the displaced arrays. -/
private lemma diag_bound {n : ℕ} {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (δ : Fin n × Fin 2 → ℝ)
    (s : Finset (Fin n → ℕ)) :
    ∑ u ∈ s, ‖matOf (cj A δ) u u‖ ≤ ∑' k, ‖l k‖ * ‖r k‖ := by
  have h := isNuc_diag_bound (cj_isNuc hA δ) s
  simpa only [LinearIsometryEquiv.norm_map] using h


/-! ### Mixing displaced copies of a nuclear density -/

/-- The mixture of the displaced copies `D(X ω) A D(X ω)⁻¹` of a nuclear density over a probability
space is a density, with characteristic function `E[exp(i ξ·X)] χ_A(ξ)`. -/
private lemma mix_explicit {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (γ : Measure Ω)
    [IsProbabilityMeasure γ] (X : Ω → Fin n × Fin 2 → ℝ) (hX : ∀ a, Measurable (fun ω => X ω a))
    {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)} {l r : ℕ → Hilbert (Fin n → ℕ)}
    (hA : IsNuc A l r) (hAd : IsDensity (matOf A)) :
    IsDensity (fun u v => ∫ ω, matOf (cj A (X ω)) u v ∂γ) ∧
    ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic (fun u v => ∫ ω, matOf (cj A (X ω)) u v ∂γ) ξ =
        (∫ ω, Complex.exp (Complex.I * (meanForm (X ω) ξ : ℂ)) ∂γ) *
          oscillatorCharacteristic (matOf A) ξ := by
  have hmeas : ∀ u v, Measurable (fun ω => matOf (cj A (X ω)) u v) := cj_measurable X hX hA
  have hint : ∀ u v, Integrable (fun ω => matOf (cj A (X ω)) u v) γ := fun u v =>
    Integrable.of_bound (hmeas u v).aestronglyMeasurable ‖A‖
      (Filter.Eventually.of_forall fun ω => (matOf_norm_le _ u v).trans (cj_norm_le A (X ω)))
  have hdens : ∀ ω, IsDensity (matOf (cj A (X ω))) := fun ω => cj_density hA hAd (X ω)
  set R : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ := fun u v => ∫ ω, matOf (cj A (X ω)) u v ∂γ with hR
  -- positivity
  have hpsd : ∀ (s : Finset (Fin n → ℕ)) (z : (Fin n → ℕ) → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * R i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * R i j * z j).re := by
    intro s z
    have hQint : Integrable (fun ω => ∑ i ∈ s, ∑ j ∈ s,
        star (z i) * matOf (cj A (X ω)) i j * z j) γ :=
      integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
        ((hint i j).const_mul _).mul_const _
    have hQ : ∑ i ∈ s, ∑ j ∈ s, star (z i) * R i j * z j =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, star (z i) * matOf (cj A (X ω)) i j * z j ∂γ := by
      rw [integral_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
        ((hint i j).const_mul _).mul_const _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum s fun j _ => ((hint i j).const_mul _).mul_const _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const, integral_const_mul]
    rw [hQ]
    have him := Complex.imCLM.integral_comp_comm hQint
    have hre := Complex.reCLM.integral_comp_comm hQint
    simp only [Complex.imCLM_apply, Complex.reCLM_apply] at him hre
    rw [← him, ← hre]
    refine ⟨?_, integral_nonneg fun ω => ((hdens ω).2.1 s z).2⟩
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => ((hdens ω).2.1 s z).1)]
    simp
  -- trace
  obtain ⟨-, hds, hdint, hdsum⟩ := fubini_bdd γ (fun u ω => matOf (cj A (X ω)) u u)
    (∑' k, ‖l k‖ * ‖r k‖) (fun u => hmeas u u) (fun ω s => diag_bound hA (X ω) s)
  have htr1 : ∀ ω, (∑' u, matOf (cj A (X ω)) u u).re = 1 := by
    intro ω
    rw [Complex.re_tsum (hds ω)]
    exact (hdens ω).2.2.2
  have htr : HasSum (fun u => (R u u).re) 1 := by
    have h := Complex.hasSum_re hdsum
    have hre := Complex.reCLM.integral_comp_comm hdint
    simp only [Complex.reCLM_apply] at hre
    rw [← hre, integral_congr_ae (Filter.Eventually.of_forall htr1)] at h
    simpa using h
  have hRd : IsDensity R := isDensity_of_posSemidef R hpsd htr.summable htr.tsum_eq
  refine ⟨hRd, fun ξ => ?_⟩
  -- the characteristic function
  have hin : ∀ u, Measurable (fun ω => ∑' v, matOf (cj A (X ω)) u v * oscillatorWeylKernel ξ v u) ∧
      HasSum (fun v => R u v * oscillatorWeylKernel ξ v u)
        (∫ ω, ∑' v, matOf (cj A (X ω)) u v * oscillatorWeylKernel ξ v u ∂γ) := by
    intro u
    obtain ⟨hm, -, -, hs⟩ := fubini_bdd γ
      (fun v ω => matOf (cj A (X ω)) u v * oscillatorWeylKernel ξ v u) ‖A‖
      (fun v => (hmeas u v).mul_const _) (fun ω s => inner_bound A (X ω) ξ u s)
    refine ⟨hm, hs.congr_fun fun v => ?_⟩
    exact (integral_mul_const _ _).symm
  obtain ⟨-, -, -, hout⟩ := fubini_bdd γ
    (fun u ω => ∑' v, matOf (cj A (X ω)) u v * oscillatorWeylKernel ξ v u)
    (∑' k, ‖l k‖ * ‖r k‖) (fun u => (hin u).1) (fun ω s => outer_bound hA (X ω) ξ s)
  have hchi : ∀ ω, ∑' u, ∑' v, matOf (cj A (X ω)) u v * oscillatorWeylKernel ξ v u =
      Complex.exp (Complex.I * (meanForm (X ω) ξ : ℂ)) * oscillatorCharacteristic (matOf A) ξ :=
    fun ω => cj_char hA (X ω) ξ
  rw [show oscillatorCharacteristic R ξ = ∑' u, ∑' v, R u v * oscillatorWeylKernel ξ v u from rfl,
    tsum_congr fun u => (hin u).2.tsum_eq, hout.tsum_eq,
    integral_congr_ae (Filter.Eventually.of_forall hchi), integral_mul_const]


end

end PartA

section PartC

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

noncomputable section

/-! ### Gaussian integrals -/

/-- The complex Gaussian integral `∫ exp(a·z) dγ(z) = exp(a·a/2)` for the standard Gaussian. -/
private lemma gauss_cexp {ι : Type} [Fintype ι] (a : ι → ℂ) :
    ∫ z : EuclideanSpace ℝ ι, Complex.exp (∑ i, a i * (z i : ℂ))
      ∂(stdGaussian (EuclideanSpace ℝ ι)) = Complex.exp (∑ i, a i ^ 2 / 2) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Complex.exp (a i * (x : ℂ)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := complexMGF_id_gaussianReal (μ := 0) (v := 1) (a i)
  simpa [complexMGF] using h

/-- The moment generating function of the standard Gaussian. -/
private lemma gauss_exp {ι : Type} [Fintype ι] (h : ι → ℝ) :
    Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (∑ i, h i * z i))
      (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ z : EuclideanSpace ℝ ι, Real.exp (∑ i, h i * z i) ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      Real.exp ((∑ i, h i ^ 2) / 2) := by
  have h1 := gauss_cexp (fun i => (h i : ℂ))
  have h2 : ∀ z : EuclideanSpace ℝ ι, Complex.exp (∑ i, (h i : ℂ) * (z i : ℂ)) =
      ((Real.exp (∑ i, h i * z i) : ℝ) : ℂ) := by
    intro z
    push_cast
    rfl
  have h3 : Complex.exp (∑ i, (h i : ℂ) ^ 2 / 2) = ((Real.exp ((∑ i, h i ^ 2) / 2) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_div]
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_complex_ofReal, h3] at h1
  have h4 := Complex.ofReal_injective h1
  refine ⟨?_, h4⟩
  by_contra hni
  rw [integral_undef hni] at h4
  exact (Real.exp_pos _).ne h4

private lemma gauss_cosh {ι : Type} [Fintype ι] (h : ι → ℝ) :
    Integrable (fun z : EuclideanSpace ℝ ι => Real.cosh (∑ i, h i * z i))
      (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ z : EuclideanSpace ℝ ι, Real.cosh (∑ i, h i * z i) ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      Real.exp ((∑ i, h i ^ 2) / 2) := by
  obtain ⟨h1, h2⟩ := gauss_exp h
  obtain ⟨h3, h4⟩ := gauss_exp (fun i => -h i)
  have e1 : ∀ z : EuclideanSpace ℝ ι, ∑ i, -h i * z i = -∑ i, h i * z i := by
    intro z
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (-h i) ^ 2 = ∑ i, h i ^ 2 := Finset.sum_congr rfl fun i _ => by ring
  simp only [e1, e2] at h3 h4
  have e3 : (fun z : EuclideanSpace ℝ ι => Real.cosh (∑ i, h i * z i)) =
      fun z => (Real.exp (∑ i, h i * z i) + Real.exp (-∑ i, h i * z i)) / 2 := by
    funext z
    rw [Real.cosh_eq]
  rw [e3]
  refine ⟨(h1.add h3).div_const 2, ?_⟩
  rw [integral_div, integral_add h1 h3, h2, h4]
  ring

/-! ### Fubini for non-negative functions with explicit inner integrals -/

private lemma prod_integrable_of_nonneg {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (f : α × β → ℝ) (hf : Measurable f)
    (h0 : ∀ p, 0 ≤ f p) (g : α → ℝ) (h1 : ∀ x, Integrable (fun y => f (x, y)) ν)
    (h2 : ∀ x, ∫ y, f (x, y) ∂ν = g x) (hg : Integrable g μ) :
    Integrable f (μ.prod ν) ∧ ∫ p, f p ∂(μ.prod ν) = ∫ x, g x ∂μ := by
  have hint : Integrable f (μ.prod ν) := by
    rw [integrable_prod_iff hf.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall h1, ?_⟩
    have h3 : (fun x => ∫ y, ‖f (x, y)‖ ∂ν) = g := by
      funext x
      rw [← h2 x]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs, abs_of_nonneg (h0 (x, y))]
    rwa [h3]
  refine ⟨hint, ?_⟩
  rw [integral_prod f hint]
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-! ### The Cameron–Martin weight -/

/-- The Cameron–Martin weight `w(x, z) = exp(⟪h_x, z⟫ - ‖h_x‖²/2)`. -/
private def cmw {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  Real.exp (∑ i, hh ω.1 i * ω.2 i - (∑ i, hh ω.1 i ^ 2) / 2)

private lemma cmw_pos {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : 0 < cmw hh ω := Real.exp_pos _

private lemma cmw_measurable {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ)
    (hhm : Measurable hh) : Measurable (cmw hh) := by
  unfold cmw
  have h1 : ∀ i, Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => hh ω.1 i) :=
    fun i => (measurable_pi_apply i).comp (hhm.comp measurable_fst)
  have h2 : ∀ i, Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => ω.2 i) :=
    fun i => by fun_prop
  refine Real.measurable_exp.comp ?_
  refine Measurable.sub ?_ ?_
  · exact Finset.measurable_sum _ fun i _ => (h1 i).mul (h2 i)
  · exact (Finset.measurable_sum _ fun i _ => (h1 i).pow_const 2).div_const 2

private lemma cmw_inner {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ) (x : EuclideanSpace ℝ ι) :
    Integrable (fun z : EuclideanSpace ℝ ι => cmw hh (x, z)) (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ z : EuclideanSpace ℝ ι, cmw hh (x, z) ∂(stdGaussian (EuclideanSpace ℝ ι)) = 1 := by
  obtain ⟨h1, h2⟩ := gauss_exp (hh x)
  have e : (fun z : EuclideanSpace ℝ ι => cmw hh (x, z)) =
      fun z => Real.exp (∑ i, hh x i * z i) * Real.exp (-((∑ i, hh x i ^ 2) / 2)) := by
    funext z
    unfold cmw
    rw [← Real.exp_add]
    congr 1
  rw [e]
  refine ⟨h1.mul_const _, ?_⟩
  rw [integral_mul_const, h2, ← Real.exp_add]
  simp

private lemma cmw_integrable {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ)
    (hhm : Measurable hh) (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] :
    Integrable (cmw hh) (μ.prod (stdGaussian (EuclideanSpace ℝ ι))) :=
  (prod_integrable_of_nonneg μ (stdGaussian (EuclideanSpace ℝ ι)) (cmw hh)
    (cmw_measurable hh hhm) (fun p => (cmw_pos hh p).le) (fun _ => 1)
    (fun x => (cmw_inner hh x).1) (fun x => (cmw_inner hh x).2) (integrable_const 1)).1

/-! ### The square root of a positive semidefinite matrix -/

open scoped MatrixOrder in
private lemma sqrt_sym {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) :
    (CFC.sqrt T)ᵀ = CFC.sqrt T := by
  have hpsd : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  have := hpsd.isHermitian.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

open scoped MatrixOrder in
private lemma sqrt_mul_self {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (hT : T.PosSemidef) :
    CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self _ hT.nonneg

private lemma dot_sym {ι : Type} [Fintype ι] (R : Matrix ι ι ℝ) (hR : Rᵀ = R) (a b : ι → ℝ) :
    (R *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (R *ᵥ b) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hR]

private lemma inner_eq_sum {ι : Type} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    inner ℝ x y = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-! ### The tilted measure -/

private lemma integral_tilt_map {Ω E' : Type} [MeasurableSpace Ω] [MeasurableSpace E'] (P : Measure Ω)
    (w : Ω → ℝ) (hw : Measurable w) (hw0 : ∀ ω, 0 ≤ w ω) (X : Ω → E') (hX : Measurable X)
    (f : E' → ℂ) (hf : Measurable f) :
    ∫ y, f y ∂((P.withDensity (fun ω => ENNReal.ofReal (w ω))).map X) =
      ∫ ω, ((w ω : ℝ) : ℂ) * f (X ω) ∂P := by
  rw [integral_map hX.aemeasurable hf.aestronglyMeasurable]
  have h := integral_withDensity_eq_integral_smul (μ := P) (f := fun ω => (w ω).toNNReal)
    hw.real_toNNReal (fun ω => f (X ω))
  refine h.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show (w ω).toNNReal • f (X ω) = ((w ω : ℝ) : ℂ) * f (X ω)
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hw0 ω), Complex.real_smul]

open scoped MatrixOrder in
/-- The affine map `(x, z) ↦ m + √T z + b_x`. -/
private def tiltX {ι : Type} [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι) (T : Matrix ι ι ℝ)
    (bb : EuclideanSpace ℝ ι → ι → ℝ) (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  m + WithLp.toLp 2 ((CFC.sqrt T) *ᵥ ω.2.ofLp) + WithLp.toLp 2 (bb ω.1)

open scoped MatrixOrder in
private lemma tiltX_measurable {ι : Type} [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (T : Matrix ι ι ℝ) (bb : EuclideanSpace ℝ ι → ι → ℝ) (hbm : Measurable bb) :
    Measurable (tiltX m T bb) := by
  have h1 : Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt T) ω.2) := by fun_prop
  have h2 : Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      (WithLp.toLp 2 (bb ω.1) : EuclideanSpace ℝ ι)) :=
    (WithLp.measurable_toLp 2 _).comp (hbm.comp measurable_fst)
  exact (measurable_const.add h1).add h2

open scoped MatrixOrder in
/-- Cameron–Martin: tilting the standard Gaussian by `h_x` and displacing by `b_x`, with
`√T h_x + b_x = x`, turns `N(0, Δ) ⊗ γ` into `N(m, T + Δ)` under `(x, z) ↦ m + √T z + b_x`. -/
private theorem tilt_measure {ι : Type} [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (T Δ : Matrix ι ι ℝ) (hT : T.PosSemidef) (hΔ : Δ.PosSemidef)
    (hh bb : EuclideanSpace ℝ ι → ι → ℝ) (hhm : Measurable hh) (hbm : Measurable bb)
    (hsplit : ∀ x, (CFC.sqrt T) *ᵥ (hh x) + bb x = x.ofLp) :
    (((multivariateGaussian 0 Δ).prod (stdGaussian (EuclideanSpace ℝ ι))).withDensity
        (fun ω => ENNReal.ofReal (cmw hh ω))).map (tiltX m T bb) =
      multivariateGaussian m (T + Δ) := by
  have hwint : Integrable (cmw hh)
      ((multivariateGaussian 0 Δ).prod (stdGaussian (EuclideanSpace ℝ ι))) :=
    cmw_integrable hh hhm _
  have hXm := tiltX_measurable m T bb hbm
  have hfin1 : IsFiniteMeasure (((multivariateGaussian 0 Δ).prod
      (stdGaussian (EuclideanSpace ℝ ι))).withDensity (fun ω => ENNReal.ofReal (cmw hh ω))) :=
    isFiniteMeasure_withDensity_ofReal hwint.2
  have hfin2 : IsFiniteMeasure ((((multivariateGaussian 0 Δ).prod
      (stdGaussian (EuclideanSpace ℝ ι))).withDensity
        (fun ω => ENNReal.ofReal (cmw hh ω))).map (tiltX m T bb)) :=
    Measure.isFiniteMeasure_map _ _
  refine Measure.ext_of_charFun ?_
  funext ξ
  rw [charFun_multivariateGaussian (hT.add hΔ), charFun_apply,
    integral_tilt_map _ (cmw hh) (cmw_measurable hh hhm) (fun ω => (cmw_pos hh ω).le) _ hXm _
      (by fun_prop)]
  have hRs := sqrt_sym T
  have hRR := sqrt_mul_self T hT
  set R := CFC.sqrt T with hR
  have hint : Integrable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ((cmw hh ω : ℝ) : ℂ) * Complex.exp ((inner ℝ (tiltX m T bb ω) ξ : ℝ) * Complex.I))
      ((multivariateGaussian 0 Δ).prod (stdGaussian (EuclideanSpace ℝ ι))) := by
    refine Integrable.mono' hwint ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have h1 := cmw_measurable hh hhm
      have h2 : Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
          inner ℝ (tiltX m T bb ω) ξ) := by fun_prop
      exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (cmw_pos hh ω)]
  rw [integral_prod _ hint]
  -- the inner integral
  have hin : ∀ x : EuclideanSpace ℝ ι,
      ∫ z : EuclideanSpace ℝ ι, ((cmw hh (x, z) : ℝ) : ℂ) *
          Complex.exp ((inner ℝ (tiltX m T bb (x, z)) ξ : ℝ) * Complex.I)
        ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      Complex.exp ((inner ℝ ξ m : ℝ) * Complex.I - ((ξ.ofLp ⬝ᵥ T *ᵥ ξ.ofLp : ℝ) : ℂ) / 2) *
        Complex.exp ((inner ℝ x ξ : ℝ) * Complex.I) := by
    intro x
    set h := hh x with hh_def
    set b := bb x with hb_def
    set rξ := R *ᵥ ξ.ofLp with hrξ
    have hsx : R *ᵥ h + b = x.ofLp := hsplit x
    -- real identities
    have e1 : ∀ z : EuclideanSpace ℝ ι, inner ℝ (tiltX m T bb (x, z)) ξ =
        m.ofLp ⬝ᵥ ξ.ofLp + rξ ⬝ᵥ z.ofLp + b ⬝ᵥ ξ.ofLp := by
      intro z
      rw [inner_eq_sum]
      have h1 : ∀ i, (tiltX m T bb (x, z)) i = m i + (R *ᵥ z.ofLp) i + b i := fun i => rfl
      simp only [h1, add_mul, Finset.sum_add_distrib]
      have h2 : ∑ i, (R *ᵥ z.ofLp) i * ξ i = rξ ⬝ᵥ z.ofLp := by
        rw [hrξ, dot_sym R hRs, dotProduct_comm]
        rfl
      rw [h2]
      rfl
    have e2 : rξ ⬝ᵥ rξ = ξ.ofLp ⬝ᵥ T *ᵥ ξ.ofLp := by
      rw [hrξ, dot_sym R hRs, Matrix.mulVec_mulVec, hRR]
    have e3 : h ⬝ᵥ rξ + b ⬝ᵥ ξ.ofLp = inner ℝ x ξ := by
      rw [inner_eq_sum, hrξ, ← dot_sym R hRs, ← add_dotProduct, hsx]
      rfl
    have e4 : inner ℝ ξ m = m.ofLp ⬝ᵥ ξ.ofLp := by
      rw [inner_eq_sum, dotProduct_comm]
      rfl
    have hpt : ∀ z : EuclideanSpace ℝ ι, ((cmw hh (x, z) : ℝ) : ℂ) *
          Complex.exp ((inner ℝ (tiltX m T bb (x, z)) ξ : ℝ) * Complex.I) =
        Complex.exp (-(((h ⬝ᵥ h : ℝ) : ℂ)) / 2 +
          Complex.I * (((m.ofLp ⬝ᵥ ξ.ofLp : ℝ) : ℂ) + ((b ⬝ᵥ ξ.ofLp : ℝ) : ℂ))) *
        Complex.exp (∑ i, ((h i : ℂ) + Complex.I * (rξ i : ℂ)) * (z i : ℂ)) := by
      intro z
      have h1 : ∑ i, ((h i : ℂ) + Complex.I * (rξ i : ℂ)) * (z i : ℂ) =
          ((h ⬝ᵥ z.ofLp : ℝ) : ℂ) + Complex.I * ((rξ ⬝ᵥ z.ofLp : ℝ) : ℂ) := by
        simp only [dotProduct, add_mul, Finset.sum_add_distrib, Complex.ofReal_sum,
          Complex.ofReal_mul, Finset.mul_sum, mul_assoc]
      have h2 : cmw hh (x, z) = Real.exp (h ⬝ᵥ z.ofLp - (h ⬝ᵥ h) / 2) := by
        unfold cmw
        simp only [dotProduct, sq]
        rfl
      rw [h1, h2, e1 z, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, gauss_cexp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have h3 : ∑ i, ((h i : ℂ) + Complex.I * (rξ i : ℂ)) ^ 2 / 2 =
        ((h ⬝ᵥ h : ℝ) : ℂ) / 2 - ((rξ ⬝ᵥ rξ : ℝ) : ℂ) / 2 +
          Complex.I * ((h ⬝ᵥ rξ : ℝ) : ℂ) := by
      simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_div,
        Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination ((rξ i : ℂ) ^ 2 / 2) * hI
    rw [h3, e4, ← e3, e2]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hin), integral_const_mul, ← charFun_apply,
    charFun_multivariateGaussian hΔ, ← Complex.exp_add]
  congr 1
  rw [inner_zero_right, Matrix.add_mulVec, dotProduct_add]
  push_cast
  ring

open scoped MatrixOrder in
/-- Change of variables for integrals against `N(m, T + Δ)`. -/
private theorem tilt_change {ι : Type} [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (T Δ : Matrix ι ι ℝ) (hT : T.PosSemidef) (hΔ : Δ.PosSemidef)
    (hh bb : EuclideanSpace ℝ ι → ι → ℝ) (hhm : Measurable hh) (hbm : Measurable bb)
    (hsplit : ∀ x, (CFC.sqrt T) *ᵥ (hh x) + bb x = x.ofLp)
    (g : EuclideanSpace ℝ ι → ℂ) (hg : Measurable g) :
    ∫ y, g y ∂(multivariateGaussian m (T + Δ)) =
      ∫ ω, ((cmw hh ω : ℝ) : ℂ) * g (tiltX m T bb ω)
        ∂((multivariateGaussian 0 Δ).prod (stdGaussian (EuclideanSpace ℝ ι))) := by
  rw [← tilt_measure m T Δ hT hΔ hh bb hhm hbm hsplit,
    integral_tilt_map _ (cmw hh) (cmw_measurable hh hhm) (fun ω => (cmw_pos hh ω).le) _
      (tiltX_measurable m T bb hbm) g hg]


end

end PartC

section PartT

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### The thermal state -/

/-- The Fock weights `p_w = (1 - r)ⁿ r^{|w|}` of the thermal state. -/
private def pw (n : ℕ) (r : ℝ) (w : Fin n → ℕ) : ℝ := (1 - r) ^ n * r ^ (∑ i, w i)

private lemma pw_pos (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (w : Fin n → ℕ) : 0 < pw n r w := by
  unfold pw
  have : 0 < 1 - r := by linarith
  positivity

/-- Homogeneity: `Γ(cR)` is `c^m Γ(R)` on the `m`-photon sector. -/
private lemma gammaFock_smul {n : ℕ} (c : ℂ) (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (c • R) u v = c ^ (∑ i, u i) * gammaFock R u v := by
  have hterm : ∀ M ∈ (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n =>
        Finset.range (u i + 1)).filter (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j),
      ∏ i, ∏ j, (c • R) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) =
        c ^ (∑ i, u i) * ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) := by
    intro M hM
    rw [Finset.mem_filter] at hM
    have hrow := hM.2.1
    have h1 : ∀ i j, (c • R) i j ^ M i j / (Nat.factorial (M i j) : ℂ) =
        c ^ M i j * (R i j ^ M i j / (Nat.factorial (M i j) : ℂ)) := by
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul, mul_pow, mul_div_assoc]
    simp only [h1, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_pow_eq_pow_sum, hrow i]
  unfold gammaFock
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_left_comm]

/-- The interleaved-to-grouped reindexing of quadratures used by `IsGaussianState`. -/
private def qe {n : ℕ} (a : Fin n × Fin 2) : Fin n ⊕ Fin n :=
  if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1

private lemma nu_alg (ν : ℝ) (hν : 0 < ν) :
    0 < ν / (1 + ν) ∧ ν / (1 + ν) < 1 ∧
      (1 + ν / (1 + ν)) / (1 - ν / (1 + ν)) = 1 + 2 * ν := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  refine ⟨by positivity, by rw [div_lt_one h1]; linarith, ?_⟩
  have h2 : 1 - ν / (1 + ν) = 1 / (1 + ν) := by field_simp; ring
  rw [h2]
  field_simp
  ring

open scoped ComplexOrder in
/-- The thermal state with fugacity `r`: diagonal with the weights `p_w`, Gaussian with covariance
`(1 + r)/(2(1 - r))·1`. -/
private lemma thermal_state_exists (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) :
    ∃ ρ : State (Occupation (Fin n)),
      ρ.coefficients = (fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0) ∧
      IsGaussianState ρ 0 (((1 + r) / (1 - r) / 2 : ℝ) •
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) := by
  have hr1 : (0 : ℝ) < 1 - r := by linarith
  have hRe : (1 : Matrix (Fin n) (Fin n) ℂ) - ((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      (((1 - r : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    push_cast
    rw [sub_smul, one_smul]
  have hR : (((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast h0.le)
  have hR1 : ((1 : Matrix (Fin n) (Fin n) ℂ) - ((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
    rw [hRe]
    exact Matrix.PosDef.one.smul (by exact_mod_cast hr1)
  obtain ⟨ρ, hρ, hG⟩ := fugacity_isGaussianState _ hR hR1
  refine ⟨ρ, ?_, ?_⟩
  · funext u v
    rw [hρ]
    show ((1 : Matrix (Fin n) (Fin n) ℂ) - ((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)).det *
      gammaFock (((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) u v = _
    rw [hRe, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, gammaFock_smul,
      (gammaFock_basic (1 : Matrix (Fin n) (Fin n) ℂ) u v).2.2]
    by_cases huv : u = v
    · simp only [huv, if_true, mul_one, pw]
      push_cast
      ring
    · simp [huv]
  · have hinv : ((1 : Matrix (Fin n) (Fin n) ℂ) - ((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
        ((((1 - r : ℝ)) : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [hRe, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀, one_smul]
      exact_mod_cast hr1.ne'
    have hprod : ((1 : Matrix (Fin n) (Fin n) ℂ) + ((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
        ((1 : Matrix (Fin n) (Fin n) ℂ) - ((r : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
        ((((1 + r) / (1 - r) : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hinv, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
      push_cast
      rw [← add_smul]
      congr 1
      field_simp
    rw [hprod] at hG
    convert hG using 1
    ext i j
    have hc : (1 + (r : ℂ)) / (1 - (r : ℂ)) = (((1 + r) / (1 - r) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hre : ((1 + (r : ℂ)) / (1 - (r : ℂ))).re = (1 + r) / (1 - r) := by
      rw [hc, Complex.ofReal_re]
    have him : ((1 + (r : ℂ)) / (1 - (r : ℂ))).im = 0 := by
      rw [hc, Complex.ofReal_im]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply] <;>
      by_cases hij : i = j <;> simp [hij, hre, him] <;> ring

/-- The data of the thermal operator `Θ` of covariance `(½ + ν)·1`. -/
private def IsThermal {n : ℕ} (ν : ℝ) (Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (l r : ℕ → Hilbert (Fin n → ℕ)) : Prop :=
  IsNuc Θ l r ∧ IsDensity (matOf Θ) ∧
  matOf Θ = (fun u v => if u = v then ((pw n (ν / (1 + ν)) u : ℝ) : ℂ) else 0) ∧
  ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic (matOf Θ) ξ =
    Complex.exp (((-varianceForm (fun a b => 2 * ((1 / 2 + ν : ℝ) •
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) (qe a) (qe b)) ξ / 4 : ℝ) : ℂ) +
      Complex.I * (meanForm (fun a => (0 : Fin n ⊕ Fin n → ℝ) (qe a)) ξ : ℂ))

private lemma thermal_op_exists (n : ℕ) (ν : ℝ) (hν : 0 < ν) :
    ∃ (Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) (l r : ℕ → Hilbert (Fin n → ℕ)),
      IsThermal ν Θ l r := by
  obtain ⟨h0, h1, h2⟩ := nu_alg ν hν
  obtain ⟨ρ, hρ, hG⟩ := thermal_state_exists n (ν / (1 + ν)) h0 h1
  have hcov : (1 + ν / (1 + ν)) / (1 - ν / (1 + ν)) / 2 = 1 / 2 + ν := by
    rw [h2]
    ring
  rw [hcov] at hG
  obtain ⟨Θ, l, r, hN, hm⟩ := exists_op ρ.coefficients ρ.density.1
  refine ⟨Θ, l, r, hN, hm ▸ ρ.density, hm.trans hρ, fun ξ => ?_⟩
  have h : GaussianAt ρ.coefficients (fun a => (0 : Fin n ⊕ Fin n → ℝ) (qe a))
      (fun a b => 2 * ((1 / 2 + ν : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        (qe a) (qe b)) := hG
  rw [hm]
  exact h.2 ξ

/-! ### The Gaussian mixture of displaced thermal states -/

/-- The mixture `∫ D(x) Θ D(x)⁻¹ dN(m, T)(x)` of displaced thermal states. -/
private def mixArr {n : ℕ} (Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ :=
  fun u v => ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2), matOf (cj Θ (fun a => ω a)) u v
    ∂(ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T)

private lemma mixArr_density {n : ℕ} {ν : ℝ} {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hΘ : IsThermal ν Θ l r) (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : IsDensity (mixArr Θ m T) :=
  (mix_explicit (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T)
    (fun ω a => ω a) (fun a => by fun_prop) hΘ.1 hΘ.2.1).1

private lemma mixArr_char {n : ℕ} {ν : ℝ} {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hΘ : IsThermal ν Θ l r) (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hT : T.PosSemidef) (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (mixArr Θ m T) ξ =
      Complex.exp (Complex.I * (meanForm m ξ : ℂ) - ((varianceForm T ξ / 2 : ℝ) : ℂ)) *
        oscillatorCharacteristic (matOf Θ) ξ := by
  have h := (mix_explicit (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T)
    (fun ω a => ω a) (fun a => by fun_prop) hΘ.1 hΘ.2.1).2 ξ
  refine h.trans ?_
  congr 1
  have hc := ProbabilityTheory.charFun_multivariateGaussian (μ := WithLp.toLp 2 m) hT
    (WithLp.toLp 2 ξ)
  rw [charFun_apply] at hc
  have h1 : ∀ x : EuclideanSpace ℝ (Fin n × Fin 2),
      inner ℝ x (WithLp.toLp 2 ξ) = meanForm (fun a => x a) ξ := by
    intro x
    simp [meanForm, PiLp.inner_apply]
  have h2 : inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin n × Fin 2)) (WithLp.toLp 2 m) =
      meanForm m ξ := by
    simp [meanForm, PiLp.inner_apply, mul_comm]
  have h3 : ξ ⬝ᵥ T *ᵥ ξ = varianceForm T ξ := by
    simp only [varianceForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  calc ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2),
        Complex.exp (Complex.I * (meanForm (fun a => ω a) ξ : ℂ))
          ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T
      = ∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
          Complex.exp ((inner ℝ x (WithLp.toLp 2 ξ) : ℂ) * Complex.I)
            ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [h1]
        rw [mul_comm]
    _ = Complex.exp (Complex.I * (meanForm m ξ : ℂ) - ((varianceForm T ξ / 2 : ℝ) : ℂ)) := by
        rw [hc, h2]
        simp only [h3]
        congr 1
        push_cast
        ring

/-- For `S ⪰ (½ + ν)·1` the mixture with `T = S - (½ + ν)·1` is the Gaussian state `ρ(μ, S)`. -/
private lemma mix_gaussian {n : ℕ} {ν : ℝ} {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hΘ : IsThermal ν Θ l r) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 + ν : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef) :
    IsGaussianState ⟨mixArr Θ (fun a => μ (qe a))
      ((S - (1 / 2 + ν : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix qe qe),
      mixArr_density hΘ _ _⟩ μ S := by
  have hsym : ∀ i j, S j i = S i j := by
    intro i j
    have h := hS.1.apply i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, star_trivial] at h
    have h1 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) j i =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) i j := by
      simp [Matrix.one_apply, eq_comm]
    rw [h1] at h
    linarith
  show GaussianAt _ (fun a => μ (qe a)) (fun a b => 2 * S (qe a) (qe b))
  refine gaussianAt_of_characteristic _ _ _ ?_ fun ξ => ?_
  · funext a b
    show 2 * S (qe b) (qe a) = 2 * S (qe a) (qe b)
    rw [hsym]
  · show oscillatorCharacteristic (mixArr _ _ _) ξ = _
    rw [mixArr_char hΘ _ _ (hS.submatrix qe) ξ, hΘ.2.2.2 ξ, ← Complex.exp_add]
    congr 1
    have hv : varianceForm (fun a b => 2 * S (qe a) (qe b)) ξ =
        2 * varianceForm ((S - (1 / 2 + ν : ℝ) •
          (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix qe qe) ξ +
        varianceForm (fun a b => 2 * ((1 / 2 + ν : ℝ) •
          (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) (qe a) (qe b)) ξ := by
      simp only [varianceForm, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hm0 : meanForm (fun a => (0 : Fin n ⊕ Fin n → ℝ) (qe a)) ξ = 0 := by
      simp [meanForm]
    rw [hv, hm0]
    push_cast
    ring

/-! ### Reindexing -/

/-- `qe` as an equivalence. -/
private def qeE (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun := qe
  invFun := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  left_inv := by
    rintro ⟨j, k⟩
    fin_cases k <;> simp [qe]
  right_inv := by
    rintro (j | j) <;> simp [qe]

private lemma qeE_apply {n : ℕ} (a : Fin n × Fin 2) : qeE n a = qe a := rfl

private lemma qe_inj {n : ℕ} (a b : Fin n × Fin 2) : qe a = qe b ↔ a = b :=
  (qeE n).injective.eq_iff

/-- A Gaussian state with covariance `S ⪰ (½ + ν)·1` is the Gaussian mixture of displaced thermal
states. -/
private lemma coeff_eq_mixArr {n : ℕ} {ν : ℝ} {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hΘ : IsThermal ν Θ l r)
    (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 + ν : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (h : IsGaussianState ρ μ S) :
    ρ.coefficients = mixArr Θ (fun a => μ (qe a))
      ((S - (1 / 2 + ν : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix qe qe) := by
  have h2 := mix_gaussian hΘ μ S hS
  exact state_ext_characteristic ρ ⟨_, mixArr_density hΘ _ _⟩ fun ξ => (h.2 ξ).trans (h2.2 ξ).symm

private lemma trace_reindex {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (M.submatrix (qe (n := n)) qe).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp (qeE n) fun k => M k k

private lemma inv_reindex {n : ℕ} (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (S.submatrix (qe (n := n)) qe)⁻¹ = S⁻¹.submatrix (qe (n := n)) qe := by
  have h1 := Matrix.inv_submatrix_equiv S (qeE n) (qeE n)
  have h3 : (⇑(qeE n) : Fin n × Fin 2 → Fin n ⊕ Fin n) = qe := rfl
  rw [h3] at h1
  exact h1

private lemma mul_reindex {n : ℕ} (A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    A.submatrix (qe (n := n)) qe * B.submatrix (qe (n := n)) qe =
      (A * B).submatrix (qe (n := n)) qe := by
  have h2 := Matrix.submatrix_mul_equiv A B (qeE n) (qeE n) (qeE n)
  have h3 : (⇑(qeE n) : Fin n × Fin 2 → Fin n ⊕ Fin n) = qe := rfl
  rw [h3] at h2
  exact h2

end

end PartT

section PartH

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### Displaced thermal operators -/

private lemma zOf_add {n : ℕ} (a b : Fin n × Fin 2 → ℝ) : zOf (a + b) = zOf a + zOf b := by
  funext j
  simp only [zOf, Pi.add_apply]
  push_cast
  ring

private lemma zOf_zero {n : ℕ} : zOf (0 : Fin n × Fin 2 → ℝ) = 0 := by
  funext j
  simp [zOf]

/-- A diagonal operator acts by multiplication. -/
private lemma diag_apply {n : ℕ} {r : ℝ} {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (y : Hilbert (Fin n → ℕ)) (u : Fin n → ℕ) : (Θ y) u = y u * ((pw n r u : ℝ) : ℂ) := by
  have h := clm_apply_hasSum Θ y u
  have he : ∀ w, (Θ (bv w)) u = if u = w then ((pw n r u : ℝ) : ℂ) else 0 := fun w =>
    congrFun (congrFun hdiag u) w
  have h2 : HasSum (fun w => y w * (Θ (bv w)) u) (y u * (Θ (bv u)) u) := by
    refine hasSum_single u fun w hw => ?_
    rw [he, if_neg (Ne.symm hw), mul_zero]
  rw [h.unique h2, he, if_pos rfl]

/-- The entries `(τ_z)_{uv} = ∑_w D(z)_{uw} p_w conj(D(z)_{vw})` of the displaced thermal state. -/
private def TT (n : ℕ) (r : ℝ) (z : Fin n → ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑' w : Fin n → ℕ, (∏ j, displacementMatrix (z j) (u j) (w j)) * ((pw n r w : ℝ) : ℂ) *
    star (∏ j, displacementMatrix (z j) (v j) (w j))

private lemma cj_diag_entry {n : ℕ} {r : ℝ} {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (b : Fin n × Fin 2 → ℝ) (u v : Fin n → ℕ) :
    matOf (cj Θ b) u v = TT n r (zOf b) u v := by
  have h1 : matOf (cj Θ b) u v = (Dop (zOf b) (Θ (Dop (-zOf b) (bv v)))) u := rfl
  have h2 := Dop_apply (zOf b) (Θ (Dop (-zOf b) (bv v))) u
  rw [h1, ← h2.tsum_eq]
  unfold TT
  refine tsum_congr fun w => ?_
  rw [diag_apply hdiag, Dop_bv, colV_apply, Kd_neg]
  unfold Kd
  ring

/-! ### The Hilbert space of weighted arrays -/

/-- `κ = (1 - r)/√r`. -/
private def kap (r : ℝ) : ℝ := (1 - r) / Real.sqrt r

/-- The array `τ^{-1/4} τ_b τ^{-1/4}`. -/
private def vvF (n : ℕ) (r : ℝ) (b : Fin n × Fin 2 → ℝ) (x : (Fin n → ℕ) × (Fin n → ℕ)) : ℂ :=
  TT n r (zOf b) x.1 x.2 / ((Real.sqrt (Real.sqrt (pw n r x.1 * pw n r x.2)) : ℝ) : ℂ)

private lemma sqrt_sqrt_sq (x : ℝ) : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
  Real.mul_self_sqrt (Real.sqrt_nonneg x)

private lemma vvF_mem (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b : Fin n × Fin 2 → ℝ) :
    Memℓp (vvF n r b) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h := (thermal_displaced_kernel r h0 h1 (zOf b) (zOf b) (pw n r) rfl (TT n r) rfl).2.1
  refine h.congr fun x => ?_
  unfold vvF
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [div_pow, sq (Real.sqrt _), sqrt_sqrt_sq, sq]

/-- `v_b = τ^{-1/4} τ_b τ^{-1/4}` as a vector of `ℓ²`. -/
private def vv (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b : Fin n × Fin 2 → ℝ) :
    Hilbert ((Fin n → ℕ) × (Fin n → ℕ)) :=
  ⟨vvF n r b, vvF_mem n r h0 h1 b⟩

private lemma vv_apply (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b : Fin n × Fin 2 → ℝ)
    (x : (Fin n → ℕ) × (Fin n → ℕ)) : vv n r h0 h1 b x = vvF n r b x := rfl

private lemma zOf_pair {n : ℕ} (b b' : Fin n × Fin 2 → ℝ) :
    ∑ j, (star (zOf b j) * zOf b' j + zOf b j * star (zOf b' j)) = ((∑ a, b a * b' a : ℝ) : ℂ) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  simp only [zOf, Complex.star_def, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [div_mul_div_comm, div_mul_div_comm, hs]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(b (j, 1) : ℂ) * (b' (j, 1) : ℂ)) * hI

/-- The reproducing kernel of the displaced thermal states. -/
private lemma vv_inner (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b b' : Fin n × Fin 2 → ℝ) :
    inner ℂ (vv n r h0 h1 b) (vv n r h0 h1 b') =
      ((Real.exp (kap r * ∑ a, b a * b' a) : ℝ) : ℂ) := by
  have h := (thermal_displaced_kernel r h0 h1 (zOf b') (zOf b) (pw n r) rfl (TT n r) rfl).2.2
  have h2 := lp.hasSum_inner (𝕜 := ℂ) (vv n r h0 h1 b) (vv n r h0 h1 b')
  have h3 : (fun x : (Fin n → ℕ) × (Fin n → ℕ) => inner ℂ (vv n r h0 h1 b x) (vv n r h0 h1 b' x)) =
      fun x => TT n r (zOf b') x.1 x.2 * star (TT n r (zOf b) x.1 x.2) /
        ((Real.sqrt (pw n r x.1 * pw n r x.2) : ℝ) : ℂ) := by
    funext x
    rw [RCLike.inner_apply, vv_apply, vv_apply]
    unfold vvF
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul, sqrt_sqrt_sq]
    rfl
  rw [h3] at h2
  have h4 := HasSum.unique h2 h
  rw [h4, zOf_pair b' b, Complex.ofReal_exp]
  congr 1
  push_cast
  unfold kap
  congr 1
  · push_cast
    rfl
  · exact Finset.sum_congr rfl fun a _ => mul_comm _ _

private lemma vv_norm_sq (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b : Fin n × Fin 2 → ℝ) :
    ‖vv n r h0 h1 b‖ ^ 2 = Real.exp (kap r * ∑ a, b a * b a) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), vv_inner]
  exact Complex.ofReal_re _

private lemma vv_norm_sub_sq (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b' b : Fin n × Fin 2 → ℝ) :
    ‖vv n r h0 h1 b' - vv n r h0 h1 b‖ ^ 2 =
      Real.exp (kap r * ∑ a, b' a * b' a) + Real.exp (kap r * ∑ a, b a * b a) -
        2 * Real.exp (kap r * ∑ a, b' a * b a) := by
  rw [norm_sub_sq (𝕜 := ℂ), vv_norm_sq, vv_norm_sq, vv_inner]
  have h : RCLike.re ((Real.exp (kap r * ∑ a, b' a * b a) : ℝ) : ℂ) =
      Real.exp (kap r * ∑ a, b' a * b a) := Complex.ofReal_re _
  rw [h]
  ring

/-- `b ↦ v_b` is continuous. -/
private lemma vv_continuous (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) : Continuous (vv n r h0 h1) := by
  rw [continuous_iff_continuousAt]
  intro b
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hφ : Continuous (fun b' : Fin n × Fin 2 → ℝ =>
      Real.sqrt (Real.exp (kap r * ∑ a, b' a * b' a) + Real.exp (kap r * ∑ a, b a * b a) -
        2 * Real.exp (kap r * ∑ a, b' a * b a))) := by fun_prop
  have ht := hφ.tendsto b
  have hval : Real.sqrt (Real.exp (kap r * ∑ a, b a * b a) + Real.exp (kap r * ∑ a, b a * b a) -
      2 * Real.exp (kap r * ∑ a, b a * b a)) = 0 := by
    rw [show Real.exp (kap r * ∑ a, b a * b a) + Real.exp (kap r * ∑ a, b a * b a) -
      2 * Real.exp (kap r * ∑ a, b a * b a) = 0 by ring, Real.sqrt_zero]
  rw [hval] at ht
  refine ht.congr fun b' => ?_
  rw [← vv_norm_sub_sq n r h0 h1 b' b, Real.sqrt_sq (norm_nonneg _)]

/-! ### Contractions as vectors of the weighted `ℓ²` -/

private lemma matOf_col_sq {I : Type} (G : Hilbert I →L[ℂ] Hilbert I) (m : I) (s : Finset I) :
    ∑ k ∈ s, ‖matOf G k m‖ ^ 2 ≤ ‖G‖ ^ 2 := by
  have h := lp_sum_sq_le (G (bv m)) s
  have h2 : ‖G (bv m)‖ ≤ ‖G‖ := by
    have := G.le_opNorm (bv m)
    rwa [norm_bv, mul_one] at this
  exact h.trans (pow_le_pow_left₀ (norm_nonneg _) h2 2)

private lemma matOf_row_sq {I : Type} (G : Hilbert I →L[ℂ] Hilbert I) (k : I) (s : Finset I) :
    ∑ m ∈ s, ‖matOf G k m‖ ^ 2 ≤ ‖G‖ ^ 2 := by
  have h := lp_sum_sq_le (ContinuousLinearMap.adjoint G (bv k)) s
  have h2 : ‖ContinuousLinearMap.adjoint G (bv k)‖ ≤ ‖G‖ := by
    have := (ContinuousLinearMap.adjoint G).le_opNorm (bv k)
    rwa [norm_bv, mul_one, LinearIsometryEquiv.norm_map] at this
  refine le_trans (le_of_eq ?_) (h.trans (pow_le_pow_left₀ (norm_nonneg _) h2 2))
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [matOf_eq_adjoint, norm_star]

private lemma pw_sum_le {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (hden : IsDensity (matOf Θ)) (s : Finset (Fin n → ℕ)) : ∑ w ∈ s, pw n r w ≤ 1 := by
  have he : (fun i => (matOf Θ i i).re) = pw n r := by
    funext i
    rw [hdiag]
    simp
  have h := hden.2.2
  rw [he] at h
  rw [← h.2]
  exact h.1.sum_le_tsum s fun w _ => (pw_pos n r h0 h1 w).le

/-- The array `τ^{1/4} G† τ^{1/4}` (conjugated). -/
private def gwF (n : ℕ) (r : ℝ) (G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (x : (Fin n → ℕ) × (Fin n → ℕ)) : ℂ :=
  ((Real.sqrt (Real.sqrt (pw n r x.1 * pw n r x.2)) : ℝ) : ℂ) * star (matOf G x.2 x.1)

private lemma sqrt_mul_le_half (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_nonneg (a - b)]

private lemma gwF_sum_le {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    (hsum : ∀ s : Finset (Fin n → ℕ), ∑ w ∈ s, pw n r w ≤ 1)
    (G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (s : Finset ((Fin n → ℕ) × (Fin n → ℕ))) : ∑ x ∈ s, ‖gwF n r G x‖ ^ 2 ≤ ‖G‖ ^ 2 := by
  have hp : ∀ w, 0 ≤ pw n r w := fun w => (pw_pos n r h0 h1 w).le
  set s₁ := s.image Prod.fst with hs₁
  set s₂ := s.image Prod.snd with hs₂
  have hsub : s ⊆ s₁ ×ˢ s₂ := by
    intro x hx
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
  have hterm : ∀ x : (Fin n → ℕ) × (Fin n → ℕ), ‖gwF n r G x‖ ^ 2 ≤
      (pw n r x.1 + pw n r x.2) / 2 * ‖matOf G x.2 x.1‖ ^ 2 := by
    intro x
    unfold gwF
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, sq (Real.sqrt _), sqrt_sqrt_sq]
    exact mul_le_mul_of_nonneg_right (sqrt_mul_le_half _ _ (hp _) (hp _)) (sq_nonneg _)
  calc ∑ x ∈ s, ‖gwF n r G x‖ ^ 2
      ≤ ∑ x ∈ s, (pw n r x.1 + pw n r x.2) / 2 * ‖matOf G x.2 x.1‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => hterm x
    _ ≤ ∑ x ∈ s₁ ×ˢ s₂, (pw n r x.1 + pw n r x.2) / 2 * ‖matOf G x.2 x.1‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          mul_nonneg (div_nonneg (add_nonneg (hp _) (hp _)) (by norm_num)) (sq_nonneg _)
    _ = (1 / 2) * ∑ m ∈ s₁, pw n r m * ∑ k ∈ s₂, ‖matOf G k m‖ ^ 2 +
          (1 / 2) * ∑ k ∈ s₂, pw n r k * ∑ m ∈ s₁, ‖matOf G k m‖ ^ 2 := by
        have e2 : ∑ k ∈ s₂, pw n r k * ∑ m ∈ s₁, ‖matOf G k m‖ ^ 2 =
            ∑ m ∈ s₁, ∑ k ∈ s₂, pw n r k * ‖matOf G k m‖ ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
        rw [Finset.sum_product, e2]
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ (1 / 2) * ∑ m ∈ s₁, pw n r m * ‖G‖ ^ 2 + (1 / 2) * ∑ k ∈ s₂, pw n r k * ‖G‖ ^ 2 := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by norm_num)
          exact mul_le_mul_of_nonneg_left (matOf_col_sq G m s₂) (hp m)
        · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
          exact mul_le_mul_of_nonneg_left (matOf_row_sq G k s₁) (hp k)
    _ ≤ (1 / 2) * (1 * ‖G‖ ^ 2) + (1 / 2) * (1 * ‖G‖ ^ 2) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hsum s₁) (sq_nonneg _)) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hsum s₂) (sq_nonneg _)) (by norm_num)
    _ = ‖G‖ ^ 2 := by ring

/-- A bounded operator `G` gives a vector of the weighted `ℓ²` of norm at most `‖G‖`. -/
private lemma gw_exists {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    (hsum : ∀ s : Finset (Fin n → ℕ), ∑ w ∈ s, pw n r w ≤ 1)
    (G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) :
    ∃ g : Hilbert ((Fin n → ℕ) × (Fin n → ℕ)), (∀ x, g x = gwF n r G x) ∧ ‖g‖ ≤ ‖G‖ := by
  have hb : ∀ s : Finset ((Fin n → ℕ) × (Fin n → ℕ)),
      ∑ x ∈ s, ‖gwF n r G x‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖G‖ ^ (2 : ℝ≥0∞).toReal := by
    intro s
    simpa using gwF_sum_le h0 h1 hsum G s
  refine ⟨⟨gwF n r G, memℓp_gen' hb⟩, fun x => rfl, ?_⟩
  exact lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _) hb

/-- The trace pairing `Tr(D_b Θ D_b⁻¹ G)` as an inner product in the weighted `ℓ²`. -/
private lemma pair_hasSum {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (g : Hilbert ((Fin n → ℕ) × (Fin n → ℕ))) (hg : ∀ x, g x = gwF n r G x)
    (b : Fin n × Fin 2 → ℝ) :
    HasSum (fun m => (cj Θ b (G (bv m))) m) (inner ℂ g (vv n r h0 h1 b)) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) g (vv n r h0 h1 b)
  refine h.prod_fiberwise fun m => ?_
  have h2 := clm_apply_hasSum (cj Θ b) (G (bv m)) m
  refine h2.congr_fun fun k => ?_
  have hpos : ((Real.sqrt (Real.sqrt (pw n r m * pw n r k)) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (Real.sqrt (pw n r m * pw n r k)) :=
      Real.sqrt_pos.2 (Real.sqrt_pos.2 (mul_pos (pw_pos n r h0 h1 m) (pw_pos n r h0 h1 k)))
    exact_mod_cast this.ne'
  rw [RCLike.inner_apply, hg, vv_apply]
  unfold gwF vvF
  rw [map_mul, Complex.conj_ofReal, ← cj_diag_entry hdiag]
  simp only [Complex.star_def, Complex.conj_conj]
  show _ = (G (bv m)) k * (cj Θ b (bv k)) m
  have e1 : matOf G k m = (G (bv m)) k := rfl
  have e2 : matOf (cj Θ b) m k = (cj Θ b (bv k)) m := rfl
  rw [e1, e2]
  field_simp

/-! ### Finite coordinate projections and cyclicity of the trace -/

/-- The coordinate projection onto the span of `e_u`, `u ∈ F`. -/
private def PF {I : Type} (F : Finset I) : Hilbert I →L[ℂ] Hilbert I :=
  ∑ u ∈ F, (innerSL ℂ (bv u)).smulRight (bv u)

private lemma PF_apply {I : Type} (F : Finset I) (x : Hilbert I) : PF F x = ∑ u ∈ F, x u • (bv u : Hilbert I) := by
  unfold PF
  rw [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_bv_left]

open Classical in
private lemma PF_coord {I : Type} (F : Finset I) (x : Hilbert I) (w : I) :
    (PF F x) w = if w ∈ F then x w else 0 := by
  rw [PF_apply]
  have h : ((∑ u ∈ F, x u • (bv u : Hilbert I) : Hilbert I) : I → ℂ) w =
      ∑ u ∈ F, x u * (bv u : Hilbert I) w := by
    rw [lp.coeFn_sum, Finset.sum_apply]
    rfl
  rw [h]
  by_cases hw : w ∈ F
  · rw [if_pos hw, Finset.sum_eq_single w]
    · rw [bv_apply_self, mul_one]
    · intro u _ hu
      rw [bv_apply_ne (Ne.symm hu), mul_zero]
    · intro h'
      exact absurd hw h'
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun u hu => ?_
    have : w ≠ u := fun h' => hw (h' ▸ hu)
    rw [bv_apply_ne this, mul_zero]

private lemma PF_norm_le {I : Type} (F : Finset I) : ‖PF F‖ ≤ 1 := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  refine lp.norm_mono (by norm_num) fun w => ?_
  rw [PF_coord]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

/-- Cyclicity: `Tr(P_F D X D⁻¹ V) = Tr(X D⁻¹ V P_F D)`. -/
private lemma cyc_hasSum {I : Type} (X V : Hilbert I →L[ℂ] Hilbert I) (D : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    (F : Finset I) :
    HasSum (fun m => (X ((D.symm : Hilbert I →L[ℂ] Hilbert I) (V (PF F ((D : Hilbert I →L[ℂ] Hilbert I)
        (bv m))))) ) m)
      (∑ u ∈ F, (D (X (D.symm (V (bv u))))) u) := by
  have h1 : ∀ m, (X ((D.symm : Hilbert I →L[ℂ] Hilbert I) (V (PF F ((D : Hilbert I →L[ℂ] Hilbert I)
      (bv m)))))) m = ∑ u ∈ F, (X (D.symm (V (bv u)))) m * (D (bv m)) u := by
    intro m
    rw [PF_apply]
    simp only [map_sum, map_smul, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe]
    have h : ((∑ u ∈ F, (D (bv m)) u • X (D.symm (V (bv u))) : Hilbert I) : I → ℂ) m =
        ∑ u ∈ F, (D (bv m)) u * (X (D.symm (V (bv u)))) m := by
      rw [lp.coeFn_sum, Finset.sum_apply]
      rfl
    rw [h]
    exact Finset.sum_congr rfl fun u _ => mul_comm _ _
  rw [funext h1]
  refine hasSum_sum fun u _ => ?_
  exact clm_apply_hasSum (D : Hilbert I →L[ℂ] Hilbert I) (X (D.symm (V (bv u)))) u

private lemma ph_neg_neg {n : ℕ} (c b : Fin n → ℂ) : ph c b * ph (-b) (-c) = 1 := by
  unfold ph
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add]
  convert Complex.exp_zero
  simp only [Pi.neg_apply, star_neg]
  ring

/-- `D_{c+b} A D_{c+b}⁻¹ = D_c (D_b A D_b⁻¹) D_c⁻¹`. -/
private lemma cj_add {n : ℕ} (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (c b : Fin n × Fin 2 → ℝ) (x : Hilbert (Fin n → ℕ)) :
    cj A (c + b) x = Deq (zOf c) (cj A b ((Deq (zOf c)).symm x)) := by
  have hL : cj A (c + b) x = Dop (zOf c + zOf b) (A (Dop (-(zOf c + zOf b)) x)) := by
    rw [← zOf_add]
    rfl
  have hR : Deq (zOf c) (cj A b ((Deq (zOf c)).symm x)) =
      Dop (zOf c) (Dop (zOf b) (A (Dop (-zOf b) (Dop (-zOf c) x)))) := rfl
  rw [hL, hR, Dop_mul (-zOf b) (-zOf c)]
  simp only [map_smul]
  rw [Dop_mul (zOf c) (zOf b), smul_smul, mul_comm, ph_neg_neg, one_smul, neg_add_rev]

/-- The partial trace pairing of a displaced thermal operator with a contraction is an inner
product with a vector of norm at most one in the weighted `ℓ²`. -/
private theorem pairing_repr {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (hden : IsDensity (matOf Θ))
    (V : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) (hV : ‖V‖ ≤ 1)
    (F : Finset (Fin n → ℕ)) (c : Fin n × Fin 2 → ℝ) :
    ∃ g : Hilbert ((Fin n → ℕ) × (Fin n → ℕ)), ‖g‖ ≤ 1 ∧ ∀ b : Fin n × Fin 2 → ℝ,
      ∑ u ∈ F, (cj Θ (c + b) (V (bv u))) u = inner ℂ g (vv n r h0 h1 b) := by
  set D := Deq (zOf c) with hD
  set G : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ) :=
    (D.symm : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) ∘L V ∘L PF F ∘L
      (D : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) with hG
  have hGn : ‖G‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    show ‖D.symm (V (PF F (D x)))‖ ≤ ‖x‖
    rw [LinearIsometryEquiv.norm_map]
    calc ‖V (PF F (D x))‖ ≤ ‖V‖ * ‖PF F (D x)‖ := V.le_opNorm _
      _ ≤ 1 * ‖PF F (D x)‖ := mul_le_mul_of_nonneg_right hV (norm_nonneg _)
      _ = ‖PF F (D x)‖ := one_mul _
      _ ≤ ‖PF F‖ * ‖D x‖ := (PF F).le_opNorm _
      _ ≤ 1 * ‖D x‖ := mul_le_mul_of_nonneg_right (PF_norm_le F) (norm_nonneg _)
      _ = ‖x‖ := by rw [one_mul, LinearIsometryEquiv.norm_map]
  obtain ⟨g, hg, hgn⟩ := gw_exists h0 h1 (pw_sum_le h0 h1 hdiag hden) G
  refine ⟨g, hgn.trans hGn, fun b => ?_⟩
  have hp := pair_hasSum h0 h1 hdiag G g hg b
  have hc := cyc_hasSum (cj Θ b) V D F
  have he : ∑ u ∈ F, (cj Θ (c + b) (V (bv u))) u =
      ∑ u ∈ F, (D (cj Θ b (D.symm (V (bv u))))) u :=
    Finset.sum_congr rfl fun u _ => by rw [cj_add]
  rw [he]
  exact hc.unique hp

end

end PartH

section PartK1

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### Exchange of a dominated series with an integral -/

private lemma fubini_dom {Ω : Type} [MeasurableSpace Ω] (γ : Measure Ω)
    {ι : Type} [Countable ι] (F : ι → Ω → ℂ) (g : Ω → ℝ) (hg : Integrable g γ)
    (hm : ∀ i, Measurable (F i)) (hb : ∀ x (s : Finset ι), ∑ i ∈ s, ‖F i x‖ ≤ g x) :
    (∀ x, Summable (fun i => F i x)) ∧
      Integrable (fun x => ∑' i, F i x) γ ∧
      HasSum (fun i => ∫ x, F i x ∂γ) (∫ x, ∑' i, F i x ∂γ) := by
  have hsum : ∀ x, Summable (fun i => ‖F i x‖) := fun x =>
    summable_of_sum_le (fun _ => norm_nonneg _) (hb x)
  have hsum' : ∀ x, Summable (fun i => F i x) := fun x => (hsum x).of_norm
  have hle : ∀ i x, ‖F i x‖ ≤ g x := fun i x => by simpa using hb x {i}
  have hint : ∀ i, Integrable (F i) γ := fun i =>
    Integrable.mono' hg (hm i).aestronglyMeasurable (Filter.Eventually.of_forall (hle i))
  have hmeas : Measurable (fun x => ∑' i, F i x) := by
    refine measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset ι) x => ∑ i ∈ s, F i x)
      (fun s => Finset.measurable_sum s fun i _ => hm i) ?_
    exact tendsto_pi_nhds.mpr fun x => (hsum' x).hasSum
  refine ⟨hsum', ?_, ?_⟩
  · refine Integrable.mono' hg hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    exact (norm_tsum_le_tsum_norm (hsum x)).trans ((hsum x).tsum_le_of_sum_le (hb x))
  · refine hasSum_integral_of_summable_integral_norm hint ?_
    refine summable_of_sum_le (c := ∫ x, g x ∂γ) (fun i => integral_nonneg fun _ => norm_nonneg _)
      fun s => ?_
    rw [← integral_finsetSum s fun i _ => (hint i).norm]
    exact integral_mono (integrable_finsetSum s fun i _ => (hint i).norm) hg fun x => hb x s

/-- If the matrix of `A` is a weighted mixture of the matrices of uniformly bounded operators,
then `A` acts coordinatewise as the mixture. -/
private lemma op_mix_apply {Ω I : Type} [MeasurableSpace Ω] [Countable I] (P : Measure Ω)
    (w : Ω → ℝ) (hwm : Measurable w) (hw0 : ∀ ω, 0 ≤ w ω) (hwi : Integrable w P)
    (B : Ω → (Hilbert I →L[ℂ] Hilbert I)) (C : ℝ) (hB : ∀ ω, ‖B ω‖ ≤ C)
    (hBm : ∀ u v, Measurable (fun ω => matOf (B ω) u v))
    (A : Hilbert I →L[ℂ] Hilbert I)
    (hA : ∀ u v, matOf A u v = ∫ ω, ((w ω : ℝ) : ℂ) * matOf (B ω) u v ∂P)
    (y : Hilbert I) (u : I) :
    Integrable (fun ω => ((w ω : ℝ) : ℂ) * (B ω y) u) P ∧
      (A y) u = ∫ ω, ((w ω : ℝ) : ℂ) * (B ω y) u ∂P := by
  have hrow : ∀ ω (s : Finset I),
      ∑ v ∈ s, ‖y v * (((w ω : ℝ) : ℂ) * matOf (B ω) u v)‖ ≤ w ω * (C * ‖y‖) := by
    intro ω s
    have h := matOf_row_bound (B ω) y u s
    calc ∑ v ∈ s, ‖y v * (((w ω : ℝ) : ℂ) * matOf (B ω) u v)‖
        = w ω * ∑ v ∈ s, ‖matOf (B ω) u v * y v‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hw0 ω)]
          ring
      _ ≤ w ω * (C * ‖y‖) :=
          mul_le_mul_of_nonneg_left
            (h.trans (mul_le_mul_of_nonneg_right (hB ω) (norm_nonneg _))) (hw0 ω)
  obtain ⟨-, hint, hsum⟩ := fubini_dom P
    (fun v ω => y v * (((w ω : ℝ) : ℂ) * matOf (B ω) u v)) (fun ω => w ω * (C * ‖y‖))
    (hwi.mul_const _)
    (fun v => measurable_const.mul ((Complex.measurable_ofReal.comp hwm).mul (hBm u v))) hrow
  have hpt : ∀ ω, ∑' v, y v * (((w ω : ℝ) : ℂ) * matOf (B ω) u v) =
      ((w ω : ℝ) : ℂ) * (B ω y) u := by
    intro ω
    have h := (clm_apply_hasSum (B ω) y u).mul_left ((w ω : ℝ) : ℂ)
    rw [← h.tsum_eq]
    refine tsum_congr fun v => ?_
    show _ = ((w ω : ℝ) : ℂ) * (y v * (B ω (bv v)) u)
    unfold matOf
    ring
  simp only [hpt] at hint hsum
  refine ⟨hint, ?_⟩
  refine (clm_apply_hasSum A y u).unique ?_
  refine hsum.congr_fun fun v => ?_
  rw [integral_const_mul, ← hA]
  rfl

/-- A positive operator is self-adjoint. -/
private lemma isSelfAdjoint_of_isPos {I : Type} {A : Hilbert I →L[ℂ] Hilbert I} (h : IsPos A) :
    IsSelfAdjoint A := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  refine (LinearMap.isSymmetric_iff_inner_map_self_real (A : Hilbert I →ₗ[ℂ] Hilbert I)).2 fun v => ?_
  have h1 := (h v).1
  have h2 : inner ℂ (A v) v = (starRingEnd ℂ) (inner ℂ v (A v)) := (inner_conj_symm _ _).symm
  show (starRingEnd ℂ) (inner ℂ (A v) v) = inner ℂ (A v) v
  rw [h2, Complex.conj_conj]
  exact (Complex.conj_eq_iff_im.2 h1).symm

private lemma sqrt_le_amgm (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s) : Real.sqrt x ≤ x / (2 * s) + s / 2 := by
  have h1 := Real.sq_sqrt hx
  have h2 : 0 ≤ (Real.sqrt x - s) ^ 2 := sq_nonneg _
  have h3 : x / (2 * s) + s / 2 = (x + s ^ 2) / (2 * s) := by
    field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  nlinarith

/-! ### Gaussian integrability of `exp(s‖g‖²)` -/

private lemma gaussReal_exp_sq (s : ℝ) (hs : s < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (s * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun x => by simp [gaussianPDF])]
  have h := (integrable_exp_neg_mul_sq (show 0 < 1 / 2 - s by linarith)).const_mul
    (Real.sqrt (2 * Real.pi * (1 : NNReal)))⁻¹
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show (Real.sqrt (2 * Real.pi * (1 : NNReal)))⁻¹ * Real.exp (-(1 / 2 - s) * x ^ 2) =
    Real.exp (s * x ^ 2) * (gaussianPDF 0 1 x).toReal
  rw [toReal_gaussianPDF, gaussianPDFReal, mul_left_comm (Real.exp (s * x ^ 2)), ← Real.exp_add]
  congr 2
  push_cast
  ring

private lemma gauss_exp_sq {ι : Type} [Fintype ι] (s : ℝ) (hs : s < 1 / 2) :
    Integrable (fun g : EuclideanSpace ℝ ι => Real.exp (s * ∑ i, g i ^ 2))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [← map_pi_eq_stdGaussian, integrable_map_measure (by fun_prop) (by fun_prop)]
  have h := Integrable.fintype_prod (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun (_ : ι) (x : ℝ) => Real.exp (s * x ^ 2)) (fun _ => gaussReal_exp_sq s hs)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show ∏ i, Real.exp (s * x i ^ 2) = Real.exp (s * ∑ i, x i ^ 2)
  rw [← Real.exp_sum, Finset.mul_sum]

/-! ### The `χ²` identity in the weighted `ℓ²` -/

/-- `‖∫ w(g) v_{b(g)} dμ(g) - v_0‖² = ∫∫ w w' exp(κ⟨b, b'⟩) - 2 ∫ w + 1`. -/
private lemma chi_sq_identity {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {n : ℕ} (r : ℝ)
    (h0 : 0 < r) (h1 : r < 1) (w : Ω → ℝ) (bbv : Ω → Fin n × Fin 2 → ℝ)
    (hint : Integrable (fun g => ((w g : ℝ) : ℂ) • vv n r h0 h1 (bbv g)) μ)
    (hk : Integrable (fun p : Ω × Ω =>
      w p.1 * w p.2 * Real.exp (kap r * ∑ a, bbv p.1 a * bbv p.2 a)) (μ.prod μ)) :
    ‖(∫ g, ((w g : ℝ) : ℂ) • vv n r h0 h1 (bbv g) ∂μ) - vv n r h0 h1 0‖ ^ 2 =
      (∫ p : Ω × Ω, w p.1 * w p.2 * Real.exp (kap r * ∑ a, bbv p.1 a * bbv p.2 a) ∂(μ.prod μ)) -
        2 * ∫ g, w g ∂μ + 1 := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ∫ g, ((w g : ℝ) : ℂ) • vv n r h0 h1 (bbv g) ∂μ := ⟨_, rfl⟩
  rw [← hY]
  have hv0 : ‖vv n r h0 h1 (0 : Fin n × Fin 2 → ℝ)‖ ^ 2 = 1 := by
    rw [vv_norm_sq]
    simp
  have hcY : ∀ b : Fin n × Fin 2 → ℝ, inner ℂ (vv n r h0 h1 b) Y =
      ((∫ g, w g * Real.exp (kap r * ∑ a, b a * bbv g a) ∂μ : ℝ) : ℂ) := by
    intro b
    rw [hY, ← integral_inner (𝕜 := ℂ) hint, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show inner ℂ (vv n r h0 h1 b) (((w g : ℝ) : ℂ) • vv n r h0 h1 (bbv g)) = _
    rw [inner_smul_right, vv_inner]
    push_cast
    ring
  have hY0 : inner ℂ Y (vv n r h0 h1 0) = ((∫ g, w g ∂μ : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hcY, Complex.conj_ofReal]
    simp
  have hYY : inner ℂ Y Y = ((∫ p : Ω × Ω,
      w p.1 * w p.2 * Real.exp (kap r * ∑ a, bbv p.1 a * bbv p.2 a) ∂(μ.prod μ) : ℝ) : ℂ) := by
    have e1 : inner ℂ Y Y = ∫ g, inner ℂ Y (((w g : ℝ) : ℂ) • vv n r h0 h1 (bbv g)) ∂μ := by
      rw [integral_inner (𝕜 := ℂ) hint Y, ← hY]
    rw [e1, integral_prod _ hk, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show inner ℂ Y (((w g : ℝ) : ℂ) • vv n r h0 h1 (bbv g)) = _
    rw [inner_smul_right, ← inner_conj_symm, hcY, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    show w g * (w g' * Real.exp (kap r * ∑ a, bbv g a * bbv g' a)) = _
    ring
  have hre1 : RCLike.re (inner ℂ Y (vv n r h0 h1 0)) = ∫ g, w g ∂μ := by
    rw [hY0]
    exact Complex.ofReal_re _
  have hre2 : RCLike.re (inner ℂ Y Y) = ∫ p : Ω × Ω,
      w p.1 * w p.2 * Real.exp (kap r * ∑ a, bbv p.1 a * bbv p.2 a) ∂(μ.prod μ) := by
    rw [hYY]
    exact Complex.ofReal_re _
  rw [norm_sub_sq (𝕜 := ℂ), hv0, ← inner_self_eq_norm_sq (𝕜 := ℂ), hre1, hre2]

end

end PartK1

section PartK2

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### Linear images of Gaussian vectors and the bilinear form -/

/-- `g ↦ M g` on the Euclidean space. -/
private def mv {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) : ι → ℝ := M *ᵥ g.ofLp

private lemma mv_measurable {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Measurable (mv M) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [mv, Matrix.mulVec, dotProduct]
  fun_prop

private lemma mv_continuous {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Continuous (mv M) := by
  refine continuous_pi fun i => ?_
  simp only [mv, Matrix.mulVec, dotProduct]
  fun_prop

/-- The matrix `M = HᵀH + κ BᵀB` of the bilinear form `⟨Hx, Hy⟩ + κ⟨Bx, By⟩`. -/
private def Mmat {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Hmᵀ * Hm + κ • (Bmᵀ * Bm)

private lemma Mmat_symm {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ) :
    (Mmat κ Hm Bm).IsSymm := by
  unfold Mmat Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose]

private lemma dot_gram {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    ∑ a, (A *ᵥ x) a * (A *ᵥ y) a = ∑ i, ∑ j, x i * (Aᵀ * A) i j * y j := by
  have h1 : ∑ a, (A *ᵥ x) a * (A *ᵥ y) a = (A *ᵥ x) ⬝ᵥ (A *ᵥ y) := rfl
  rw [h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private lemma bilin_eq {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ) (x y : ι → ℝ) :
    ∑ a, (Hm *ᵥ x) a * (Hm *ᵥ y) a + κ * ∑ a, (Bm *ᵥ x) a * (Bm *ᵥ y) a =
      ∑ i, ∑ j, x i * Mmat κ Hm Bm i j * y j := by
  rw [dot_gram, dot_gram, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Mmat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma trace_mul_self_symm {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    (M * M).trace = ∑ i, ∑ j, M i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hM.apply i j, sq]

private lemma trace_mul_self_nonneg {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    0 ≤ (M * M).trace := by
  rw [trace_mul_self_symm M hM]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `xᵀ M x ≤ ‖M‖_F ‖x‖²`. -/
private lemma quad_le_frob {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (hM : M.IsSymm) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * M i j * x j ≤ Real.sqrt ((M * M).trace) * ∑ i, x i ^ 2 := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ι × ι))
    (fun p => M p.1 p.2) (fun p => x p.1 * x p.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have e1 : ∑ i, ∑ j, (x i * x j) ^ 2 = (∑ i, x i ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : Real.sqrt ((∑ i, x i ^ 2) ^ 2) = ∑ i, x i ^ 2 :=
    Real.sqrt_sq (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [e1, e2, ← trace_mul_self_symm M hM] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma le_sqrt_of_forall_amgm (x T : ℝ) (hT : 0 ≤ T)
    (h : ∀ s : ℝ, 0 < s → x ≤ T / (2 * s) + s / 2) : x ≤ Real.sqrt T := by
  rcases hT.eq_or_lt with hT0 | hTpos
  · rw [← hT0, Real.sqrt_zero]
    by_contra hx
    rw [not_le] at hx
    have := h x hx
    rw [← hT0, zero_div, zero_add] at this
    linarith
  · have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
    have h2 := h _ hs
    have h3 : T / (2 * Real.sqrt T) + Real.sqrt T / 2 = Real.sqrt T := by
      have h4 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT
      field_simp
      nlinarith
    rwa [h3] at h2

/-! ### The kernel integrals -/

/-- The integrand `w(g, z) w(g', z) exp(κ⟨b_g, b_{g'}⟩)`. -/
private def kfun {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι) : ℝ :=
  cmw (mv Hm) (q.1.1, q.2) * cmw (mv Hm) (q.1.2, q.2) *
    Real.exp (κ * ∑ a, mv Bm q.1.1 a * mv Bm q.1.2 a)

private lemma kfun_nonneg {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι) : 0 ≤ kfun κ Hm Bm q :=
  mul_nonneg (mul_nonneg (cmw_pos _ _).le (cmw_pos _ _).le) (Real.exp_pos _).le

private lemma kfun_measurable {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ) :
    Measurable (kfun κ Hm Bm) := by
  have hw := cmw_measurable (mv Hm) (mv_measurable Hm)
  have h1 : Measurable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι =>
      cmw (mv Hm) (q.1.1, q.2)) := hw.comp (by fun_prop)
  have h2 : Measurable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι =>
      cmw (mv Hm) (q.1.2, q.2)) := hw.comp (by fun_prop)
  have hb1 : ∀ a, Measurable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      EuclideanSpace ℝ ι => mv Bm q.1.1 a) := fun a =>
    (measurable_pi_apply a).comp ((mv_measurable Bm).comp (by fun_prop))
  have hb2 : ∀ a, Measurable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      EuclideanSpace ℝ ι => mv Bm q.1.2 a) := fun a =>
    (measurable_pi_apply a).comp ((mv_measurable Bm).comp (by fun_prop))
  unfold kfun
  exact (h1.mul h2).mul (Real.measurable_exp.comp
    ((Finset.measurable_sum _ fun a _ => (hb1 a).mul (hb2 a)).const_mul κ))

/-- Integrating out `z`: `∫ w(g, z) w(g', z) dγ(z) = exp⟨h_g, h_{g'}⟩`. -/
private lemma kfun_inner {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    Integrable (fun z => kfun κ Hm Bm (p, z)) (stdGaussian (EuclideanSpace ℝ ι)) ∧
    ∫ z, kfun κ Hm Bm (p, z) ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      Real.exp (∑ i, ∑ j, p.1 i * Mmat κ Hm Bm i j * p.2 j) := by
  obtain ⟨hi, he⟩ := gauss_exp (fun i => mv Hm p.1 i + mv Hm p.2 i)
  have e : (fun z : EuclideanSpace ℝ ι => kfun κ Hm Bm (p, z)) = fun z =>
      Real.exp (∑ i, (mv Hm p.1 i + mv Hm p.2 i) * z i) *
        Real.exp (-((∑ i, mv Hm p.1 i ^ 2) / 2) - (∑ i, mv Hm p.2 i ^ 2) / 2 +
          κ * ∑ a, mv Bm p.1 a * mv Bm p.2 a) := by
    funext z
    unfold kfun cmw
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  rw [e]
  refine ⟨hi.mul_const _, ?_⟩
  rw [integral_mul_const, he, ← Real.exp_add, ← bilin_eq]
  congr 1
  have e2 : ∑ i, (mv Hm p.1 i + mv Hm p.2 i) ^ 2 =
      ∑ i, mv Hm p.1 i ^ 2 + 2 * ∑ i, mv Hm p.1 i * mv Hm p.2 i + ∑ i, mv Hm p.2 i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  unfold mv
  ring

/-- The triple integrability and the bound `∫ k ≤ 1 + Tr M²`. -/
private lemma kfun_integrable {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (hT : (Mmat κ Hm Bm * Mmat κ Hm Bm).trace ≤ 1 / 2) :
    Integrable (kfun κ Hm Bm) (((stdGaussian (EuclideanSpace ℝ ι)).prod
      (stdGaussian (EuclideanSpace ℝ ι))).prod (stdGaussian (EuclideanSpace ℝ ι))) ∧
    ∫ q, kfun κ Hm Bm q ∂(((stdGaussian (EuclideanSpace ℝ ι)).prod
      (stdGaussian (EuclideanSpace ℝ ι))).prod (stdGaussian (EuclideanSpace ℝ ι))) ≤
      1 + (Mmat κ Hm Bm * Mmat κ Hm Bm).trace := by
  obtain ⟨hb1, hb2⟩ := gaussian_bilinear_exp_bound (Mmat κ Hm Bm) (Mmat_symm κ Hm Bm) hT
  obtain ⟨h1, h2⟩ := prod_integrable_of_nonneg
    ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)))
    (stdGaussian (EuclideanSpace ℝ ι)) (kfun κ Hm Bm) (kfun_measurable κ Hm Bm)
    (kfun_nonneg κ Hm Bm)
    (fun p => Real.exp (∑ i, ∑ j, p.1 i * Mmat κ Hm Bm i j * p.2 j))
    (fun p => (kfun_inner κ Hm Bm p).1) (fun p => (kfun_inner κ Hm Bm p).2) hb1
  exact ⟨h1, h2.trans_le hb2⟩

/-- `κ‖Bg‖² ≤ gᵀMg ≤ ‖M‖_F ‖g‖²`. -/
private lemma kap_quad_le {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (hT : (Mmat κ Hm Bm * Mmat κ Hm Bm).trace ≤ 1 / 2) (x : ι → ℝ) :
    κ * ∑ a, (Bm *ᵥ x) a ^ 2 ≤ Real.sqrt (1 / 2) * ∑ i, x i ^ 2 := by
  have h1 := bilin_eq κ Hm Bm x x
  have h2 := quad_le_frob (Mmat κ Hm Bm) (Mmat_symm κ Hm Bm) x
  have h3 : 0 ≤ ∑ a, (Hm *ᵥ x) a * (Hm *ᵥ x) a :=
    Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have h4 : ∑ a, (Bm *ᵥ x) a ^ 2 = ∑ a, (Bm *ᵥ x) a * (Bm *ᵥ x) a :=
    Finset.sum_congr rfl fun a _ => sq _
  have h5 : Real.sqrt ((Mmat κ Hm Bm * Mmat κ Hm Bm).trace) * ∑ i, x i ^ 2 ≤
      Real.sqrt (1 / 2) * ∑ i, x i ^ 2 :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hT)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [h4]
  linarith

private lemma sqrt_half_lt : Real.sqrt (1 / 2) / 2 < 1 / 2 := by
  have h : Real.sqrt (1 / 2) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- The norm bound for the Bochner integrand. -/
private def nfun {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  cmw (mv Hm) ω * Real.exp (κ / 2 * ∑ a, mv Bm ω.1 a ^ 2)

private lemma nfun_integrable {ι : Type} [Fintype ι] (κ : ℝ) (Hm Bm : Matrix ι ι ℝ)
    (hT : (Mmat κ Hm Bm * Mmat κ Hm Bm).trace ≤ 1 / 2) :
    Integrable (nfun κ Hm Bm) ((stdGaussian (EuclideanSpace ℝ ι)).prod
      (stdGaussian (EuclideanSpace ℝ ι))) := by
  have hw := cmw_measurable (mv Hm) (mv_measurable Hm)
  have hem : Measurable (fun g : EuclideanSpace ℝ ι => Real.exp (κ / 2 * ∑ a, mv Bm g a ^ 2)) :=
    Real.measurable_exp.comp ((Finset.measurable_sum _ fun a _ =>
      ((measurable_pi_apply a).comp (mv_measurable Bm)).pow_const 2).const_mul _)
  have hg : Integrable (fun g : EuclideanSpace ℝ ι => Real.exp (κ / 2 * ∑ a, mv Bm g a ^ 2))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine Integrable.mono' (gauss_exp_sq (Real.sqrt (1 / 2) / 2) sqrt_half_lt)
      hem.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h := kap_quad_le κ Hm Bm hT g.ofLp
    unfold mv
    have e : ∑ i, g i ^ 2 = ∑ i, g.ofLp i ^ 2 := rfl
    rw [e]
    linarith
  refine (prod_integrable_of_nonneg (stdGaussian (EuclideanSpace ℝ ι))
    (stdGaussian (EuclideanSpace ℝ ι)) (nfun κ Hm Bm) ?_ (fun p => ?_)
    (fun g => Real.exp (κ / 2 * ∑ a, mv Bm g a ^ 2)) (fun g => ?_) (fun g => ?_) hg).1
  · exact hw.mul (hem.comp measurable_fst)
  · exact mul_nonneg (cmw_pos _ _).le (Real.exp_pos _).le
  · show Integrable (fun z => cmw (mv Hm) (g, z) * Real.exp (κ / 2 * ∑ a, mv Bm g a ^ 2))
      (stdGaussian (EuclideanSpace ℝ ι))
    exact (cmw_inner (mv Hm) g).1.mul_const _
  · show ∫ z, cmw (mv Hm) (g, z) * Real.exp (κ / 2 * ∑ a, mv Bm g a ^ 2)
      ∂(stdGaussian (EuclideanSpace ℝ ι)) = _
    rw [integral_mul_const, (cmw_inner (mv Hm) g).2, one_mul]

end

end PartK2

section PartK3

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-- The real phase space `ℝ^{2n}` in interleaved coordinates. -/
private abbrev EE (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard Gaussian on the phase space. -/
private abbrev GG (n : ℕ) : Measure (EE n) := stdGaussian (EE n)

private lemma vv_norm (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (b : Fin n × Fin 2 → ℝ) :
    ‖vv n r h0 h1 b‖ = Real.exp (kap r / 2 * ∑ a, b a ^ 2) := by
  refine (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 ?_
  have e : ∑ a, b a * b a = ∑ a, b a ^ 2 := Finset.sum_congr rfl fun a _ => (sq _).symm
  rw [vv_norm_sq, sq, ← Real.exp_add, e]
  congr 1
  ring

/-- The bound for a fixed `z`: the `g`-integral is an inner product with `Y_z - v_0`. -/
private lemma slice_bound {n : ℕ} (r : ℝ) (h0 : 0 < r) (h1 : r < 1)
    (Hm Bm : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (z : EE n)
    (g₀ : Hilbert ((Fin n → ℕ) × (Fin n → ℕ))) (hg₀ : ‖g₀‖ ≤ 1)
    (hn : Integrable (fun g : EE n => nfun (kap r) Hm Bm (g, z)) (GG n))
    (hk : Integrable (fun p : EE n × EE n => kfun (kap r) Hm Bm (p, z)) ((GG n).prod (GG n))) :
    ‖∫ g : EE n, (((cmw (mv Hm) (g, z) : ℝ) : ℂ) * inner ℂ g₀ (vv n r h0 h1 (mv Bm g)) -
        inner ℂ g₀ (vv n r h0 h1 0)) ∂(GG n)‖ ^ 2 ≤
      (∫ p : EE n × EE n, kfun (kap r) Hm Bm (p, z) ∂((GG n).prod (GG n))) -
        2 * ∫ g : EE n, cmw (mv Hm) (g, z) ∂(GG n) + 1 := by
  have hwm : Measurable (fun g : EE n => cmw (mv Hm) (g, z)) :=
    (cmw_measurable (mv Hm) (mv_measurable Hm)).comp (measurable_id.prodMk measurable_const)
  have hfm : AEStronglyMeasurable
      (fun g : EE n => ((cmw (mv Hm) (g, z) : ℝ) : ℂ) • vv n r h0 h1 (mv Bm g)) (GG n) :=
    AEStronglyMeasurable.smul (Complex.measurable_ofReal.comp hwm).aestronglyMeasurable
      ((vv_continuous n r h0 h1).comp (mv_continuous Bm)).aestronglyMeasurable
  have hfi : Integrable
      (fun g : EE n => ((cmw (mv Hm) (g, z) : ℝ) : ℂ) • vv n r h0 h1 (mv Bm g)) (GG n) := by
    refine Integrable.mono' hn hfm (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cmw_pos _ _), vv_norm]
    exact le_rfl
  have chi := chi_sq_identity (GG n) r h0 h1 (fun g : EE n => cmw (mv Hm) (g, z)) (mv Bm) hfi hk
  have e : (fun g : EE n => ((cmw (mv Hm) (g, z) : ℝ) : ℂ) * inner ℂ g₀ (vv n r h0 h1 (mv Bm g)) -
      inner ℂ g₀ (vv n r h0 h1 0)) = fun g =>
      inner ℂ g₀ (((cmw (mv Hm) (g, z) : ℝ) : ℂ) • vv n r h0 h1 (mv Bm g) - vv n r h0 h1 0) := by
    funext g
    rw [inner_sub_right, inner_smul_right]
  have hint2 : ∫ g : EE n, inner ℂ g₀ (((cmw (mv Hm) (g, z) : ℝ) : ℂ) • vv n r h0 h1 (mv Bm g) -
      vv n r h0 h1 0) ∂(GG n) = inner ℂ g₀ (∫ g : EE n, (((cmw (mv Hm) (g, z) : ℝ) : ℂ) •
        vv n r h0 h1 (mv Bm g) - vv n r h0 h1 0) ∂(GG n)) :=
    integral_inner (𝕜 := ℂ) (hfi.sub (integrable_const _)) g₀
  rw [e, hint2, integral_sub hfi (integrable_const _), integral_const, probReal_univ, one_smul]
  have h2 : ‖inner ℂ g₀ ((∫ g : EE n, ((cmw (mv Hm) (g, z) : ℝ) : ℂ) • vv n r h0 h1 (mv Bm g)
      ∂(GG n)) - vv n r h0 h1 0)‖ ≤ ‖(∫ g : EE n, ((cmw (mv Hm) (g, z) : ℝ) : ℂ) •
        vv n r h0 h1 (mv Bm g) ∂(GG n)) - vv n r h0 h1 0‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) hg₀
  refine (pow_le_pow_left₀ (norm_nonneg _) h2 2).trans (le_of_eq ?_)
  exact chi

/-- The partial traces of `(A' - A₀) V` against contractions are bounded by `√(Tr M²)`. -/
private theorem pairing_bound {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)} {l₀ r₀ : ℕ → Hilbert (Fin n → ℕ)}
    (hN : IsNuc Θ l₀ r₀)
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (hden : IsDensity (matOf Θ))
    (mf : Fin n × Fin 2 → ℝ) (Rm Hm Bm : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hT : (Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace ≤ 1 / 2)
    (A' A₀ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    (e0 : ∀ u v, matOf A₀ u v = ∫ z : EE n, matOf (cj Θ (mf + Rm *ᵥ z.ofLp)) u v ∂(GG n))
    (e1 : ∀ u v, matOf A' u v = ∫ ω : EE n × EE n, ((cmw (mv Hm) ω : ℝ) : ℂ) *
      matOf (cj Θ (mf + Rm *ᵥ ω.2.ofLp + Bm *ᵥ ω.1.ofLp)) u v ∂((GG n).prod (GG n)))
    (V : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) (hV : ‖V‖ ≤ 1)
    (F : Finset (Fin n → ℕ)) :
    ‖∑ u ∈ F, ((A' - A₀) (V (bv u))) u‖ ≤
      Real.sqrt ((Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace) := by
  have hT0 : 0 ≤ (Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace :=
    trace_mul_self_nonneg _ (Mmat_symm (kap r) Hm Bm)
  have hwm := cmw_measurable (mv Hm) (mv_measurable Hm)
  have hwi : Integrable (cmw (mv Hm)) ((GG n).prod (GG n)) :=
    cmw_integrable (mv Hm) (mv_measurable Hm) (GG n)
  -- measurability of the displacement fields
  have hYb : ∀ a, Measurable (fun ω : EE n × EE n => (mf + Rm *ᵥ ω.2.ofLp) a) := by
    intro a
    show Measurable (fun ω : EE n × EE n => mf a + mv Rm ω.2 a)
    exact measurable_const.add ((measurable_pi_apply a).comp ((mv_measurable Rm).comp measurable_snd))
  have hYt : ∀ a, Measurable (fun ω : EE n × EE n =>
      (mf + Rm *ᵥ ω.2.ofLp + Bm *ᵥ ω.1.ofLp) a) := by
    intro a
    show Measurable (fun ω : EE n × EE n => mf a + mv Rm ω.2 a + mv Bm ω.1 a)
    exact (measurable_const.add ((measurable_pi_apply a).comp
      ((mv_measurable Rm).comp measurable_snd))).add
      ((measurable_pi_apply a).comp ((mv_measurable Bm).comp measurable_fst))
  -- the two operators act coordinatewise as mixtures
  have e0' : ∀ u v, matOf A₀ u v = ∫ ω : EE n × EE n,
      (((1 : ℝ)) : ℂ) * matOf (cj Θ (mf + Rm *ᵥ ω.2.ofLp)) u v ∂((GG n).prod (GG n)) := by
    intro u v
    have h := integral_fun_snd (μ := GG n) (ν := GG n)
      (fun z : EE n => matOf (cj Θ (mf + Rm *ᵥ z.ofLp)) u v)
    rw [probReal_univ, one_smul] at h
    rw [e0, ← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have hA' := fun (y : Hilbert (Fin n → ℕ)) (u : Fin n → ℕ) =>
    op_mix_apply ((GG n).prod (GG n)) (cmw (mv Hm)) hwm (fun ω => (cmw_pos _ ω).le) hwi
      (fun ω => cj Θ (mf + Rm *ᵥ ω.2.ofLp + Bm *ᵥ ω.1.ofLp)) ‖Θ‖ (fun ω => cj_norm_le Θ _)
      (fun u v => cj_measurable _ hYt hN u v) A' e1 y u
  have hA0 := fun (y : Hilbert (Fin n → ℕ)) (u : Fin n → ℕ) =>
    op_mix_apply ((GG n).prod (GG n)) (fun _ => (1 : ℝ)) measurable_const (fun _ => zero_le_one)
      (integrable_const _) (fun ω => cj Θ (mf + Rm *ᵥ ω.2.ofLp)) ‖Θ‖ (fun ω => cj_norm_le Θ _)
      (fun u v => cj_measurable _ hYb hN u v) A₀ e0' y u
  -- the representing vectors
  have hrep := fun z : EE n => pairing_repr h0 h1 hdiag hden V hV F (mf + Rm *ᵥ z.ofLp)
  choose gz hgz1 hgz2 using hrep
  obtain ⟨J, hJ⟩ : ∃ J : EE n × EE n → ℂ, J = fun ω => ((cmw (mv Hm) ω : ℝ) : ℂ) *
      inner ℂ (gz ω.2) (vv n r h0 h1 (mv Bm ω.1)) - inner ℂ (gz ω.2) (vv n r h0 h1 0) := ⟨_, rfl⟩
  have hJpt : J = fun ω => ∑ u ∈ F, (((cmw (mv Hm) ω : ℝ) : ℂ) *
      (cj Θ (mf + Rm *ᵥ ω.2.ofLp + Bm *ᵥ ω.1.ofLp) (V (bv u))) u -
      (((1 : ℝ)) : ℂ) * (cj Θ (mf + Rm *ᵥ ω.2.ofLp) (V (bv u))) u) := by
    funext ω
    have ha := hgz2 ω.2 (Bm *ᵥ ω.1.ofLp)
    have hb := hgz2 ω.2 0
    rw [add_zero] at hb
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha, hb, hJ]
    simp only [Complex.ofReal_one, one_mul]
    rfl
  have hJint : Integrable J ((GG n).prod (GG n)) := by
    rw [hJpt]
    exact integrable_finsetSum _ fun u _ => ((hA' (V (bv u)) u).1).sub ((hA0 (V (bv u)) u).1)
  have hΛ : ∑ u ∈ F, ((A' - A₀) (V (bv u))) u = ∫ ω, J ω ∂((GG n).prod (GG n)) := by
    have hfs : ∀ u ∈ F, Integrable (fun ω : EE n × EE n => ((cmw (mv Hm) ω : ℝ) : ℂ) *
        (cj Θ (mf + Rm *ᵥ ω.2.ofLp + Bm *ᵥ ω.1.ofLp) (V (bv u))) u -
        (((1 : ℝ)) : ℂ) * (cj Θ (mf + Rm *ᵥ ω.2.ofLp) (V (bv u))) u) ((GG n).prod (GG n)) :=
      fun u _ => ((hA' (V (bv u)) u).1).sub ((hA0 (V (bv u)) u).1)
    simp only [hJpt]
    rw [integral_finsetSum _ hfs]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_sub (hA' _ u).1 (hA0 _ u).1, ← (hA' _ u).2, ← (hA0 _ u).2]
    rfl
  -- the kernel integrals
  have hk := kfun_integrable (kap r) Hm Bm hT
  have hn := nfun_integrable (kap r) Hm Bm hT
  have hae1 := hn.prod_left_ae
  have hae2 := hk.1.prod_left_ae
  obtain ⟨Q, hQ⟩ : ∃ Q : EE n → ℝ, Q = fun z =>
      ∫ p : EE n × EE n, kfun (kap r) Hm Bm (p, z) ∂((GG n).prod (GG n)) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : EE n → ℝ, W = fun z => ∫ g : EE n, cmw (mv Hm) (g, z) ∂(GG n) :=
    ⟨_, rfl⟩
  have hQi : Integrable Q (GG n) := by
    rw [hQ]
    exact hk.1.integral_prod_right
  have hWi : Integrable W (GG n) := by
    rw [hW]
    exact hwi.integral_prod_right
  have hQint : ∫ z, Q z ∂(GG n) ≤ 1 + (Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace := by
    rw [hQ, ← integral_prod_symm _ hk.1]
    exact hk.2
  have hWint : ∫ z, W z ∂(GG n) = 1 := by
    rw [hW, ← integral_prod_symm _ hwi, integral_prod _ hwi]
    simp only [(cmw_inner (mv Hm) _).2]
    simp
  refine le_sqrt_of_forall_amgm _ _ hT0 fun s hs => ?_
  rw [hΛ, integral_prod_symm J hJint]
  have hbound : ∀ᵐ z ∂(GG n), ‖∫ g, J (g, z) ∂(GG n)‖ ≤ (Q z - 2 * W z + 1) / (2 * s) + s / 2 := by
    filter_upwards [hae1, hae2] with z hz1 hz2
    have h := slice_bound r h0 h1 Hm Bm z (gz z) (hgz1 z) hz1 hz2
    have h' : ‖∫ g, J (g, z) ∂(GG n)‖ ^ 2 ≤ Q z - 2 * W z + 1 := by
      rw [hJ, hQ, hW]
      exact h
    have hx : 0 ≤ Q z - 2 * W z + 1 := (sq_nonneg _).trans h'
    calc ‖∫ g, J (g, z) ∂(GG n)‖ = Real.sqrt (‖∫ g, J (g, z) ∂(GG n)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (Q z - 2 * W z + 1) := Real.sqrt_le_sqrt h'
      _ ≤ (Q z - 2 * W z + 1) / (2 * s) + s / 2 := sqrt_le_amgm _ s hx hs
  have hGi : Integrable (fun z => (Q z - 2 * W z + 1) / (2 * s) + s / 2) (GG n) :=
    (((hQi.sub (hWi.const_mul 2)).add (integrable_const 1)).div_const _).add (integrable_const _)
  refine (norm_integral_le_of_norm_le hGi hbound).trans ?_
  have hval : ∫ z, ((Q z - 2 * W z + 1) / (2 * s) + s / 2) ∂(GG n) =
      ((∫ z, Q z ∂(GG n)) - 2 * 1 + 1) / (2 * s) + s / 2 := by
    have i1 : Integrable (fun z => Q z - 2 * W z) (GG n) := hQi.sub (hWi.const_mul 2)
    have i2 : Integrable (fun z => Q z - 2 * W z + 1) (GG n) := i1.add (integrable_const 1)
    have i3 : Integrable (fun z => (Q z - 2 * W z + 1) / (2 * s)) (GG n) := i2.div_const _
    rw [integral_add i3 (integrable_const _), integral_div, integral_add i1 (integrable_const 1),
      integral_sub hQi (hWi.const_mul 2), integral_const_mul, hWint]
    simp
  rw [hval]
  have h3 : (∫ z, Q z ∂(GG n)) - 2 * 1 + 1 ≤ (Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace := by
    linarith
  have h4 : (0 : ℝ) < 2 * s := by positivity
  have h5 := div_le_div_of_nonneg_right h3 h4.le
  linarith

end

end PartK3

section PartK4

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

private lemma single_eq_bv {I : Type} [DecidableEq I] (i : I) :
    (lp.single 2 i (1 : ℂ) : Hilbert I) = bv i := by
  unfold bv
  congr
  exact Subsingleton.elim _ _

/-- The `χ²` bound for the two mixtures. -/
private theorem mix_bound {n : ℕ} {r : ℝ} (h0 : 0 < r) (h1 : r < 1)
    {Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)} {l₀ r₀ : ℕ → Hilbert (Fin n → ℕ)}
    (hN : IsNuc Θ l₀ r₀)
    (hdiag : matOf Θ = fun u v => if u = v then ((pw n r u : ℝ) : ℂ) else 0)
    (hden : IsDensity (matOf Θ))
    (mf : Fin n × Fin 2 → ℝ) (Rm Hm Bm : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hT : (Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace ≤ 1 / 2)
    (X' X : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) (hX' : IsDensity X') (hX : IsDensity X)
    (e0 : ∀ u v, X u v = ∫ z : EE n, matOf (cj Θ (mf + Rm *ᵥ z.ofLp)) u v ∂(GG n))
    (e1 : ∀ u v, X' u v = ∫ ω : EE n × EE n, ((cmw (mv Hm) ω : ℝ) : ℂ) *
      matOf (cj Θ (mf + Rm *ᵥ ω.2.ofLp + Bm *ᵥ ω.1.ofLp)) u v ∂((GG n).prod (GG n))) :
    traceSize (X' - X) ≤
      ENNReal.ofReal (Real.sqrt ((Mmat (kap r) Hm Bm * Mmat (kap r) Hm Bm).trace)) := by
  obtain ⟨A', l', r', hN', hm'⟩ := exists_op X' hX'.1
  obtain ⟨A₀, l0, r0, hN0, hm0⟩ := exists_op X hX.1
  have hp' : IsPos A' := isPos_of_matrix A' (by rw [hm']; exact hX'.2.1)
  have hp0 : IsPos A₀ := isPos_of_matrix A₀ (by rw [hm0]; exact hX.2.1)
  have hsa : IsSelfAdjoint (A' - A₀) :=
    (isSelfAdjoint_of_isPos hp').sub (isSelfAdjoint_of_isPos hp0)
  have hmat : X' - X = fun u v : Fin n → ℕ => inner ℂ (lp.single 2 u (1 : ℂ) :
      Hilbert (Fin n → ℕ)) ((A' - A₀) (lp.single 2 v (1 : ℂ))) := by
    funext u v
    rw [single_eq_bv, single_eq_bv, inner_bv_left, ← hm', ← hm0]
    rfl
  rw [hmat]
  refine traceSize_le_of_pairing (A' - A₀) hsa _ (Real.sqrt_nonneg _) fun V hV F => ?_
  have h := pairing_bound h0 h1 hN hdiag hden mf Rm Hm Bm hT A' A₀
    (fun u v => by rw [hm0]; exact e0 u v) (fun u v => by rw [hm']; exact e1 u v) V hV F
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [single_eq_bv, inner_bv_left]

end

end PartK4

section PartM

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

noncomputable section

/-! ### The matrix inequality `Tr M² ≤ K² Tr(S⁻¹ΔS⁻¹Δ)` -/

open scoped MatrixOrder in
/-- The trace of a product of two positive semidefinite matrices is non-negative. -/
private lemma trace_mul_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  have h := (hP.mul_mul_conjTranspose_same B).trace_nonneg
  have e : (P * (star B * B)).trace = (B * P * Bᴴ).trace := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [e]
  exact h

private lemma gram_psd {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (Aᵀ * A).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Abstract form of the matrix inequality. -/
private lemma Mmat_trace_bound {ι : Type} [Fintype ι] [DecidableEq ι] (L Z R S : Matrix ι ι ℝ) (a κ : ℝ)
    (hL : Lᵀ = L) (hZ : Zᵀ = Z) (hR : Rᵀ = R) (hRR : R * R = S - a • (1 : Matrix ι ι ℝ))
    (hZS : Z * S = 1) (hκ : 0 ≤ κ) (hK : 1 ≤ κ * a) :
    (Mmat κ (R * Z * L) (a • (Z * L)) * Mmat κ (R * Z * L) (a • (Z * L))).trace ≤
      (κ * a) ^ 2 * (Z * (L * L) * Z * (L * L)).trace := by
  obtain ⟨P, hP⟩ : ∃ P, P = L * Z * L := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = L * Z * Z * L := ⟨_, rfl⟩
  have hHH : (R * Z * L)ᵀ * (R * Z * L) = P - a • Q := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hL, hZ, hR]
    calc L * (Z * R) * (R * Z * L) = L * Z * (R * R) * Z * L := by
          simp only [Matrix.mul_assoc]
      _ = L * (Z * S) * Z * L - a • (L * Z * Z * L) := by
          rw [hRR]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, Matrix.mul_assoc]
      _ = P - a • Q := by rw [hZS, Matrix.mul_one, hP, hQ]
  have hBB : (a • (Z * L))ᵀ * (a • (Z * L)) = (a * a) • Q := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, hL, hZ, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hQ]
    simp only [Matrix.mul_assoc]
  obtain ⟨M, hM⟩ : ∃ M, M = Mmat κ (R * Z * L) (a • (Z * L)) := ⟨_, rfl⟩
  have hMpsd : M.PosSemidef := by
    rw [hM]
    unfold Mmat
    exact (gram_psd _).add ((gram_psd _).smul hκ)
  have hMe : M = P - a • Q + κ • ((a * a) • Q) := by
    rw [hM]
    unfold Mmat
    rw [hHH, hBB]
  have hNM : ((κ * a) • P - M).PosSemidef := by
    have e : (κ * a) • P - M = (κ * a - 1) • ((R * Z * L)ᵀ * (R * Z * L)) := by
      rw [hMe, hHH]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact (gram_psd _).smul (by linarith)
  have hN : ((κ * a) • P).PosSemidef := by
    have h := hMpsd.add hNM
    rwa [add_sub_cancel] at h
  have t1 := trace_mul_nonneg hMpsd hNM
  have t2 := trace_mul_nonneg hNM hN
  rw [Matrix.mul_sub, Matrix.trace_sub] at t1
  rw [Matrix.sub_mul, Matrix.trace_sub] at t2
  have e3 : (((κ * a) • P) * ((κ * a) • P)).trace = (κ * a) ^ 2 * (Z * (L * L) * Z * (L * L)).trace := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul, ← sq, hP]
    congr 1
    rw [Matrix.mul_assoc L, Matrix.mul_assoc L, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [← hM, ← e3]
  linarith

/-- `K_ν = κ a ≥ 1` and the value of `κ`. -/
private lemma kap_facts (ν : ℝ) (hν : 0 < ν) :
    0 ≤ kap (ν / (1 + ν)) ∧ 1 ≤ kap (ν / (1 + ν)) * (1 / 2 + ν) ∧
      kap (ν / (1 + ν)) * (1 / 2 + ν) = (1 / 2 + ν) / Real.sqrt (ν * (1 + ν)) := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have hr : 0 < ν / (1 + ν) := by positivity
  have hs : 0 < Real.sqrt (ν * (1 + ν)) := Real.sqrt_pos.2 (by positivity)
  have hk : kap (ν / (1 + ν)) = 1 / Real.sqrt (ν * (1 + ν)) := by
    unfold kap
    have e1 : 1 - ν / (1 + ν) = 1 / (1 + ν) := by
      field_simp
      ring
    have e2 : Real.sqrt (ν / (1 + ν)) = Real.sqrt (ν * (1 + ν)) / (1 + ν) := by
      rw [show ν / (1 + ν) = ν * (1 + ν) / (1 + ν) ^ 2 by field_simp, Real.sqrt_div (by positivity),
        Real.sqrt_sq h1.le]
    rw [e1, e2]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hk]
    positivity
  · rw [hk, one_div, inv_mul_eq_div, le_div_iff₀ hs, one_mul]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  · rw [hk]
    field_simp

open scoped MatrixOrder in
/-- The concrete split and trace bound for `S ⪰ a·1`, `Δ ⪰ 0`. -/
private lemma split_trace_facts {ι : Type} [Fintype ι] [DecidableEq ι] (Si Δi : Matrix ι ι ℝ) (a κ : ℝ)
    (ha : 0 < a) (hTi : (Si - a • (1 : Matrix ι ι ℝ)).PosSemidef) (hΔi : Δi.PosSemidef)
    (hκ : 0 ≤ κ) (hK : 1 ≤ κ * a) :
    CFC.sqrt (Si - a • (1 : Matrix ι ι ℝ)) *
        (CFC.sqrt (Si - a • (1 : Matrix ι ι ℝ)) * Si⁻¹ * CFC.sqrt Δi) +
      a • (Si⁻¹ * CFC.sqrt Δi) = CFC.sqrt Δi ∧
    (Mmat κ (CFC.sqrt (Si - a • (1 : Matrix ι ι ℝ)) * Si⁻¹ * CFC.sqrt Δi)
        (a • (Si⁻¹ * CFC.sqrt Δi)) *
      Mmat κ (CFC.sqrt (Si - a • (1 : Matrix ι ι ℝ)) * Si⁻¹ * CFC.sqrt Δi)
        (a • (Si⁻¹ * CFC.sqrt Δi))).trace ≤
      (κ * a) ^ 2 * (Si⁻¹ * Δi * Si⁻¹ * Δi).trace := by
  have hSpd : Si.PosDef := by
    have h1 := Matrix.PosDef.posSemidef_add hTi ((Matrix.PosDef.one (n := ι) (R := ℝ)).smul ha)
    rwa [sub_add_cancel] at h1
  have hdet : IsUnit Si.det := (Matrix.isUnit_iff_isUnit_det Si).mp hSpd.isUnit
  have hSinv : Si * Si⁻¹ = 1 := Matrix.mul_nonsing_inv Si hdet
  have hinvS : Si⁻¹ * Si = 1 := Matrix.nonsing_inv_mul Si hdet
  have hZ : Si⁻¹ᵀ = Si⁻¹ := by
    have h := hSpd.isHermitian.inv
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hRR := sqrt_mul_self _ hTi
  have hRs := sqrt_sym (Si - a • (1 : Matrix ι ι ℝ))
  have hLL := sqrt_mul_self _ hΔi
  have hLs := sqrt_sym Δi
  refine ⟨?_, ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRR, Matrix.sub_mul, Matrix.sub_mul, hSinv,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, sub_add_cancel]
  · have h := Mmat_trace_bound (CFC.sqrt Δi) Si⁻¹ (CFC.sqrt (Si - a • (1 : Matrix ι ι ℝ))) Si a κ
      hLs hZ hRs hRR hinvS hκ hK
    rwa [hLL] at h

end

end PartM

section PartF

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### The two mixtures as integrals over `γ ⊗ γ` -/

open scoped MatrixOrder in
private lemma mix_entry_base {n : ℕ} (Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    {l₀ r₀ : ℕ → Hilbert (Fin n → ℕ)} (hN : IsNuc Θ l₀ r₀) (mf : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (u v : Fin n → ℕ) :
    mixArr Θ mf T u v =
      ∫ z : EE n, matOf (cj Θ (mf + CFC.sqrt T *ᵥ z.ofLp)) u v ∂(GG n) := by
  have hm : Measurable (fun y : EE n => matOf (cj Θ (fun a => y a)) u v) :=
    cj_measurable (fun (ω : EE n) a => ω a) (fun a => by fun_prop) hN u v
  unfold mixArr
  rw [show multivariateGaussian (WithLp.toLp 2 mf) T =
      (stdGaussian (EE n)).map (fun z => WithLp.toLp 2 mf +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt T) z) from rfl]
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable]
  rfl

open scoped MatrixOrder in
private lemma mix_entry_tilt {n : ℕ} (Θ : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ))
    {l₀ r₀ : ℕ → Hilbert (Fin n → ℕ)} (hN : IsNuc Θ l₀ r₀) (mf : Fin n × Fin 2 → ℝ)
    (Si Δi : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (a : ℝ) (ha : 0 < a)
    (hTi : (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef)
    (hΔi : Δi.PosSemidef) (u v : Fin n → ℕ) :
    mixArr Θ mf (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + Δi) u v =
      ∫ ω : EE n × EE n, ((cmw (mv (CFC.sqrt (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *
          Si⁻¹ * CFC.sqrt Δi)) ω : ℝ) : ℂ) *
        matOf (cj Θ (mf + CFC.sqrt (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *ᵥ
          ω.2.ofLp + (a • (Si⁻¹ * CFC.sqrt Δi)) *ᵥ ω.1.ofLp)) u v ∂((GG n).prod (GG n)) := by
  have hm : Measurable (fun y : EE n => matOf (cj Θ (fun i => y i)) u v) :=
    cj_measurable (fun (ω : EE n) a => ω a) (fun a => by fun_prop) hN u v
  have hSpd : Si.PosDef := by
    have h1 := Matrix.PosDef.posSemidef_add hTi
      ((Matrix.PosDef.one (n := Fin n × Fin 2) (R := ℝ)).smul ha)
    rwa [sub_add_cancel] at h1
  have hSinv : Si * Si⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Si ((Matrix.isUnit_iff_isUnit_det Si).mp hSpd.isUnit)
  have hRR := sqrt_mul_self _ hTi
  obtain ⟨Rm, hRm⟩ : ∃ Rm, Rm = CFC.sqrt (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨Lm, hLm⟩ : ∃ Lm, Lm = CFC.sqrt Δi := ⟨_, rfl⟩
  rw [← hRm, ← hLm]
  rw [← hRm] at hRR
  have hsplit : ∀ x : EE n, CFC.sqrt (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *ᵥ
      (mv (Rm * Si⁻¹) x) + mv (a • Si⁻¹) x = x.ofLp := by
    intro x
    rw [← hRm]
    unfold mv
    rw [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.mul_assoc, hRR, Matrix.sub_mul,
      hSinv, Matrix.smul_mul, Matrix.one_mul, sub_add_cancel, Matrix.one_mulVec]
  unfold mixArr
  rw [tilt_change (WithLp.toLp 2 mf) _ Δi hTi hΔi (mv (Rm * Si⁻¹)) (mv (a • Si⁻¹))
    (mv_measurable _) (mv_measurable _) hsplit _ hm]
  -- change of variables `x = L g`
  have hmg : multivariateGaussian (0 : EE n) Δi =
      (GG n).map (fun g => Matrix.toEuclideanCLM (𝕜 := ℝ) Lm g) := by
    have h : multivariateGaussian (0 : EE n) Δi =
        (stdGaussian (EE n)).map (fun g => 0 + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Δi) g) := rfl
    rw [h, hLm]
    simp only [zero_add]
  have hφm : Measurable (fun g : EE n => Matrix.toEuclideanCLM (𝕜 := ℝ) Lm g) := by fun_prop
  have hprod := Measure.map_prod_map (GG n) (GG n)
    (f := fun g : EE n => Matrix.toEuclideanCLM (𝕜 := ℝ) Lm g) (g := id) hφm measurable_id
  rw [Measure.map_id, ← hmg] at hprod
  have hFm : Measurable (fun ω : EE n × EE n => ((cmw (mv (Rm * Si⁻¹)) ω : ℝ) : ℂ) *
      matOf (cj Θ (fun i => (tiltX (WithLp.toLp 2 mf)
        (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) (mv (a • Si⁻¹)) ω) i)) u v) :=
    (Complex.measurable_ofReal.comp (cmw_measurable _ (mv_measurable _))).mul
      (hm.comp (tiltX_measurable _ _ _ (mv_measurable _)))
  rw [hprod, integral_map (hφm.prodMap measurable_id).aemeasurable hFm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hφ : (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1).ofLp = Lm *ᵥ ω.1.ofLp := rfl
  have h1 : mv (Rm * Si⁻¹) (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1) = mv (Rm * Si⁻¹ * Lm) ω.1 := by
    unfold mv
    rw [hφ, Matrix.mulVec_mulVec]
  have h2 : mv (a • Si⁻¹) (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1) =
      (a • (Si⁻¹ * Lm)) *ᵥ ω.1.ofLp := by
    unfold mv
    rw [hφ, Matrix.mulVec_mulVec, Matrix.smul_mul]
  have hc : cmw (mv (Rm * Si⁻¹)) (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1, ω.2) =
      cmw (mv (Rm * Si⁻¹ * Lm)) ω := by
    unfold cmw
    simp only [h1]
  have ht : (fun i => (tiltX (WithLp.toLp 2 mf)
      (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) (mv (a • Si⁻¹))
        (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1, ω.2)) i) =
      mf + Rm *ᵥ ω.2.ofLp + (a • (Si⁻¹ * Lm)) *ᵥ ω.1.ofLp := by
    rw [← h2, hRm]
    rfl
  show ((cmw (mv (Rm * Si⁻¹)) (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1, ω.2) : ℝ) : ℂ) *
      matOf (cj Θ (fun i => (tiltX (WithLp.toLp 2 mf)
        (Si - a • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) (mv (a • Si⁻¹))
          (Matrix.toEuclideanCLM (𝕜 := ℝ) Lm ω.1, ω.2)) i)) u v = _
  rw [hc, ht]

/-! ### The statement -/

private lemma final_small (K D t : ℝ) (hK : 0 ≤ K) (ht : t ≤ K ^ 2 * D) :
    Real.sqrt t / 2 ≤ Real.sqrt 2 * K * Real.sqrt D := by
  have h1 : Real.sqrt t ≤ K * Real.sqrt D := by
    calc Real.sqrt t ≤ Real.sqrt (K ^ 2 * D) := Real.sqrt_le_sqrt ht
      _ = K * Real.sqrt D := by rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
  have h2 : 0 ≤ K * Real.sqrt D := mul_nonneg hK (Real.sqrt_nonneg _)
  have h3 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  nlinarith

private lemma final_large (K D : ℝ) (hK : 0 ≤ K) (h : ¬ K ^ 2 * D ≤ 1 / 2) :
    1 ≤ Real.sqrt 2 * K * Real.sqrt D := by
  rw [not_le] at h
  have e : Real.sqrt 2 * K * Real.sqrt D = Real.sqrt (2 * (K ^ 2 * D)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
    ring
  rw [e, Real.le_sqrt' (by norm_num)]
  linarith

private theorem main {n : ℕ} (ρ ρ' : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (ν : ℝ) (hν : 0 < ν)
    (hS : (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (hord : (S' - S).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ S') :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) *
        Real.sqrt (S⁻¹ * (S' - S) * S⁻¹ * (S' - S)).trace) := by
  obtain ⟨Θ, l₀, r₀, hΘ⟩ := thermal_op_exists n ν hν
  obtain ⟨hr0, hr1, -⟩ := nu_alg ν hν
  obtain ⟨hκ0, hK1, hKeq⟩ := kap_facts ν hν
  have ha : (0 : ℝ) < 1 / 2 + ν := by linarith
  have hS' : (S' - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef := by
    have h1 := hS.add hord
    have h2 : S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) + (S' - S) =
        S' - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by abel
    rwa [h2] at h1
  have e1 := coeff_eq_mixArr hΘ ρ μ S hS h
  have e2 := coeff_eq_mixArr hΘ ρ' μ S' hS' h'
  have hT : (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix
      (qe (n := n)) qe = S.submatrix (qe (n := n)) qe -
        (1 / 2 + ν) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      qe_inj]
  have hT' : (S' - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix
      (qe (n := n)) qe = S.submatrix (qe (n := n)) qe -
        (1 / 2 + ν) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) +
          (S' - S).submatrix (qe (n := n)) qe := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, qe_inj]
    ring
  rw [hT] at e1
  rw [hT'] at e2
  have hTi : (S.submatrix (qe (n := n)) qe -
      (1 / 2 + ν) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef := by
    rw [← hT]
    exact hS.submatrix qe
  have hΔi : ((S' - S).submatrix (qe (n := n)) qe).PosSemidef := hord.submatrix qe
  obtain ⟨-, htrace⟩ := split_trace_facts (S.submatrix (qe (n := n)) qe)
    ((S' - S).submatrix (qe (n := n)) qe) (1 / 2 + ν) (kap (ν / (1 + ν))) ha hTi hΔi hκ0 hK1
  have hD : ((S.submatrix (qe (n := n)) qe)⁻¹ * (S' - S).submatrix (qe (n := n)) qe *
      (S.submatrix (qe (n := n)) qe)⁻¹ * (S' - S).submatrix (qe (n := n)) qe).trace =
      (S⁻¹ * (S' - S) * S⁻¹ * (S' - S)).trace := by
    rw [inv_reindex, mul_reindex, mul_reindex, mul_reindex, trace_reindex]
  rw [hD, hKeq] at htrace
  have hK0 : 0 ≤ (1 / 2 + ν) / Real.sqrt (ν * (1 + ν)) := by positivity
  by_cases hcase : ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) ^ 2 *
      (S⁻¹ * (S' - S) * S⁻¹ * (S' - S)).trace ≤ 1 / 2
  · have hb := mix_bound hr0 hr1 hΘ.1 hΘ.2.2.1 hΘ.2.1 (fun a => μ (qe a)) _ _ _
      (htrace.trans hcase) ρ'.coefficients ρ.coefficients ρ'.density ρ.density
      (fun u v => by rw [e1]; exact mix_entry_base Θ hΘ.1 _ _ u v)
      (fun u v => by rw [e2]; exact mix_entry_tilt Θ hΘ.1 _ _ _ _ ha hTi hΔi u v)
    unfold traceDist
    calc traceSize (ρ'.coefficients - ρ.coefficients) / 2
        ≤ ENNReal.ofReal (Real.sqrt _) / 2 := ENNReal.div_le_div_right hb 2
      _ = ENNReal.ofReal (Real.sqrt _ / 2) := by
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [h2, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (final_small _ _ _ hK0 htrace)
  · refine (traceDist_le_one ρ' ρ).trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (final_large _ _ hK0 hcase)

end

end PartF

end CovGap

theorem solution {n : ℕ} (ρ ρ' : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (ν : ℝ) (hν : 0 < ν)
    (hS : (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (hord : (S' - S).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ S') :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) *
        Real.sqrt (S⁻¹ * (S' - S) * S⁻¹ * (S' - S)).trace) :=
  CovGap.main ρ ρ' μ S S' ν hν hS hord h h'
