-- Prove2me | solution 1 for BosonicLearn.cov_perturbation_classical
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T22:03:42.831334+00:00
-- url     : https://prove2.me/submissions/51927988-d6b2-4c4a-9338-a38dd795010b

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_displacementMatrix_prod_mul
import Theorems.Thm_BosonicLearn_displacementMatrix_unitary
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
import Theorems.Thm_BosonicLearn_gaussianAt_of_characteristic
import Theorems.Thm_BosonicLearn_vacuum_isGaussianState
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_BosonicLearn_traceDist_le_one

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

open BosonicLearn

/-!
# One-sided covariance perturbation for classical covariances

`½‖ρ(μ, S') − ρ(μ, S)‖₁ ≤ 2 Tr[S⁻¹(S' − S)]` for `S ⪰ ½·1`, `S' ⪰ S`.

Notation (interleaved coordinates): `T = S − ½·1`, `Δ = S' − S`, `R = √T`, and for a vector `x`:
`h_x = R S⁻¹ x`, `b_x = ½ S⁻¹ x` (so `R h_x + b_x = x`), `t_x = ‖b_x‖²/2`.

* **Part A** (copied from the verified solution of `gaussianState_classical_family`): displacement
  operators on `ℓ²`, mixtures of displaced nuclear densities, and `ρ(μ, S) = ∫ |y⟩⟨y| dN(μ, T)(y)`.
* **Part B**: `PT X M` (positive finite quadratic forms, trace `M`); two such arrays with the same
  trace are at trace distance `≤ 2M` (`isDensity_of_posSemidef` and `traceDist_le_one`); the array
  `∫ |F ω⟩⟨F ω| dP` of a measurable field of vectors is `PT` with trace `∫ ‖F‖²`.
* **Part C**: Gaussian integrals; the Cameron–Martin change of variables
  `∫ g dN(m, T + Δ) = ∫∫ w(x, z) g(m + R z + b_x) dγ(z) dN(0, Δ)(x)`,
  `w(x, z) = exp(⟪h_x, z⟫ − ‖h_x‖²/2)`; symmetry and second moments of `N(0, Δ)`.
* **Part D**: the displaced vacuum `A₀ = D_y e₀`, the displaced coherent vectors `A± = D_y D_{±b} e₀`
  with their Gram matrix, `U = (A₊ + A₋)/2`, `V = (A₊ − A₋)/2` and norms of `α A₀ + β U + γ V`.
* **Part S**: scalar inequalities: the total weight of the six rank-one fields is at most
  `5 e^{-s²/2}(cosh g − 1) + (1 − e^{-s²/2}) + 3 t e^{-s²/2} cosh g`.
* **Part F1**: after symmetrizing in `x ↦ −x` the integrand
  `½ w₊ |A₊⟩⟨A₊| + ½ w₋ |A₋⟩⟨A₋| − |A₀⟩⟨A₀|` is a signed sum of six rank-one fields; equality of
  the positive and negative masses follows from `Tr ρ' = Tr ρ`, so Part B applies.
* **Parts E, F2, F3**: matrix algebra (`‖h_x‖² + 4 t_x = xᵀS⁻¹x`), the integral of the dominating
  function (`≤ ∫ (3‖h_x‖² + 3 t_x) dN(0, Δ) ≤ 4 Tr[S⁻¹Δ]`) and the assembly.
-/

namespace CovPert

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

/-! ### The vacuum -/

/-- The nuclear expansion of the vacuum projection: one term `|0⟩⟨0|`. -/
private def vl (n : ℕ) (k : ℕ) : Hilbert (Fin n → ℕ) := if k = 0 then bv 0 else 0

private lemma vl_summable (n : ℕ) : Summable (fun k => ‖vl n k‖ * ‖vl n k‖) := by
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have hk' : k ≠ 0 := by simpa using hk
  simp [vl, hk']

/-- The vacuum projection `|0⟩⟨0|`. -/
private def vacOp (n : ℕ) : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ) := nucOp (vl n) (vl n)

private lemma vacOp_isNuc (n : ℕ) : IsNuc (vacOp n) (vl n) (vl n) :=
  nucOp_isNuc _ _ (vl_summable n)

/-- The entries of the coherent state `D(z_δ)|0⟩⟨0|D(z_δ)⁻¹`. -/
private lemma vac_entry {n : ℕ} (δ : Fin n × Fin 2 → ℝ) (u v : Fin n → ℕ) :
    matOf (cj (vacOp n) δ) u v = Kd (zOf δ) u 0 * star (Kd (zOf δ) v 0) := by
  have h := isNuc_entry (cj_isNuc (vacOp_isNuc n) δ) u v
  have h2 : HasSum (fun k => (Deq (zOf δ) (vl n k)) u * star ((Deq (zOf δ) (vl n k)) v))
      ((Deq (zOf δ) (vl n 0)) u * star ((Deq (zOf δ) (vl n 0)) v)) := by
    refine hasSum_single 0 fun k hk => ?_
    simp [vl, hk]
  rw [h.unique h2]
  simp only [vl, ↓reduceIte, Deq_apply, Dop_bv, colV_apply]

private lemma vac_mat {n : ℕ} (u v : Fin n → ℕ) :
    matOf (vacOp n) u v = if u = 0 ∧ v = 0 then 1 else 0 := by
  have h := isNuc_entry (vacOp_isNuc n) u v
  have h2 : HasSum (fun k => vl n k u * star (vl n k v)) (vl n 0 u * star (vl n 0 v)) := by
    refine hasSum_single 0 fun k hk => ?_
    simp [vl, hk]
  rw [h.unique h2]
  simp only [vl, ↓reduceIte]
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · subst hu hv
      simp [bv_apply_self]
    · subst hu
      simp [hv, bv_apply_ne hv]
  · simp [hu, bv_apply_ne hu]

/-- The interleaved-to-grouped reindexing of quadratures used by `IsGaussianState`. -/
private def qe {n : ℕ} (a : Fin n × Fin 2) : Fin n ⊕ Fin n :=
  if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1

private lemma vac_exists (n : ℕ) : ∃ ρ : State (Occupation (Fin n)),
    ρ.coefficients = matOf (vacOp n) ∧
    IsGaussianState ρ 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) := by
  obtain ⟨ρ, hρ, hG⟩ := vacuum_isGaussianState n
  refine ⟨ρ, ?_, hG⟩
  funext u v
  rw [hρ, vac_mat]

/-- The vacuum state. -/
private def vacState (n : ℕ) : State (Occupation (Fin n)) := Classical.choose (vac_exists n)

private lemma vacState_coeff (n : ℕ) : (vacState n).coefficients = matOf (vacOp n) :=
  (Classical.choose_spec (vac_exists n)).1

private lemma vacState_gaussian (n : ℕ) :
    IsGaussianState (vacState n) 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) :=
  (Classical.choose_spec (vac_exists n)).2

private lemma vac_density (n : ℕ) : IsDensity (matOf (vacOp n)) :=
  vacState_coeff n ▸ (vacState n).density

private lemma vac_char (n : ℕ) (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (matOf (vacOp n)) ξ =
      Complex.exp (((-varianceForm (fun a b => 2 * ((1 / 2 : ℝ) •
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) (qe a) (qe b)) ξ / 4 : ℝ) : ℂ) +
        Complex.I * (meanForm (fun a => (0 : Fin n ⊕ Fin n → ℝ) (qe a)) ξ : ℂ)) := by
  have h : GaussianAt (vacState n).coefficients (fun a => (0 : Fin n ⊕ Fin n → ℝ) (qe a))
      (fun a b => 2 * ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        (qe a) (qe b)) := vacState_gaussian n
  rw [← vacState_coeff]
  exact h.2 ξ

/-! ### The Gaussian mixture of coherent states -/

/-- The mixture `∫ D(x)|0⟩⟨0|D(x)⁻¹ dN(m, T)(x)` of coherent states. -/
private def mixArr {n : ℕ} (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ :=
  fun u v => ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2), matOf (cj (vacOp n) (fun a => ω a)) u v
    ∂(ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T)

private lemma mixArr_density {n : ℕ} (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : IsDensity (mixArr m T) :=
  (mix_explicit (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T)
    (fun ω a => ω a) (fun a => by fun_prop) (vacOp_isNuc n) (vac_density n)).1

private lemma mixArr_char {n : ℕ} (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hT : T.PosSemidef) (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (mixArr m T) ξ =
      Complex.exp (Complex.I * (meanForm m ξ : ℂ) - ((varianceForm T ξ / 2 : ℝ) : ℂ)) *
        oscillatorCharacteristic (matOf (vacOp n)) ξ := by
  have h := (mix_explicit (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 m) T)
    (fun ω a => ω a) (fun a => by fun_prop) (vacOp_isNuc n) (vac_density n)).2 ξ
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

/-- For `S ⪰ ½·1` the mixture with `T = S - ½·1` is the Gaussian state `ρ(μ, S)`. -/
private lemma mix_gaussian {n : ℕ} (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef) :
    IsGaussianState ⟨mixArr (fun a => μ (qe a))
      ((S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix qe qe),
      mixArr_density _ _⟩ μ S := by
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
  · show oscillatorCharacteristic (mixArr _ _) ξ = _
    rw [mixArr_char _ _ (hS.submatrix qe) ξ, vac_char, ← Complex.exp_add]
    congr 1
    have hv : varianceForm (fun a b => 2 * S (qe a) (qe b)) ξ =
        2 * varianceForm ((S - (1 / 2 : ℝ) •
          (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix qe qe) ξ +
        varianceForm (fun a b => 2 * ((1 / 2 : ℝ) •
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


end

end PartA

section PartB

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal Matrix
open BosonicLearn

noncomputable section

/-! ### Trace-norm bounds for differences of positive arrays of equal trace -/

/-- `PT X M`: the finite quadratic forms of `X` are real and non-negative and the diagonal of `X`
sums to `M`. -/
private def PT {I : Type} (X : Matrix I I ℂ) (M : ℝ) : Prop :=
  (∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re) ∧
  HasSum (fun i => (X i i).re) M

private lemma PT_add {I : Type} {X Y : Matrix I I ℂ} {M M' : ℝ} (hX : PT X M) (hY : PT Y M') :
    PT (X + Y) (M + M') := by
  refine ⟨fun s z => ?_, ?_⟩
  · have h : ∑ i ∈ s, ∑ j ∈ s, star (z i) * (X + Y) i j * z j =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j +
          ∑ i ∈ s, ∑ j ∈ s, star (z i) * Y i j * z j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.add_apply]
      ring
    rw [h, Complex.add_im, Complex.add_re]
    exact ⟨by rw [(hX.1 s z).1, (hY.1 s z).1, add_zero], add_nonneg (hX.1 s z).2 (hY.1 s z).2⟩
  · have h := hX.2.add hY.2
    refine h.congr_fun fun i => ?_
    rw [Matrix.add_apply, Complex.add_re]

private lemma PT_smul {I : Type} {X : Matrix I I ℂ} {M : ℝ} (c : ℝ) (hc : 0 ≤ c) (hX : PT X M) :
    PT ((c : ℂ) • X) (c * M) := by
  refine ⟨fun s z => ?_, ?_⟩
  · have h : ∑ i ∈ s, ∑ j ∈ s, star (z i) * ((c : ℂ) • X) i j * z j =
        (c : ℂ) * ∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hX.1 s z).1, mul_zero]
    exact ⟨rfl, mul_nonneg hc (hX.1 s z).2⟩
  · have h := hX.2.mul_left c
    refine h.congr_fun fun i => ?_
    rw [Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]

private lemma PT_of_density {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) : PT X 1 := by
  refine ⟨hX.2.1, ?_⟩
  have h := hX.2.2.1.hasSum
  rwa [hX.2.2.2] at h

private lemma PT_density {I : Type} [Countable I] {X : Matrix I I ℂ} (hX : PT X 1) : IsDensity X :=
  isDensity_of_posSemidef X hX.1 hX.2.summable hX.2.tsum_eq

private lemma traceSize_smul_le {I : Type} (c : ℝ) (hc : 0 ≤ c) (X : Matrix I I ℂ) :
    traceSize ((c : ℂ) • X) ≤ ENNReal.ofReal c * traceSize X := by
  have key : ∀ e : NuclearExpansion X, traceSize ((c : ℂ) • X) ≤
      ENNReal.ofReal c * ENNReal.ofReal (∑' k, ‖e.left k‖ * ‖e.right k‖) := by
    intro e
    let e' : NuclearExpansion ((c : ℂ) • X) :=
      { left := fun k => (c : ℂ) • e.left k
        right := e.right
        summable := by
          have h := e.summable.mul_left c
          refine h.congr fun k => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, mul_assoc]
        coefficients := by
          intro i j
          rw [Matrix.smul_apply, smul_eq_mul, e.coefficients i j, ← tsum_mul_left]
          refine tsum_congr fun k => ?_
          simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
          ring }
    refine (iInf_le _ e').trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    show ∑' k, ‖(c : ℂ) • e.left k‖ * ‖e.right k‖ = c * ∑' k, ‖e.left k‖ * ‖e.right k‖
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, mul_assoc]
  rcases hc.eq_or_lt with h0 | hpos
  · subst h0
    let e0 : NuclearExpansion (((0 : ℝ) : ℂ) • X) :=
      { left := fun _ => 0
        right := fun _ => 0
        summable := by simp
        coefficients := by
          intro i j
          simp }
    have h1 : traceSize (((0 : ℝ) : ℂ) • X) ≤ 0 := by
      refine (iInf_le _ e0).trans (le_of_eq ?_)
      simp [e0]
    simpa using h1
  · show traceSize ((c : ℂ) • X) ≤ ENNReal.ofReal c *
      ⨅ e : NuclearExpansion X, ENNReal.ofReal (∑' k, ‖e.left k‖ * ‖e.right k‖)
    rw [ENNReal.mul_iInf_of_ne (by simpa using hpos) ENNReal.ofReal_ne_top]
    exact le_iInf key

/-- Two positive arrays with the same trace `M` are at trace distance at most `2M`. -/
private theorem PT_diff_bound {I : Type} [Countable I] (D : Matrix I I ℂ) (hD : IsDensity D)
    {X Y : Matrix I I ℂ} {M : ℝ} (hM : 0 ≤ M) (hX : PT X M) (hY : PT Y M) :
    traceSize (X - Y) ≤ ENNReal.ofReal (2 * M) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  set c : ℝ := M + (ε : ℝ) / 2 with hc
  have hcpos : 0 < c := by positivity
  have hDPT : PT D 1 := PT_of_density hD
  have hmk : ∀ {Z : Matrix I I ℂ}, PT Z M →
      PT (((c⁻¹ : ℝ) : ℂ) • (Z + (((ε : ℝ) / 2 : ℝ) : ℂ) • D)) 1 := by
    intro Z hZ
    have h := PT_smul c⁻¹ (inv_nonneg.2 hcpos.le)
      (PT_add hZ (PT_smul ((ε : ℝ) / 2) (by positivity) hDPT))
    have h1 : c⁻¹ * (M + (ε : ℝ) / 2 * 1) = 1 := by
      rw [mul_one, ← hc]
      exact inv_mul_cancel₀ hcpos.ne'
    rwa [h1] at h
  have hdX := PT_density (hmk hX)
  have hdY := PT_density (hmk hY)
  have h1 := traceDist_le_one ⟨_, hdX⟩ ⟨_, hdY⟩
  have h2 : traceSize (((c⁻¹ : ℝ) : ℂ) • (X + (((ε : ℝ) / 2 : ℝ) : ℂ) • D) -
      ((c⁻¹ : ℝ) : ℂ) • (Y + (((ε : ℝ) / 2 : ℝ) : ℂ) • D)) ≤ 2 := by
    unfold traceDist at h1
    have h3 := mul_le_mul_left h1 (2 : ℝ≥0∞)
    rwa [ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul] at h3
  have h3 : X - Y = (c : ℂ) • (((c⁻¹ : ℝ) : ℂ) • (X + (((ε : ℝ) / 2 : ℝ) : ℂ) • D) -
      ((c⁻¹ : ℝ) : ℂ) • (Y + (((ε : ℝ) / 2 : ℝ) : ℂ) • D)) := by
    rw [← smul_sub, smul_smul]
    have h4 : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hcpos.ne', Complex.ofReal_one]
    rw [h4, one_smul]
    abel
  rw [h3]
  calc traceSize ((c : ℂ) • (((c⁻¹ : ℝ) : ℂ) • (X + (((ε : ℝ) / 2 : ℝ) : ℂ) • D) -
        ((c⁻¹ : ℝ) : ℂ) • (Y + (((ε : ℝ) / 2 : ℝ) : ℂ) • D)))
      ≤ ENNReal.ofReal c * traceSize (((c⁻¹ : ℝ) : ℂ) • (X + (((ε : ℝ) / 2 : ℝ) : ℂ) • D) -
        ((c⁻¹ : ℝ) : ℂ) • (Y + (((ε : ℝ) / 2 : ℝ) : ℂ) • D)) := traceSize_smul_le c hcpos.le _
    _ ≤ ENNReal.ofReal c * 2 := by gcongr
    _ = ENNReal.ofReal (2 * M) + ε := by
        have h5 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h5, ← ENNReal.ofReal_mul hcpos.le, ← ENNReal.ofReal_coe_nnreal (p := ε),
          ← ENNReal.ofReal_add (by positivity) ε.coe_nonneg]
        congr 1
        rw [hc]
        ring

/-! ### Arrays obtained by integrating rank-one projections -/

/-- The array `∫ |F ω⟩⟨F ω| dP(ω)`. -/
private def rk {Ω I : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → Hilbert I) : Matrix I I ℂ :=
  fun u v => ∫ ω, F ω u * star (F ω v) ∂P

private lemma hasSum_norm_sq {I : Type} (x : Hilbert I) : HasSum (fun u => ‖x u‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa using h

private lemma norm_sq_measurable {Ω I : Type} [MeasurableSpace Ω] [Countable I] (F : Ω → Hilbert I)
    (hF : ∀ u, Measurable (fun ω => F ω u)) : Measurable (fun ω => ‖F ω‖ ^ 2) := by
  refine measurable_of_tendsto_metrizable' Filter.atTop
    (f := fun (s : Finset I) ω => ∑ u ∈ s, ‖F ω u‖ ^ 2)
    (fun s => Finset.measurable_sum s fun u _ => (hF u).norm.pow_const 2) ?_
  exact tendsto_pi_nhds.mpr fun ω => hasSum_norm_sq (F ω)

private lemma rk_entry_integrable {Ω I : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → Hilbert I)
    (hF : ∀ u, Measurable (fun ω => F ω u)) (hint : Integrable (fun ω => ‖F ω‖ ^ 2) P) (u v : I) :
    Integrable (fun ω => F ω u * star (F ω v)) P := by
  refine Integrable.mono' hint
    ((hF u).mul (continuous_star.measurable.comp (hF v))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul, norm_star, sq]
  exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) _ _)
    (lp.norm_apply_le_norm (by norm_num) _ _) (norm_nonneg _) (norm_nonneg _)

private lemma rk_PT {Ω I : Type} [MeasurableSpace Ω] [Countable I] (P : Measure Ω) (F : Ω → Hilbert I)
    (hF : ∀ u, Measurable (fun ω => F ω u)) (hint : Integrable (fun ω => ‖F ω‖ ^ 2) P) :
    PT (rk P F) (∫ ω, ‖F ω‖ ^ 2 ∂P) := by
  have hei := rk_entry_integrable P F hF hint
  refine ⟨fun s z => ?_, ?_⟩
  · have hQint : Integrable (fun ω => ∑ i ∈ s, ∑ j ∈ s,
        star (z i) * (F ω i * star (F ω j)) * z j) P :=
      integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
        ((hei i j).const_mul _).mul_const _
    have hQ : ∑ i ∈ s, ∑ j ∈ s, star (z i) * rk P F i j * z j =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, star (z i) * (F ω i * star (F ω j)) * z j ∂P := by
      rw [integral_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
        ((hei i j).const_mul _).mul_const _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum s fun j _ => ((hei i j).const_mul _).mul_const _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const, integral_const_mul]
      rfl
    have hpt : ∀ ω, ∑ i ∈ s, ∑ j ∈ s, star (z i) * (F ω i * star (F ω j)) * z j =
        ((‖∑ i ∈ s, star (z i) * F ω i‖ ^ 2 : ℝ) : ℂ) := by
      intro ω
      have h1 : ((‖∑ i ∈ s, star (z i) * F ω i‖ ^ 2 : ℝ) : ℂ) =
          (∑ i ∈ s, star (z i) * F ω i) * star (∑ j ∈ s, star (z j) * F ω j) := by
        rw [Complex.star_def, Complex.mul_conj']
        push_cast
        rfl
      rw [h1, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul', star_star]
      ring
    rw [hQ, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
    exact ⟨Complex.ofReal_im _, by
      rw [Complex.ofReal_re]
      exact integral_nonneg fun ω => by positivity⟩
  · have hd : ∀ u, (rk P F u u).re = ∫ ω, ‖F ω u‖ ^ 2 ∂P := by
      intro u
      have h1 : ∀ ω, F ω u * star (F ω u) = ((‖F ω u‖ ^ 2 : ℝ) : ℂ) := by
        intro ω
        rw [Complex.star_def, Complex.mul_conj']
        push_cast
        rfl
      show (∫ ω, F ω u * star (F ω u) ∂P).re = _
      rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_complex_ofReal, Complex.ofReal_re]
    have hint_u : ∀ u, Integrable (fun ω => ‖F ω u‖ ^ 2) P := by
      intro u
      refine Integrable.mono' hint ((hF u).norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm (by norm_num) _ _) 2
    have hsum : Summable (fun u => ∫ ω, ‖(‖F ω u‖ ^ 2 : ℝ)‖ ∂P) := by
      refine summable_of_sum_le (c := ∫ ω, ‖F ω‖ ^ 2 ∂P)
        (fun u => integral_nonneg fun ω => norm_nonneg _) fun s => ?_
      rw [← integral_finsetSum s fun u _ => (hint_u u).norm]
      refine integral_mono (integrable_finsetSum s fun u _ => (hint_u u).norm) hint fun ω => ?_
      have h2 := (hasSum_norm_sq (F ω)).summable.sum_le_tsum s (fun u _ => by positivity)
      rw [(hasSum_norm_sq (F ω)).tsum_eq] at h2
      refine le_trans (le_of_eq ?_) h2
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 := hasSum_integral_of_summable_integral_norm hint_u hsum
    have h4 : (fun ω => ∑' u, ‖F ω u‖ ^ 2) = fun ω => ‖F ω‖ ^ 2 := by
      funext ω
      exact (hasSum_norm_sq (F ω)).tsum_eq
    rw [h4] at h3
    exact h3.congr_fun fun u => hd u

end

end PartB

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

/-! ### Symmetry and second moments of centred Gaussians -/

private lemma gauss_neg {ι : Type} [Fintype ι] [DecidableEq ι] (Δ : Matrix ι ι ℝ) (hΔ : Δ.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ).map (fun x => -x) =
      multivariateGaussian 0 Δ := by
  have hfin : IsFiniteMeasure ((multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ).map
      (fun x => -x)) := Measure.isFiniteMeasure_map _ _
  refine Measure.ext_of_charFun ?_
  funext ξ
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ x : EuclideanSpace ℝ ι, Complex.exp ((inner ℝ (-x) ξ : ℝ) * Complex.I) =
      Complex.exp ((inner ℝ x (-ξ) : ℝ) * Complex.I) := by
    intro x
    rw [inner_neg_left, inner_neg_right]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), ← charFun_apply,
    charFun_multivariateGaussian hΔ, charFun_multivariateGaussian hΔ]
  congr 1
  simp [Matrix.mulVec_neg]

private lemma gauss_second_moment {ι : Type} [Fintype ι] [DecidableEq ι] (Δ : Matrix ι ι ℝ)
    (hΔ : Δ.PosSemidef) (a b : ι) :
    Integrable (fun x : EuclideanSpace ℝ ι => x a * x b) (multivariateGaussian 0 Δ) ∧
    ∫ x : EuclideanSpace ℝ ι, x a * x b ∂(multivariateGaussian 0 Δ) = Δ a b := by
  have hmp : ∀ i : ι, MeasurePreserving (fun x : EuclideanSpace ℝ ι => x i)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ) (gaussianReal 0 (Δ i i).toNNReal) :=
    fun i => measurePreserving_eval_multivariateGaussian hΔ
  have hL2 : ∀ i : ι, MemLp (fun x : EuclideanSpace ℝ ι => x i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ) := by
    intro i
    have h1 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 (Δ i i).toNNReal) := memLp_id_gaussianReal 2
    exact h1.comp_measurePreserving (hmp i)
  have hmean : ∀ i : ι, ∫ x : EuclideanSpace ℝ ι, x i ∂(multivariateGaussian 0 Δ) = 0 := by
    intro i
    have h1 : ∫ y : ℝ, y ∂(gaussianReal 0 (Δ i i).toNNReal) = 0 := integral_id_gaussianReal
    rw [← (hmp i).map_eq, integral_map (hmp i).measurable.aemeasurable (by fun_prop)] at h1
    exact h1
  refine ⟨(hL2 a).integrable_mul (hL2 b), ?_⟩
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hΔ a b
  rw [covariance, hmean a, hmean b] at hc
  simpa using hc

private lemma gauss_quad {ι : Type} [Fintype ι] [DecidableEq ι] (Δ : Matrix ι ι ℝ) (hΔ : Δ.PosSemidef)
    (L : Matrix ι ι ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => x.ofLp ⬝ᵥ L *ᵥ x.ofLp) (multivariateGaussian 0 Δ) ∧
    ∫ x : EuclideanSpace ℝ ι, x.ofLp ⬝ᵥ L *ᵥ x.ofLp ∂(multivariateGaussian 0 Δ) =
      (L * Δ).trace := by
  have e : (fun x : EuclideanSpace ℝ ι => x.ofLp ⬝ᵥ L *ᵥ x.ofLp) =
      fun x => ∑ a, ∑ b, L a b * (x a * x b) := by
    funext x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hi : ∀ a b : ι, Integrable (fun x : EuclideanSpace ℝ ι => L a b * (x a * x b))
      (multivariateGaussian 0 Δ) := fun a b => (gauss_second_moment Δ hΔ a b).1.const_mul _
  rw [e]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, (gauss_second_moment Δ hΔ a b).2]
  have hsym : Δ b a = Δ a b := by
    have := hΔ.isHermitian.apply a b
    simpa using this
  rw [hsym]

end

end PartC

section PartD

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

/-! ### Coherent vectors and their even/odd combinations -/

/-- The vacuum expectation of a displacement. -/
private lemma Kd_zero_zero {n : ℕ} (z : Fin n → ℂ) :
    Kd z 0 0 = ((Real.exp (-(∑ j, Complex.normSq (z j)) / 2) : ℝ) : ℂ) := by
  unfold Kd
  have h : ∀ j, displacementMatrix (z j) ((0 : Fin n → ℕ) j) ((0 : Fin n → ℕ) j) =
      ((Real.exp (-Complex.normSq (z j) / 2) : ℝ) : ℂ) := by
    intro j
    simp [displacementMatrix]
  rw [Finset.prod_congr rfl fun j _ => h j, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `t = ∑ⱼ |αⱼ|²` for the amplitude `α = zOf b`. -/
private def tpar {n : ℕ} (b : Fin n × Fin 2 → ℝ) : ℝ := ∑ j, Complex.normSq (zOf b j)

private lemma tpar_eq {n : ℕ} (b : Fin n × Fin 2 → ℝ) : tpar b = (∑ a, b a ^ 2) / 2 := by
  unfold tpar
  rw [Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : zOf b j = (((b (j, 0) / Real.sqrt 2 : ℝ) : ℂ) +
      ((b (j, 1) / Real.sqrt 2 : ℝ) : ℂ) * Complex.I) := by
    unfold zOf
    push_cast
    ring
  rw [h3, Complex.normSq_add_mul_I, div_pow, div_pow, h2]
  ring

private lemma tpar_nonneg {n : ℕ} (b : Fin n × Fin 2 → ℝ) : 0 ≤ tpar b :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private lemma zOf_add {n : ℕ} (a b : Fin n × Fin 2 → ℝ) : zOf (a + b) = zOf a + zOf b := by
  funext j
  simp only [zOf, Pi.add_apply]
  push_cast
  ring

private lemma zOf_neg {n : ℕ} (b : Fin n × Fin 2 → ℝ) : zOf (-b) = -zOf b := by
  funext j
  simp only [zOf, Pi.neg_apply]
  push_cast
  ring

private lemma zOf_zero {n : ℕ} : zOf (0 : Fin n × Fin 2 → ℝ) = 0 := by
  funext j
  simp [zOf]

private lemma tpar_neg {n : ℕ} (b : Fin n × Fin 2 → ℝ) : tpar (-b) = tpar b := by
  rw [tpar_eq, tpar_eq]
  simp

private lemma eq_zero_of_tpar {n : ℕ} (b : Fin n × Fin 2 → ℝ) (h : tpar b = 0) : b = 0 := by
  rw [tpar_eq] at h
  have h1 : ∑ a, b a ^ 2 = 0 := by linarith
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => sq_nonneg (b a)).1 h1
  funext a
  have := h2 a (Finset.mem_univ a)
  simpa using this

private lemma ph_self {n : ℕ} (a : Fin n → ℂ) : ph a a = 1 := by
  unfold ph
  refine Finset.prod_eq_one fun j _ => ?_
  have h : (a j * star (a j) - star (a j) * a j) / 2 = 0 := by ring
  rw [h, Complex.exp_zero]

private lemma ph_mul_star {n : ℕ} (a b : Fin n → ℂ) : ph a b * star (ph a b) = 1 := by
  unfold ph
  rw [star_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  simp only [map_div₀, map_sub, map_mul, Complex.conj_conj]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofNat 2
  rw [h2]
  ring

/-- The displaced vacuum (coherent vector of `y`). -/
private def A0 {n : ℕ} (y : Fin n × Fin 2 → ℝ) : Hilbert (Fin n → ℕ) := Dop (zOf y) (bv 0)

/-- The coherent vector of `b`, displaced by `y` (with its Weyl phase). -/
private def Ap {n : ℕ} (y b : Fin n × Fin 2 → ℝ) : Hilbert (Fin n → ℕ) :=
  Dop (zOf y) (Dop (zOf b) (bv 0))

private lemma A0_apply {n : ℕ} (y : Fin n × Fin 2 → ℝ) (u : Fin n → ℕ) : A0 y u = Kd (zOf y) u 0 := by
  unfold A0
  rw [Dop_bv, colV_apply]

private lemma Ap_apply {n : ℕ} (y b : Fin n × Fin 2 → ℝ) (u : Fin n → ℕ) :
    Ap y b u = ph (zOf y) (zOf b) * Kd (zOf (y + b)) u 0 := by
  unfold Ap
  rw [Dop_mul, zOf_add, Dop_bv]
  rfl

private lemma Ap_zero {n : ℕ} (y : Fin n × Fin 2 → ℝ) : Ap y 0 = A0 y := by
  unfold Ap A0
  rw [zOf_zero, Dop_zero]

private lemma A0_entry {n : ℕ} (y : Fin n × Fin 2 → ℝ) (u v : Fin n → ℕ) :
    A0 y u * star (A0 y v) = matOf (cj (vacOp n) y) u v := by
  rw [vac_entry, A0_apply, A0_apply]

private lemma Ap_entry {n : ℕ} (y b : Fin n × Fin 2 → ℝ) (u v : Fin n → ℕ) :
    Ap y b u * star (Ap y b v) = matOf (cj (vacOp n) (y + b)) u v := by
  rw [vac_entry, Ap_apply, Ap_apply, star_mul']
  have h := ph_mul_star (zOf y) (zOf b)
  linear_combination (Kd (zOf (y + b)) u 0 * star (Kd (zOf (y + b)) v 0)) * h

private lemma norm_A0 {n : ℕ} (y : Fin n × Fin 2 → ℝ) : ‖A0 y‖ = 1 := by
  unfold A0
  rw [LinearIsometry.norm_map, norm_bv]

private lemma norm_Ap {n : ℕ} (y b : Fin n × Fin 2 → ℝ) : ‖Ap y b‖ = 1 := by
  unfold Ap
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map, norm_bv]

private lemma inner_A0_Ap {n : ℕ} (y b : Fin n × Fin 2 → ℝ) :
    inner ℂ (A0 y) (Ap y b) = ((Real.exp (-tpar b / 2) : ℝ) : ℂ) := by
  unfold A0 Ap
  rw [LinearIsometry.inner_map_map, inner_bv_left, Dop_bv, colV_apply, Kd_zero_zero]
  rfl

private lemma inner_Ap_Ap_neg {n : ℕ} (y b : Fin n × Fin 2 → ℝ) :
    inner ℂ (Ap y b) (Ap y (-b)) = ((Real.exp (-(2 * tpar b)) : ℝ) : ℂ) := by
  unfold Ap
  rw [LinearIsometry.inner_map_map, ← Deq_apply (zOf b), LinearIsometryEquiv.inner_map_eq_flip,
    Deq_symm_apply, zOf_neg, Dop_mul, ph_self, one_smul, inner_bv_left, Dop_bv, colV_apply,
    Kd_zero_zero]
  congr 2
  unfold tpar
  rw [neg_div, Finset.mul_sum, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (-zOf b + -zOf b) j = (-2 : ℂ) * zOf b j := by
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rw [h, Complex.normSq_mul]
  have h2 : Complex.normSq (-2 : ℂ) = 4 := by
    rw [Complex.normSq_neg]
    norm_num [Complex.normSq_apply]
  rw [h2]
  ring

/-- The even part of the displaced coherent vector. -/
private def Uv {n : ℕ} (y b : Fin n × Fin 2 → ℝ) : Hilbert (Fin n → ℕ) :=
  (1 / 2 : ℂ) • (Ap y b + Ap y (-b))

/-- The odd part of the displaced coherent vector. -/
private def Vv {n : ℕ} (y b : Fin n × Fin 2 → ℝ) : Hilbert (Fin n → ℕ) :=
  (1 / 2 : ℂ) • (Ap y b - Ap y (-b))

/-- A real combination of the displaced vacuum and of the even and odd parts. -/
private def fld {n : ℕ} (y b : Fin n × Fin 2 → ℝ) (α β γ : ℝ) : Hilbert (Fin n → ℕ) :=
  (α : ℂ) • A0 y + (β : ℂ) • Uv y b + (γ : ℂ) • Vv y b

private lemma fld_apply {n : ℕ} (y b : Fin n × Fin 2 → ℝ) (α β γ : ℝ) (u : Fin n → ℕ) :
    fld y b α β γ u = (α : ℂ) * A0 y u + (β : ℂ) * ((Ap y b u + Ap y (-b) u) / 2) +
      (γ : ℂ) * ((Ap y b u - Ap y (-b) u) / 2) := by
  unfold fld Uv Vv
  simp only [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  ring

private lemma fld_norm_sq {n : ℕ} (y b : Fin n × Fin 2 → ℝ) (α β γ : ℝ) :
    ‖fld y b α β γ‖ ^ 2 = α ^ 2 + β ^ 2 * ((1 + Real.exp (-(2 * tpar b))) / 2) +
      γ ^ 2 * ((1 - Real.exp (-(2 * tpar b))) / 2) + 2 * α * β * Real.exp (-tpar b / 2) := by
  have h00 : inner ℂ (A0 y) (A0 y) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, norm_A0]
    norm_num
  have hpp : ∀ c : Fin n × Fin 2 → ℝ, inner ℂ (Ap y c) (Ap y c) = (1 : ℂ) := by
    intro c
    rw [inner_self_eq_norm_sq_to_K, norm_Ap]
    norm_num
  have h0p := inner_A0_Ap y b
  have h0m := inner_A0_Ap y (-b)
  rw [tpar_neg] at h0m
  have hp0 : inner ℂ (Ap y b) (A0 y) = ((Real.exp (-tpar b / 2) : ℝ) : ℂ) := by
    rw [← inner_conj_symm, h0p, Complex.conj_ofReal]
  have hm0 : inner ℂ (Ap y (-b)) (A0 y) = ((Real.exp (-tpar b / 2) : ℝ) : ℂ) := by
    rw [← inner_conj_symm, h0m, Complex.conj_ofReal]
  have hpm := inner_Ap_Ap_neg y b
  have hmp : inner ℂ (Ap y (-b)) (Ap y b) = ((Real.exp (-(2 * tpar b)) : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hpm, Complex.conj_ofReal]
  have key : inner ℂ (fld y b α β γ) (fld y b α β γ) =
      ((α ^ 2 + β ^ 2 * ((1 + Real.exp (-(2 * tpar b))) / 2) +
        γ ^ 2 * ((1 - Real.exp (-(2 * tpar b))) / 2) +
        2 * α * β * Real.exp (-tpar b / 2) : ℝ) : ℂ) := by
    unfold fld Uv Vv
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, h00, hpp, h0p, h0m, hp0, hm0, hpm, hmp, Complex.conj_ofReal, map_div₀,
      map_one, Complex.conj_ofNat]
    push_cast
    ring
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (fld y b α β γ)
  rw [key] at h2
  exact Complex.ofReal_injective (by rw [h2, Complex.ofReal_pow]; rfl)

/-! ### Measurability -/

private lemma ph_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (Y B : Ω → Fin n × Fin 2 → ℝ)
    (hY : ∀ a, Measurable (fun ω => Y ω a)) (hB : ∀ a, Measurable (fun ω => B ω a)) :
    Measurable (fun ω => ph (zOf (Y ω)) (zOf (B ω))) := by
  unfold ph
  refine Finset.measurable_prod _ fun j _ => ?_
  unfold zOf
  have h0 := hY (j, 0)
  have h1 := hY (j, 1)
  have h2 := hB (j, 0)
  have h3 := hB (j, 1)
  have hs : Measurable (fun z : ℂ => star z) := continuous_star.measurable
  fun_prop

private lemma Ap_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (Y B : Ω → Fin n × Fin 2 → ℝ)
    (hY : ∀ a, Measurable (fun ω => Y ω a)) (hB : ∀ a, Measurable (fun ω => B ω a))
    (u : Fin n → ℕ) : Measurable (fun ω => Ap (Y ω) (B ω) u) := by
  simp only [Ap_apply]
  refine (ph_measurable Y B hY hB).mul ?_
  exact Kd_measurable (fun ω => Y ω + B ω) (fun a => (hY a).add (hB a)) u 0

private lemma A0_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (Y : Ω → Fin n × Fin 2 → ℝ)
    (hY : ∀ a, Measurable (fun ω => Y ω a)) (u : Fin n → ℕ) :
    Measurable (fun ω => A0 (Y ω) u) := by
  simp only [A0_apply]
  exact Kd_measurable Y hY u 0

private lemma fld_measurable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (Y B : Ω → Fin n × Fin 2 → ℝ)
    (hY : ∀ a, Measurable (fun ω => Y ω a)) (hB : ∀ a, Measurable (fun ω => B ω a))
    (α β γ : Ω → ℝ) (hα : Measurable α) (hβ : Measurable β) (hγ : Measurable γ) (u : Fin n → ℕ) :
    Measurable (fun ω => fld (Y ω) (B ω) (α ω) (β ω) (γ ω) u) := by
  simp only [fld_apply]
  have h0 := A0_measurable Y hY u
  have hp := Ap_measurable Y B hY hB u
  have hm := Ap_measurable Y (fun ω => -B ω) hY (fun a => (hB a).neg) u
  have hα' : Measurable (fun ω => ((α ω : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hα
  have hβ' : Measurable (fun ω => ((β ω : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hβ
  have hγ' : Measurable (fun ω => ((γ ω : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hγ
  exact ((hα'.mul h0).add (hβ'.mul ((hp.add hm).div_const 2))).add
    (hγ'.mul ((hp.sub hm).div_const 2))

end

end PartD

section PartS

noncomputable section

/-! ### Scalar inequalities -/

private lemma exp_neg_le_quad (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hy
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-y) := Real.exp_pos _
  have hq : 0 < 1 + y + y ^ 2 / 2 := by positivity
  have h4 : Real.exp (-y) * (1 + y + y ^ 2 / 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h1 h3.le).trans (le_of_eq h2)
  have h5 : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by
    have : (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) = 1 + y ^ 4 / 4 := by ring
    rw [this]
    have : 0 ≤ y ^ 4 / 4 := by positivity
    linarith
  exact le_of_mul_le_mul_right (h4.trans h5) hq

/-- The norm square of `α A₀ + β U + γ V` in terms of `t`. -/
private def Nf (α β γ t : ℝ) : ℝ :=
  α ^ 2 + β ^ 2 * ((1 + Real.exp (-(2 * t))) / 2) + γ ^ 2 * ((1 - Real.exp (-(2 * t))) / 2) +
    2 * α * β * Real.exp (-t / 2)

/-- The symmetrized weight `e^{-s²/2} cosh g`. -/
private def wsf (s2 g : ℝ) : ℝ := Real.exp (-s2 / 2) * Real.cosh g

/-- The antisymmetrized weight `e^{-s²/2} sinh g`. -/
private def waf (s2 g : ℝ) : ℝ := Real.exp (-s2 / 2) * Real.sinh g

private def tauf (g : ℝ) : ℝ := Real.sinh g / Real.cosh g

private def c1f (s2 g : ℝ) : ℝ := Real.sqrt (Real.exp (-s2 / 2) * (Real.cosh g - 1))

private def d1f (s2 : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-s2 / 2))

private def rf (s2 g : ℝ) : ℝ := Real.sqrt (wsf s2 g)

private def lamf (t : ℝ) : ℝ := Real.sqrt (t / 2)

private def muf (t : ℝ) : ℝ := (Real.sqrt (t / 2))⁻¹

/-- The dominating function. -/
private def Bf (s2 g t : ℝ) : ℝ :=
  5 * (Real.exp (-s2 / 2) * (Real.cosh g - 1)) + (1 - Real.exp (-s2 / 2)) +
    3 * t * (Real.exp (-s2 / 2) * Real.cosh g)

private lemma wsf_nonneg (s2 g : ℝ) : 0 ≤ wsf s2 g :=
  mul_nonneg (Real.exp_pos _).le (Real.cosh_pos g).le

private lemma c1f_sq (s2 g : ℝ) : c1f s2 g ^ 2 = wsf s2 g - Real.exp (-s2 / 2) := by
  unfold c1f wsf
  rw [Real.sq_sqrt (mul_nonneg (Real.exp_pos _).le (by linarith [Real.one_le_cosh g]))]
  ring

private lemma d1f_sq (s2 : ℝ) (hs : 0 ≤ s2) : d1f s2 ^ 2 = 1 - Real.exp (-s2 / 2) := by
  unfold d1f
  rw [Real.sq_sqrt]
  have : Real.exp (-s2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

private lemma rf_sq (s2 g : ℝ) : rf s2 g ^ 2 = wsf s2 g := Real.sq_sqrt (wsf_nonneg s2 g)

private lemma wsf_mul_tauf (s2 g : ℝ) : wsf s2 g * tauf g = waf s2 g := by
  unfold wsf tauf waf
  have := (Real.cosh_pos g).ne'
  field_simp

private lemma lamf_mul_muf (t : ℝ) (ht : 0 < t) : lamf t * muf t = 1 := by
  unfold lamf muf
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'

private lemma lamf_zero : lamf 0 = 0 := by simp [lamf]

private lemma muf_zero : muf 0 = 0 := by simp [muf]

private lemma Bf_nonneg (s2 g t : ℝ) (hs : 0 ≤ s2) (ht : 0 ≤ t) : 0 ≤ Bf s2 g t := by
  unfold Bf
  have h1 : Real.exp (-s2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.one_le_cosh g
  have h3 := (Real.exp_pos (-s2 / 2)).le
  have h4 : 0 ≤ Real.exp (-s2 / 2) * (Real.cosh g - 1) := mul_nonneg h3 (by linarith)
  have h5 : 0 ≤ 3 * t * (Real.exp (-s2 / 2) * Real.cosh g) :=
    mul_nonneg (by positivity) (mul_nonneg h3 (by linarith))
  linarith

/-- The total mass of the six fields is dominated by `Bf`. -/
private lemma mass_bound (s2 g t : ℝ) (hs : 0 ≤ s2) (ht : 0 ≤ t) :
    Nf (c1f s2 g) 0 0 t + Nf (rf s2 g * (lamf t - muf t) / 2) (rf s2 g * (lamf t + muf t) / 2) 0 t +
      Nf 0 (rf s2 g * tauf g) (rf s2 g) t +
    (Nf (d1f s2) 0 0 t + Nf (rf s2 g * (lamf t + muf t) / 2) (rf s2 g * (lamf t - muf t) / 2) 0 t +
      Nf 0 (rf s2 g * tauf g) 0 t) ≤ Bf s2 g t := by
  have he0 : Real.exp (-s2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0' := (Real.exp_pos (-s2 / 2)).le
  have hc := Real.one_le_cosh g
  have hws := wsf_nonneg s2 g
  have hk4 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hk4' := (Real.exp_pos (-(2 * t))).le
  have hk4q : Real.exp (-(2 * t)) ≤ 1 - 2 * t + 2 * t ^ 2 := by
    have := exp_neg_le_quad (2 * t) (by positivity)
    nlinarith
  have hk4l : 1 - 2 * t ≤ Real.exp (-(2 * t)) := by
    have := Real.add_one_le_exp (-(2 * t))
    linarith
  have hk : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hkl : 1 - t / 2 ≤ Real.exp (-t / 2) := by
    have := Real.add_one_le_exp (-t / 2)
    linarith
  -- the first pair
  have h1 : Nf (c1f s2 g) 0 0 t = Real.exp (-s2 / 2) * (Real.cosh g - 1) := by
    unfold Nf
    rw [c1f_sq]
    unfold wsf
    ring
  have h1' : Nf (d1f s2) 0 0 t = 1 - Real.exp (-s2 / 2) := by
    unfold Nf
    rw [d1f_sq s2 hs]
    ring
  -- the second pair
  have h2 : Nf (rf s2 g * (lamf t - muf t) / 2) (rf s2 g * (lamf t + muf t) / 2) 0 t +
      Nf (rf s2 g * (lamf t + muf t) / 2) (rf s2 g * (lamf t - muf t) / 2) 0 t =
      wsf s2 g * (lamf t ^ 2 * ((3 + Real.exp (-(2 * t))) / 4 + Real.exp (-t / 2)) +
        muf t ^ 2 * ((3 + Real.exp (-(2 * t))) / 4 - Real.exp (-t / 2))) := by
    unfold Nf
    rw [← rf_sq]
    ring
  have h2' : lamf t ^ 2 * ((3 + Real.exp (-(2 * t))) / 4 + Real.exp (-t / 2)) +
        muf t ^ 2 * ((3 + Real.exp (-(2 * t))) / 4 - Real.exp (-t / 2)) ≤ 2 * t := by
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      simp [lamf_zero, muf_zero]
    · have hl : lamf t ^ 2 = t / 2 := Real.sq_sqrt (by positivity)
      have hm : muf t ^ 2 = 2 / t := by
        unfold muf
        rw [inv_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [hl, hm]
      have hA : (3 + Real.exp (-(2 * t))) / 4 + Real.exp (-t / 2) ≤ 2 := by linarith
      have hB : (3 + Real.exp (-(2 * t))) / 4 - Real.exp (-t / 2) ≤ t ^ 2 / 2 := by linarith
      have h3 : t / 2 * ((3 + Real.exp (-(2 * t))) / 4 + Real.exp (-t / 2)) ≤ t / 2 * 2 :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      have h4 : 2 / t * ((3 + Real.exp (-(2 * t))) / 4 - Real.exp (-t / 2)) ≤
          2 / t * (t ^ 2 / 2) := mul_le_mul_of_nonneg_left hB (by positivity)
      have h5 : 2 / t * (t ^ 2 / 2) = t := by
        field_simp
      linarith
  -- the third pair
  have h3 : Nf 0 (rf s2 g * tauf g) (rf s2 g) t + Nf 0 (rf s2 g * tauf g) 0 t =
      wsf s2 g * tauf g ^ 2 * (1 + Real.exp (-(2 * t))) +
        wsf s2 g * ((1 - Real.exp (-(2 * t))) / 2) := by
    unfold Nf
    rw [← rf_sq]
    ring
  have h3' : wsf s2 g * tauf g ^ 2 ≤ 2 * (Real.exp (-s2 / 2) * (Real.cosh g - 1)) := by
    have hcp := Real.cosh_pos g
    have e : wsf s2 g * tauf g ^ 2 =
        Real.exp (-s2 / 2) * ((Real.cosh g - 1) * ((Real.cosh g + 1) / Real.cosh g)) := by
      unfold wsf tauf
      have hsq := Real.cosh_sq g
      have hs2 : Real.sinh g ^ 2 = (Real.cosh g - 1) * (Real.cosh g + 1) := by
        have h' : (Real.cosh g - 1) * (Real.cosh g + 1) = Real.cosh g ^ 2 - 1 := by ring
        rw [h', hsq]
        ring
      rw [div_pow, hs2]
      field_simp
    rw [e]
    have h6 : (Real.cosh g + 1) / Real.cosh g ≤ 2 := by
      rw [div_le_iff₀ hcp]
      linarith
    have h7 : (Real.cosh g - 1) * ((Real.cosh g + 1) / Real.cosh g) ≤ (Real.cosh g - 1) * 2 :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    nlinarith
  have h3'' : 0 ≤ wsf s2 g * tauf g ^ 2 := mul_nonneg hws (sq_nonneg _)
  have h8 : wsf s2 g * tauf g ^ 2 * (1 + Real.exp (-(2 * t))) ≤ wsf s2 g * tauf g ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) h3''
  have h9 : wsf s2 g * ((1 - Real.exp (-(2 * t))) / 2) ≤ wsf s2 g * t :=
    mul_le_mul_of_nonneg_left (by linarith) hws
  have h10 : wsf s2 g * (lamf t ^ 2 * ((3 + Real.exp (-(2 * t))) / 4 + Real.exp (-t / 2)) +
        muf t ^ 2 * ((3 + Real.exp (-(2 * t))) / 4 - Real.exp (-t / 2))) ≤ wsf s2 g * (2 * t) :=
    mul_le_mul_of_nonneg_left h2' hws
  have hB : Bf s2 g t = 5 * (Real.exp (-s2 / 2) * (Real.cosh g - 1)) + (1 - Real.exp (-s2 / 2)) +
      3 * t * wsf s2 g := rfl
  rw [hB]
  linarith

/-- The Gaussian integral of the dominating function is at most `3 s² + 3 t`. -/
private lemma Bf_int_bound (s2 t : ℝ) :
    5 * (Real.exp (-s2 / 2) * (Real.exp (s2 / 2) - 1)) + (1 - Real.exp (-s2 / 2)) +
      3 * t * (Real.exp (-s2 / 2) * Real.exp (s2 / 2)) ≤ 3 * s2 + 3 * t := by
  have h1 : Real.exp (-s2 / 2) * Real.exp (s2 / 2) = 1 := by
    rw [← Real.exp_add]
    simp [neg_div]
  have h2 : 1 - s2 / 2 ≤ Real.exp (-s2 / 2) := by
    have := Real.add_one_le_exp (-s2 / 2)
    linarith
  have h3 : Real.exp (-s2 / 2) * (Real.exp (s2 / 2) - 1) = 1 - Real.exp (-s2 / 2) := by
    rw [mul_sub, h1, mul_one]
  rw [h3, h1]
  linarith

end

end PartS

section PartF1

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

/-! ### The decomposition of the symmetrized integrand into signed rank-one fields -/

private lemma fld_apply_star {n : ℕ} (y b : Fin n × Fin 2 → ℝ) (α β γ : ℝ) (v : Fin n → ℕ) :
    star (fld y b α β γ v) = (α : ℂ) * star (A0 y v) +
      (β : ℂ) * ((star (Ap y b v) + star (Ap y (-b) v)) / 2) +
      (γ : ℂ) * ((star (Ap y b v) - star (Ap y (-b) v)) / 2) := by
  rw [fld_apply]
  simp only [star_add, star_sub, star_mul', star_div₀, Complex.star_def, Complex.conj_ofReal]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofNat 2
  rw [h2]

/-- The pointwise algebraic identity behind the decomposition. -/
private lemma ptwise_identity (a p q a' p' q' : ℂ) (c1 d1 r lam mu τ ws wa e0 : ℝ)
    (h1 : c1 ^ 2 = ws - e0) (h2 : d1 ^ 2 = 1 - e0) (h3 : r ^ 2 = ws)
    (h4 : lam * mu = 1 ∨ (lam = 0 ∧ mu = 0 ∧ p = a ∧ q = a ∧ p' = a' ∧ q' = a'))
    (h5 : ws * τ = wa) :
    (((c1 : ℝ) : ℂ) * a + ((0 : ℝ) : ℂ) * ((p + q) / 2) + ((0 : ℝ) : ℂ) * ((p - q) / 2)) *
        (((c1 : ℝ) : ℂ) * a' + ((0 : ℝ) : ℂ) * ((p' + q') / 2) + ((0 : ℝ) : ℂ) * ((p' - q') / 2)) +
      (((r * (lam - mu) / 2 : ℝ) : ℂ) * a + ((r * (lam + mu) / 2 : ℝ) : ℂ) * ((p + q) / 2) +
          ((0 : ℝ) : ℂ) * ((p - q) / 2)) *
        (((r * (lam - mu) / 2 : ℝ) : ℂ) * a' + ((r * (lam + mu) / 2 : ℝ) : ℂ) * ((p' + q') / 2) +
          ((0 : ℝ) : ℂ) * ((p' - q') / 2)) +
      (((0 : ℝ) : ℂ) * a + ((r * τ : ℝ) : ℂ) * ((p + q) / 2) + ((r : ℝ) : ℂ) * ((p - q) / 2)) *
        (((0 : ℝ) : ℂ) * a' + ((r * τ : ℝ) : ℂ) * ((p' + q') / 2) +
          ((r : ℝ) : ℂ) * ((p' - q') / 2)) -
      ((((d1 : ℝ) : ℂ) * a + ((0 : ℝ) : ℂ) * ((p + q) / 2) + ((0 : ℝ) : ℂ) * ((p - q) / 2)) *
        (((d1 : ℝ) : ℂ) * a' + ((0 : ℝ) : ℂ) * ((p' + q') / 2) + ((0 : ℝ) : ℂ) * ((p' - q') / 2)) +
      (((r * (lam + mu) / 2 : ℝ) : ℂ) * a + ((r * (lam - mu) / 2 : ℝ) : ℂ) * ((p + q) / 2) +
          ((0 : ℝ) : ℂ) * ((p - q) / 2)) *
        (((r * (lam + mu) / 2 : ℝ) : ℂ) * a' + ((r * (lam - mu) / 2 : ℝ) : ℂ) * ((p' + q') / 2) +
          ((0 : ℝ) : ℂ) * ((p' - q') / 2)) +
      (((0 : ℝ) : ℂ) * a + ((r * τ : ℝ) : ℂ) * ((p + q) / 2) + ((0 : ℝ) : ℂ) * ((p - q) / 2)) *
        (((0 : ℝ) : ℂ) * a' + ((r * τ : ℝ) : ℂ) * ((p' + q') / 2) +
          ((0 : ℝ) : ℂ) * ((p' - q') / 2))) =
    (((ws + wa) / 2 : ℝ) : ℂ) * (p * p') + (((ws - wa) / 2 : ℝ) : ℂ) * (q * q') - a * a' := by
  have h1c : ((c1 : ℝ) : ℂ) ^ 2 = (ws : ℂ) - (e0 : ℂ) := by exact_mod_cast h1
  have h2c : ((d1 : ℝ) : ℂ) ^ 2 = 1 - (e0 : ℂ) := by exact_mod_cast h2
  have h3c : ((r : ℝ) : ℂ) ^ 2 = (ws : ℂ) := by exact_mod_cast h3
  have h5c : (ws : ℂ) * (τ : ℂ) = (wa : ℂ) := by exact_mod_cast h5
  rcases h4 with h4 | ⟨hl, hm, hp, hq, hp', hq'⟩
  · have h4c : (lam : ℂ) * (mu : ℂ) = 1 := by exact_mod_cast h4
    push_cast
    linear_combination (a * a') * h1c - (a * a') * h2c +
      ((lam : ℂ) * (mu : ℂ) * ((p + q) / 2 * ((p' + q') / 2) - a * a') +
        (τ : ℂ) * ((p + q) / 2 * ((p' - q') / 2) + (p - q) / 2 * ((p' + q') / 2)) +
        (p - q) / 2 * ((p' - q') / 2)) * h3c +
      ((ws : ℂ) * ((p + q) / 2 * ((p' + q') / 2) - a * a')) * h4c +
      ((p + q) / 2 * ((p' - q') / 2) + (p - q) / 2 * ((p' + q') / 2)) * h5c
  · subst hl hm hp hq hp' hq'
    push_cast
    linear_combination (q * q') * h1c - (q * q') * h2c

/-- Trace-norm bound for the symmetrized difference of the two mixtures. -/
private theorem decomp_bound {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y B : Ω → Fin n × Fin 2 → ℝ) (hY : ∀ a, Measurable (fun ω => Y ω a))
    (hB : ∀ a, Measurable (fun ω => B ω a))
    (s2 g : Ω → ℝ) (hs2 : Measurable s2) (hg : Measurable g) (hs0 : ∀ ω, 0 ≤ s2 ω)
    (hBint : Integrable (fun ω => Bf (s2 ω) (g ω) (tpar (B ω))) P)
    (X₁ X₂ : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) (hX₁ : IsDensity X₁) (hX₂ : IsDensity X₂)
    (hΘ : ∀ u v, X₁ u v - X₂ u v = ∫ ω,
      ((((wsf (s2 ω) (g ω) + waf (s2 ω) (g ω)) / 2 : ℝ) : ℂ) *
          (Ap (Y ω) (B ω) u * star (Ap (Y ω) (B ω) v)) +
        (((wsf (s2 ω) (g ω) - waf (s2 ω) (g ω)) / 2 : ℝ) : ℂ) *
          (Ap (Y ω) (-B ω) u * star (Ap (Y ω) (-B ω) v)) -
        A0 (Y ω) u * star (A0 (Y ω) v)) ∂P) :
    traceSize (X₁ - X₂) ≤ ENNReal.ofReal (∫ ω, Bf (s2 ω) (g ω) (tpar (B ω)) ∂P) := by
  -- measurability of the scalar coefficients
  have ht : Measurable (fun ω => tpar (B ω)) := by
    simp only [tpar_eq]
    exact (Finset.measurable_sum _ fun a _ => (hB a).pow_const 2).div_const 2
  have hws : Measurable (fun ω => wsf (s2 ω) (g ω)) := by
    unfold wsf
    exact (Real.measurable_exp.comp ((hs2.neg).div_const 2)).mul (Real.measurable_cosh.comp hg)
  have hr : Measurable (fun ω => rf (s2 ω) (g ω)) := by
    unfold rf
    exact Real.continuous_sqrt.measurable.comp hws
  have hτ : Measurable (fun ω => tauf (g ω)) := by
    unfold tauf
    exact (Real.measurable_sinh.comp hg).div (Real.measurable_cosh.comp hg)
  have hc1 : Measurable (fun ω => c1f (s2 ω) (g ω)) := by
    unfold c1f
    exact Real.continuous_sqrt.measurable.comp ((Real.measurable_exp.comp ((hs2.neg).div_const 2)).mul
      ((Real.measurable_cosh.comp hg).sub_const 1))
  have hd1 : Measurable (fun ω => d1f (s2 ω)) := by
    unfold d1f
    exact Real.continuous_sqrt.measurable.comp
      (measurable_const.sub (Real.measurable_exp.comp ((hs2.neg).div_const 2)))
  have hlam : Measurable (fun ω => lamf (tpar (B ω))) := by
    unfold lamf
    exact Real.continuous_sqrt.measurable.comp (ht.div_const 2)
  have hmu : Measurable (fun ω => muf (tpar (B ω))) := by
    unfold muf
    exact (Real.continuous_sqrt.measurable.comp (ht.div_const 2)).inv
  have h0m : Measurable (fun _ : Ω => (0 : ℝ)) := measurable_const
  -- the six fields
  set F1 : Ω → Hilbert (Fin n → ℕ) := fun ω => fld (Y ω) (B ω) (c1f (s2 ω) (g ω)) 0 0 with hF1
  set F2 : Ω → Hilbert (Fin n → ℕ) := fun ω => fld (Y ω) (B ω)
    (rf (s2 ω) (g ω) * (lamf (tpar (B ω)) - muf (tpar (B ω))) / 2)
    (rf (s2 ω) (g ω) * (lamf (tpar (B ω)) + muf (tpar (B ω))) / 2) 0 with hF2
  set F3 : Ω → Hilbert (Fin n → ℕ) := fun ω => fld (Y ω) (B ω) 0
    (rf (s2 ω) (g ω) * tauf (g ω)) (rf (s2 ω) (g ω)) with hF3
  set G1 : Ω → Hilbert (Fin n → ℕ) := fun ω => fld (Y ω) (B ω) (d1f (s2 ω)) 0 0 with hG1
  set G2 : Ω → Hilbert (Fin n → ℕ) := fun ω => fld (Y ω) (B ω)
    (rf (s2 ω) (g ω) * (lamf (tpar (B ω)) + muf (tpar (B ω))) / 2)
    (rf (s2 ω) (g ω) * (lamf (tpar (B ω)) - muf (tpar (B ω))) / 2) 0 with hG2
  set G3 : Ω → Hilbert (Fin n → ℕ) := fun ω => fld (Y ω) (B ω) 0
    (rf (s2 ω) (g ω) * tauf (g ω)) 0 with hG3
  have mF1 : ∀ u, Measurable (fun ω => F1 ω u) := fun u =>
    fld_measurable Y B hY hB _ _ _ hc1 h0m h0m u
  have mF2 : ∀ u, Measurable (fun ω => F2 ω u) := fun u =>
    fld_measurable Y B hY hB _ _ _ ((hr.mul (hlam.sub hmu)).div_const 2)
      ((hr.mul (hlam.add hmu)).div_const 2) h0m u
  have mF3 : ∀ u, Measurable (fun ω => F3 ω u) := fun u =>
    fld_measurable Y B hY hB _ _ _ h0m (hr.mul hτ) hr u
  have mG1 : ∀ u, Measurable (fun ω => G1 ω u) := fun u =>
    fld_measurable Y B hY hB _ _ _ hd1 h0m h0m u
  have mG2 : ∀ u, Measurable (fun ω => G2 ω u) := fun u =>
    fld_measurable Y B hY hB _ _ _ ((hr.mul (hlam.add hmu)).div_const 2)
      ((hr.mul (hlam.sub hmu)).div_const 2) h0m u
  have mG3 : ∀ u, Measurable (fun ω => G3 ω u) := fun u =>
    fld_measurable Y B hY hB _ _ _ h0m (hr.mul hτ) h0m u
  -- the masses
  have hmass : ∀ ω, ‖F1 ω‖ ^ 2 + ‖F2 ω‖ ^ 2 + ‖F3 ω‖ ^ 2 +
      (‖G1 ω‖ ^ 2 + ‖G2 ω‖ ^ 2 + ‖G3 ω‖ ^ 2) ≤ Bf (s2 ω) (g ω) (tpar (B ω)) := by
    intro ω
    have h := mass_bound (s2 ω) (g ω) (tpar (B ω)) (hs0 ω) (tpar_nonneg _)
    simp only [hF1, hF2, hF3, hG1, hG2, hG3, fld_norm_sq]
    exact h
  have hintOf : ∀ F : Ω → Hilbert (Fin n → ℕ), (∀ u, Measurable (fun ω => F ω u)) →
      (∀ ω, ‖F ω‖ ^ 2 ≤ Bf (s2 ω) (g ω) (tpar (B ω))) → Integrable (fun ω => ‖F ω‖ ^ 2) P := by
    intro F hFm hle
    refine Integrable.mono' hBint (norm_sq_measurable F hFm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle ω
  have iF1 := hintOf F1 mF1 fun ω => by
    have := hmass ω
    nlinarith [sq_nonneg ‖F2 ω‖, sq_nonneg ‖F3 ω‖, sq_nonneg ‖G1 ω‖, sq_nonneg ‖G2 ω‖,
      sq_nonneg ‖G3 ω‖]
  have iF2 := hintOf F2 mF2 fun ω => by
    have := hmass ω
    nlinarith [sq_nonneg ‖F1 ω‖, sq_nonneg ‖F3 ω‖, sq_nonneg ‖G1 ω‖, sq_nonneg ‖G2 ω‖,
      sq_nonneg ‖G3 ω‖]
  have iF3 := hintOf F3 mF3 fun ω => by
    have := hmass ω
    nlinarith [sq_nonneg ‖F1 ω‖, sq_nonneg ‖F2 ω‖, sq_nonneg ‖G1 ω‖, sq_nonneg ‖G2 ω‖,
      sq_nonneg ‖G3 ω‖]
  have iG1 := hintOf G1 mG1 fun ω => by
    have := hmass ω
    nlinarith [sq_nonneg ‖F1 ω‖, sq_nonneg ‖F2 ω‖, sq_nonneg ‖F3 ω‖, sq_nonneg ‖G2 ω‖,
      sq_nonneg ‖G3 ω‖]
  have iG2 := hintOf G2 mG2 fun ω => by
    have := hmass ω
    nlinarith [sq_nonneg ‖F1 ω‖, sq_nonneg ‖F2 ω‖, sq_nonneg ‖F3 ω‖, sq_nonneg ‖G1 ω‖,
      sq_nonneg ‖G3 ω‖]
  have iG3 := hintOf G3 mG3 fun ω => by
    have := hmass ω
    nlinarith [sq_nonneg ‖F1 ω‖, sq_nonneg ‖F2 ω‖, sq_nonneg ‖F3 ω‖, sq_nonneg ‖G1 ω‖,
      sq_nonneg ‖G2 ω‖]
  -- positivity and traces
  have hPos := PT_add (PT_add (rk_PT P F1 mF1 iF1) (rk_PT P F2 mF2 iF2)) (rk_PT P F3 mF3 iF3)
  have hNeg := PT_add (PT_add (rk_PT P G1 mG1 iG1) (rk_PT P G2 mG2 iG2)) (rk_PT P G3 mG3 iG3)
  -- the decomposition
  have hdiff : X₁ - X₂ = (rk P F1 + rk P F2 + rk P F3) - (rk P G1 + rk P G2 + rk P G3) := by
    funext u v
    have e1 := rk_entry_integrable P F1 mF1 iF1 u v
    have e2 := rk_entry_integrable P F2 mF2 iF2 u v
    have e3 := rk_entry_integrable P F3 mF3 iF3 u v
    have e4 := rk_entry_integrable P G1 mG1 iG1 u v
    have e5 := rk_entry_integrable P G2 mG2 iG2 u v
    have e6 := rk_entry_integrable P G3 mG3 iG3 u v
    have hsplit : ((rk P F1 + rk P F2 + rk P F3) - (rk P G1 + rk P G2 + rk P G3)) u v =
        ∫ ω, (F1 ω u * star (F1 ω v) + F2 ω u * star (F2 ω v) + F3 ω u * star (F3 ω v) -
          (G1 ω u * star (G1 ω v) + G2 ω u * star (G2 ω v) + G3 ω u * star (G3 ω v))) ∂P := by
      have h1 := integral_add e1 e2
      have h2 := integral_add (e1.add e2) e3
      have h3 := integral_add e4 e5
      have h4 := integral_add (e4.add e5) e6
      have h5 := integral_sub ((e1.add e2).add e3) ((e4.add e5).add e6)
      simp only [Pi.add_apply] at h2 h4 h5
      rw [h5, h2, h1, h4, h3]
      rfl
    rw [hsplit, Matrix.sub_apply, hΘ u v]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF1, hF2, hF3, hG1, hG2, hG3, fld_apply_star]
    simp only [fld_apply]
    refine (ptwise_identity _ _ _ _ _ _ (c1f (s2 ω) (g ω)) (d1f (s2 ω)) (rf (s2 ω) (g ω))
      (lamf (tpar (B ω))) (muf (tpar (B ω))) (tauf (g ω)) (wsf (s2 ω) (g ω)) (waf (s2 ω) (g ω))
      (Real.exp (-s2 ω / 2)) (c1f_sq _ _) (d1f_sq _ (hs0 ω)) (rf_sq _ _) ?_
      (wsf_mul_tauf _ _)).symm
    rcases (tpar_nonneg (B ω)).eq_or_lt with h0 | hpos
    · right
      have hB0 : B ω = 0 := eq_zero_of_tpar _ h0.symm
      rw [← h0, hB0, neg_zero, Ap_zero]
      exact ⟨lamf_zero, muf_zero, rfl, rfl, rfl, rfl⟩
    · left
      exact lamf_mul_muf _ hpos
  -- equality of the two masses
  have hM : ∫ ω, ‖F1 ω‖ ^ 2 ∂P + ∫ ω, ‖F2 ω‖ ^ 2 ∂P + ∫ ω, ‖F3 ω‖ ^ 2 ∂P =
      ∫ ω, ‖G1 ω‖ ^ 2 ∂P + ∫ ω, ‖G2 ω‖ ^ 2 ∂P + ∫ ω, ‖G3 ω‖ ^ 2 ∂P := by
    have h1 := ((PT_of_density hX₁).2.sub (PT_of_density hX₂).2)
    have h2 := hPos.2.sub hNeg.2
    have h3 : (fun i => (X₁ i i).re - (X₂ i i).re) =
        fun i => ((rk P F1 + rk P F2 + rk P F3) i i).re -
          ((rk P G1 + rk P G2 + rk P G3) i i).re := by
      funext i
      have := congrFun (congrFun hdiff i) i
      rw [Matrix.sub_apply, Matrix.sub_apply] at this
      rw [← Complex.sub_re, ← Complex.sub_re, this]
    rw [h3] at h1
    have h4 := h1.unique h2
    linarith
  have hM0 : 0 ≤ ∫ ω, ‖F1 ω‖ ^ 2 ∂P + ∫ ω, ‖F2 ω‖ ^ 2 ∂P + ∫ ω, ‖F3 ω‖ ^ 2 ∂P :=
    add_nonneg (add_nonneg (integral_nonneg fun ω => by positivity)
      (integral_nonneg fun ω => by positivity)) (integral_nonneg fun ω => by positivity)
  rw [← hM] at hNeg
  rw [hdiff]
  refine (PT_diff_bound X₂ hX₂ hM0 hPos hNeg).trans (ENNReal.ofReal_le_ofReal ?_)
  have htot : 2 * (∫ ω, ‖F1 ω‖ ^ 2 ∂P + ∫ ω, ‖F2 ω‖ ^ 2 ∂P + ∫ ω, ‖F3 ω‖ ^ 2 ∂P) =
      ∫ ω, (‖F1 ω‖ ^ 2 + ‖F2 ω‖ ^ 2 + ‖F3 ω‖ ^ 2 +
        (‖G1 ω‖ ^ 2 + ‖G2 ω‖ ^ 2 + ‖G3 ω‖ ^ 2)) ∂P := by
    have h1 := integral_add iF1 iF2
    have h2 := integral_add (iF1.add iF2) iF3
    have h3 := integral_add iG1 iG2
    have h4 := integral_add (iG1.add iG2) iG3
    have h5 := integral_add ((iF1.add iF2).add iF3) ((iG1.add iG2).add iG3)
    simp only [Pi.add_apply] at h2 h4 h5
    rw [h5, h2, h1, h4, h3, ← hM]
    ring
  rw [htot]
  exact integral_mono (((iF1.add iF2).add iF3).add ((iG1.add iG2).add iG3)) hBint hmass

end

end PartF1

section PartE

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

/-! ### Reindexing and matrix algebra -/

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

/-- A Gaussian state with classical covariance is the Gaussian mixture of coherent states. -/
private lemma coeff_eq_mixArr {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (h : IsGaussianState ρ μ S) :
    ρ.coefficients = mixArr (fun a => μ (qe a))
      ((S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix qe qe) := by
  have h2 := mix_gaussian μ S hS
  exact state_ext_characteristic ρ ⟨_, mixArr_density _ _⟩ fun ξ => (h.2 ξ).trans (h2.2 ξ).symm

private lemma trace_reindex {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (M.submatrix (qe (n := n)) qe).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp (qeE n) fun k => M k k

private lemma inv_mul_reindex {n : ℕ} (S D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    (S.submatrix (qe (n := n)) qe)⁻¹ * D.submatrix (qe (n := n)) qe =
      (S⁻¹ * D).submatrix (qe (n := n)) qe := by
  have h1 := Matrix.inv_submatrix_equiv S (qeE n) (qeE n)
  have h2 := Matrix.submatrix_mul_equiv S⁻¹ D (qeE n) (qeE n) (qeE n)
  have h3 : (⇑(qeE n) : Fin n × Fin 2 → Fin n ⊕ Fin n) = qe := rfl
  rw [h3] at h1 h2
  rw [h1, h2]

open scoped MatrixOrder in
/-- The split `x = T S⁻¹ x + ½ S⁻¹ x` and the identity `‖√T S⁻¹x‖² + ½‖S⁻¹x‖² = xᵀS⁻¹x`. -/
private lemma split_facts {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ)
    (hTi : (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (∀ x : ι → ℝ, CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ
        (CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ (Si⁻¹ *ᵥ x)) +
          (1 / 2 : ℝ) • (Si⁻¹ *ᵥ x) = x) ∧
    (∀ x : ι → ℝ, (CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ (Si⁻¹ *ᵥ x)) ⬝ᵥ
        (CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ (Si⁻¹ *ᵥ x)) +
          (1 / 2 : ℝ) * ((Si⁻¹ *ᵥ x) ⬝ᵥ (Si⁻¹ *ᵥ x)) = x ⬝ᵥ Si⁻¹ *ᵥ x) := by
  have hSpd : Si.PosDef := by
    have h1 := Matrix.PosDef.posSemidef_add hTi
      ((Matrix.PosDef.one (n := ι) (R := ℝ)).smul (show (0 : ℝ) < 1 / 2 by norm_num))
    rwa [sub_add_cancel] at h1
  have hSinv : Si * Si⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Si ((Matrix.isUnit_iff_isUnit_det Si).mp hSpd.isUnit)
  have hRR := sqrt_mul_self _ hTi
  have hRs := sqrt_sym (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ))
  set R := CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) with hR
  have key : ∀ x : ι → ℝ, R *ᵥ (R *ᵥ (Si⁻¹ *ᵥ x)) + (1 / 2 : ℝ) • (Si⁻¹ *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, hRR, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_add_cancel, Matrix.mulVec_mulVec, hSinv, Matrix.one_mulVec]
  refine ⟨key, fun x => ?_⟩
  rw [dot_sym R hRs, ← smul_eq_mul (a := (1 / 2 : ℝ)), ← dotProduct_smul, ← dotProduct_add, key x,
    dotProduct_comm]

end

end PartE

section PartF2

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

/-! ### The split of the extra noise -/

open scoped MatrixOrder in
/-- `h_x = √T S⁻¹ x`. -/
private def hhF {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ι → ℝ :=
  CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ (Si⁻¹ *ᵥ x.ofLp)

/-- `b_x = ½ S⁻¹ x`. -/
private def bbF {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ι → ℝ :=
  (1 / 2 : ℝ) • (Si⁻¹ *ᵥ x.ofLp)

open scoped MatrixOrder in
/-- `y_z = m + √T z`. -/
private def YF {ι : Type} [Fintype ι] [DecidableEq ι] (mf : ι → ℝ) (Si : Matrix ι ι ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ι → ℝ :=
  mf + CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ ω.2.ofLp

private lemma mulVec_measurable {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) :
    Measurable (fun x : EuclideanSpace ℝ ι => M *ᵥ x.ofLp) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private lemma mulVec_measurable' {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) :
    Measurable (fun v : ι → ℝ => M *ᵥ v) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

open scoped MatrixOrder in
private lemma hhF_measurable {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) :
    Measurable (hhF Si) :=
  (mulVec_measurable' _).comp (mulVec_measurable Si⁻¹)

private lemma bbF_measurable {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) :
    Measurable (bbF Si) :=
  (mulVec_measurable Si⁻¹).const_smul (1 / 2 : ℝ)

open scoped MatrixOrder in
private lemma hhF_neg {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    hhF Si (-x) = -hhF Si x := by
  unfold hhF
  rw [WithLp.ofLp_neg, Matrix.mulVec_neg, Matrix.mulVec_neg]

private lemma bbF_neg {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    bbF Si (-x) = -bbF Si x := by
  unfold bbF
  rw [WithLp.ofLp_neg, Matrix.mulVec_neg, smul_neg]

open scoped MatrixOrder in
private lemma hb_split {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ)
    (hTi : (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef) (x : EuclideanSpace ℝ ι) :
    CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) *ᵥ hhF Si x + bbF Si x = x.ofLp :=
  (split_facts Si hTi).1 x.ofLp

private lemma hb_quad {n : ℕ} (Si : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hTi : (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    ∑ i, hhF Si x i ^ 2 + 4 * tpar (bbF Si x) = x.ofLp ⬝ᵥ Si⁻¹ *ᵥ x.ofLp := by
  rw [← (split_facts Si hTi).2 x.ofLp, tpar_eq]
  unfold hhF bbF
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, sq]
  rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The two mixtures as integrals over `N(0, Δ) ⊗ γ` -/

open scoped MatrixOrder in
private lemma YF_measurable {ι : Type} [Fintype ι] [DecidableEq ι] (mf : ι → ℝ) (Si : Matrix ι ι ℝ)
    (a : ι) : Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => YF mf Si ω a) := by
  have h : Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => YF mf Si ω) :=
    measurable_const.add ((mulVec_measurable _).comp measurable_snd)
  exact (measurable_pi_apply a).comp h

private lemma bbF_measurable' {ι : Type} [Fintype ι] [DecidableEq ι] (Si : Matrix ι ι ℝ) (a : ι) :
    Measurable (fun ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => bbF Si ω.1 a) :=
  (measurable_pi_apply a).comp ((bbF_measurable Si).comp measurable_fst)

open scoped MatrixOrder in
private lemma mix_entry_base {n : ℕ} (mf : Fin n × Fin 2 → ℝ)
    (Si Δi : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (u v : Fin n → ℕ) :
    mixArr mf (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) u v =
      ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2),
        A0 (YF mf Si ω) u * star (A0 (YF mf Si ω) v)
        ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi).prod
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)))) := by
  have h1 : ∀ z : EuclideanSpace ℝ (Fin n × Fin 2),
      matOf (cj (vacOp n) (fun a => (WithLp.toLp 2 mf + Matrix.toEuclideanCLM (𝕜 := ℝ)
        (CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ))) z) a)) u v =
      A0 (mf + CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *ᵥ
        z.ofLp) u * star (A0 (mf + CFC.sqrt (Si - (1 / 2 : ℝ) •
          (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *ᵥ z.ofLp) v) := by
    intro z
    rw [A0_entry]
    rfl
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
      matOf (cj (vacOp n) (fun a => y a)) u v) :=
    cj_measurable (fun (ω : EuclideanSpace ℝ (Fin n × Fin 2)) a => ω a) (fun a => by fun_prop)
      (vacOp_isNuc n) u v
  unfold mixArr
  rw [show multivariateGaussian (WithLp.toLp 2 mf)
      (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) =
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2))).map (fun z => WithLp.toLp 2 mf +
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ))) z)
      from rfl]
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable,
    integral_congr_ae (Filter.Eventually.of_forall h1)]
  have h2 := integral_fun_snd (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi)
    (ν := stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)))
    (fun z : EuclideanSpace ℝ (Fin n × Fin 2) =>
      A0 (mf + CFC.sqrt (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *ᵥ
        z.ofLp) u * star (A0 (mf + CFC.sqrt (Si - (1 / 2 : ℝ) •
          (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) *ᵥ z.ofLp) v))
  rw [probReal_univ, one_smul] at h2
  exact h2.symm

open scoped MatrixOrder in
private lemma mix_entry_tilt {n : ℕ} (mf : Fin n × Fin 2 → ℝ)
    (Si Δi : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hTi : (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef)
    (hΔi : Δi.PosSemidef) (u v : Fin n → ℕ) :
    mixArr mf (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + Δi) u v =
      ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2),
        ((cmw (hhF Si) ω : ℝ) : ℂ) *
          (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v))
        ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi).prod
          (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)))) := by
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
      matOf (cj (vacOp n) (fun a => y a)) u v) :=
    cj_measurable (fun (ω : EuclideanSpace ℝ (Fin n × Fin 2)) a => ω a) (fun a => by fun_prop)
      (vacOp_isNuc n) u v
  unfold mixArr
  rw [tilt_change (WithLp.toLp 2 mf) _ Δi hTi hΔi (hhF Si) (bbF Si) (hhF_measurable Si)
    (bbF_measurable Si) (hb_split Si hTi) _ hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ((cmw (hhF Si) ω : ℝ) : ℂ) * matOf (cj (vacOp n) (fun a => (tiltX (WithLp.toLp 2 mf)
    (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)) (bbF Si) ω) a)) u v =
    ((cmw (hhF Si) ω : ℝ) : ℂ) *
      (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v))
  rw [Ap_entry]
  rfl

private lemma integral_neg_fst {ι : Type} [Fintype ι] [DecidableEq ι] (Δ : Matrix ι ι ℝ)
    (hΔ : Δ.PosSemidef) (f : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℂ) (hf : Measurable f) :
    ∫ ω, f ω ∂((multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ).prod
        (stdGaussian (EuclideanSpace ℝ ι))) =
      ∫ ω, f (-ω.1, ω.2) ∂((multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ).prod
        (stdGaussian (EuclideanSpace ℝ ι))) := by
  have h := Measure.map_prod_map (multivariateGaussian (0 : EuclideanSpace ℝ ι) Δ)
    (stdGaussian (EuclideanSpace ℝ ι)) (f := fun x => -x) (g := id) measurable_neg measurable_id
  rw [gauss_neg Δ hΔ, Measure.map_id] at h
  conv_lhs => rw [h]
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

private lemma cmw_eq {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ)
    (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    cmw hh ω = wsf (∑ i, hh ω.1 i ^ 2) (∑ i, hh ω.1 i * ω.2 i) +
      waf (∑ i, hh ω.1 i ^ 2) (∑ i, hh ω.1 i * ω.2 i) := by
  unfold cmw wsf waf
  rw [← mul_add, Real.cosh_add_sinh, ← Real.exp_add]
  congr 1
  ring

private lemma cmw_neg_eq {ι : Type} [Fintype ι] (hh : EuclideanSpace ℝ ι → ι → ℝ)
    (hneg : ∀ x, hh (-x) = -hh x) (ω : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    cmw hh (-ω.1, ω.2) = wsf (∑ i, hh ω.1 i ^ 2) (∑ i, hh ω.1 i * ω.2 i) -
      waf (∑ i, hh ω.1 i ^ 2) (∑ i, hh ω.1 i * ω.2 i) := by
  unfold cmw wsf waf
  rw [← mul_sub, Real.cosh_sub_sinh, ← Real.exp_add]
  congr 1
  simp only [hneg, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_sq]
  ring

/-! ### The integral of the dominating function -/

private lemma Bf_measurable {Ω : Type} [MeasurableSpace Ω] (a b c : Ω → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hc : Measurable c) : Measurable (fun ω => Bf (a ω) (b ω) (c ω)) := by
  unfold Bf
  have h1 : Measurable (fun ω => Real.exp (-a ω / 2)) :=
    Real.measurable_exp.comp (ha.neg.div_const 2)
  have h2 : Measurable (fun ω => Real.cosh (b ω)) := Real.measurable_cosh.comp hb
  exact (((h1.mul (h2.sub_const 1)).const_mul 5).add (measurable_const.sub h1)).add
    ((hc.const_mul 3).mul (h1.mul h2))

private lemma Bf_integral {n : ℕ} (Si Δi : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hTi : (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef)
    (hΔi : Δi.PosSemidef) :
    Integrable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2) =>
        Bf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i) (tpar (bbF Si ω.1)))
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)))) ∧
    ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2),
        Bf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i) (tpar (bbF Si ω.1))
      ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)))) ≤ 4 * (Si⁻¹ * Δi).trace := by
  have hs2m : Measurable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) => ∑ i, hhF Si x i ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hhF_measurable Si)).pow_const 2
  have htm : Measurable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) => tpar (bbF Si x)) := by
    simp only [tpar_eq]
    exact (Finset.measurable_sum _ fun a _ =>
      ((measurable_pi_apply a).comp (bbF_measurable Si)).pow_const 2).div_const 2
  have hgm : Measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ∑ i, hhF Si ω.1 i * ω.2 i) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp ((hhF_measurable Si).comp measurable_fst)).mul (by fun_prop)
  have hfm := Bf_measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ∑ i, hhF Si ω.1 i ^ 2) _
    (fun ω => tpar (bbF Si ω.1)) (hs2m.comp measurable_fst) hgm (htm.comp measurable_fst)
  have hs0 : ∀ x : EuclideanSpace ℝ (Fin n × Fin 2), 0 ≤ ∑ i, hhF Si x i ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨hq, hqi⟩ := gauss_quad Δi hΔi Si⁻¹
  -- the inner integrals
  have hin : ∀ x : EuclideanSpace ℝ (Fin n × Fin 2),
      Integrable (fun z : EuclideanSpace ℝ (Fin n × Fin 2) =>
        Bf (∑ i, hhF Si x i ^ 2) (∑ i, hhF Si x i * z i) (tpar (bbF Si x)))
        (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2))) ∧
      ∫ z : EuclideanSpace ℝ (Fin n × Fin 2),
        Bf (∑ i, hhF Si x i ^ 2) (∑ i, hhF Si x i * z i) (tpar (bbF Si x))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2))) =
      5 * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) * (Real.exp ((∑ i, hhF Si x i ^ 2) / 2) - 1)) +
        (1 - Real.exp (-(∑ i, hhF Si x i ^ 2) / 2)) +
        3 * tpar (bbF Si x) * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) *
          Real.exp ((∑ i, hhF Si x i ^ 2) / 2)) := by
    intro x
    obtain ⟨hc, hci⟩ := gauss_cosh (hhF Si x)
    set s := ∑ i, hhF Si x i ^ 2 with hs
    set t := tpar (bbF Si x) with ht
    have e : (fun z : EuclideanSpace ℝ (Fin n × Fin 2) =>
        Bf s (∑ i, hhF Si x i * z i) t) = fun z =>
        (1 - 6 * Real.exp (-s / 2)) +
          (5 * Real.exp (-s / 2) + 3 * t * Real.exp (-s / 2)) *
            Real.cosh (∑ i, hhF Si x i * z i) := by
      funext z
      unfold Bf
      ring
    rw [e]
    refine ⟨(integrable_const _).add (hc.const_mul _), ?_⟩
    rw [integral_add (integrable_const _) (hc.const_mul _), integral_const, integral_const_mul,
      hci, probReal_univ, one_smul]
    ring
  have hG0 : ∀ x : EuclideanSpace ℝ (Fin n × Fin 2), 0 ≤
      5 * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) * (Real.exp ((∑ i, hhF Si x i ^ 2) / 2) - 1)) +
        (1 - Real.exp (-(∑ i, hhF Si x i ^ 2) / 2)) +
        3 * tpar (bbF Si x) * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) *
          Real.exp ((∑ i, hhF Si x i ^ 2) / 2)) := by
    intro x
    rw [← (hin x).2]
    exact integral_nonneg fun z => Bf_nonneg _ _ _ (hs0 x) (tpar_nonneg _)
  have hGle : ∀ x : EuclideanSpace ℝ (Fin n × Fin 2),
      5 * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) * (Real.exp ((∑ i, hhF Si x i ^ 2) / 2) - 1)) +
        (1 - Real.exp (-(∑ i, hhF Si x i ^ 2) / 2)) +
        3 * tpar (bbF Si x) * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) *
          Real.exp ((∑ i, hhF Si x i ^ 2) / 2)) ≤ 4 * (x.ofLp ⬝ᵥ Si⁻¹ *ᵥ x.ofLp) := by
    intro x
    have h1 := Bf_int_bound (∑ i, hhF Si x i ^ 2) (tpar (bbF Si x))
    have h2 := hb_quad Si hTi x
    have h3 := hs0 x
    have h4 := tpar_nonneg (bbF Si x)
    linarith
  have hGm : Measurable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      5 * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) * (Real.exp ((∑ i, hhF Si x i ^ 2) / 2) - 1)) +
        (1 - Real.exp (-(∑ i, hhF Si x i ^ 2) / 2)) +
        3 * tpar (bbF Si x) * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) *
          Real.exp ((∑ i, hhF Si x i ^ 2) / 2))) := by
    have h1 : Measurable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
        Real.exp (-(∑ i, hhF Si x i ^ 2) / 2)) :=
      Real.measurable_exp.comp (hs2m.neg.div_const 2)
    have h2 : Measurable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
        Real.exp ((∑ i, hhF Si x i ^ 2) / 2)) :=
      Real.measurable_exp.comp (hs2m.div_const 2)
    exact (((h1.mul (h2.sub_const 1)).const_mul 5).add (measurable_const.sub h1)).add
      ((htm.const_mul 3).mul (h1.mul h2))
  have hGi : Integrable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      5 * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) * (Real.exp ((∑ i, hhF Si x i ^ 2) / 2) - 1)) +
        (1 - Real.exp (-(∑ i, hhF Si x i ^ 2) / 2)) +
        3 * tpar (bbF Si x) * (Real.exp (-(∑ i, hhF Si x i ^ 2) / 2) *
          Real.exp ((∑ i, hhF Si x i ^ 2) / 2)))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi) := by
    refine Integrable.mono' (hq.const_mul 4) hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 x)]
    exact hGle x
  obtain ⟨hint, hval⟩ := prod_integrable_of_nonneg
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi)
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2)))
    (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2) =>
      Bf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i) (tpar (bbF Si ω.1))) hfm
    (fun ω => Bf_nonneg _ _ _ (hs0 ω.1) (tpar_nonneg _)) _ (fun x => (hin x).1)
    (fun x => (hin x).2) hGi
  refine ⟨hint, ?_⟩
  rw [hval, ← hqi, ← integral_const_mul]
  exact integral_mono hGi (hq.const_mul 4) hGle

end

end PartF2

section PartF3

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

/-! ### The bound in interleaved coordinates -/

private lemma entry_norm_le_one {I : Type} (x : Hilbert I) (hx : ‖x‖ = 1) (u v : I) :
    ‖x u * star (x v)‖ ≤ 1 := by
  rw [norm_mul, norm_star]
  have h1 := lp.norm_apply_le_norm (p := 2) (by norm_num) x u
  have h2 := lp.norm_apply_le_norm (p := 2) (by norm_num) x v
  rw [hx] at h1 h2
  calc ‖x u‖ * ‖x v‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

open scoped MatrixOrder in
private theorem mix_bound {n : ℕ} (mf : Fin n × Fin 2 → ℝ)
    (Si Δi : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hTi : (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef)
    (hΔi : Δi.PosSemidef) :
    traceSize (mixArr mf (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) + Δi) -
        mixArr mf (Si - (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ))) ≤
      ENNReal.ofReal (4 * (Si⁻¹ * Δi).trace) := by
  obtain ⟨hBint, hBle⟩ := Bf_integral Si Δi hTi hΔi
  have hY := YF_measurable mf Si
  have hB := bbF_measurable' Si
  have hs2 : Measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ∑ i, hhF Si ω.1 i ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp ((hhF_measurable Si).comp measurable_fst)).pow_const 2
  have hg : Measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ∑ i, hhF Si ω.1 i * ω.2 i) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp ((hhF_measurable Si).comp measurable_fst)).mul (by fun_prop)
  refine (decomp_bound _ (YF mf Si) (fun ω => bbF Si ω.1) hY hB _ _ hs2 hg
    (fun ω => Finset.sum_nonneg fun i _ => sq_nonneg _) hBint _ _ (mixArr_density _ _)
    (mixArr_density _ _) ?_).trans (ENNReal.ofReal_le_ofReal hBle)
  intro u v
  set P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n × Fin 2)) Δi).prod
    (stdGaussian (EuclideanSpace ℝ (Fin n × Fin 2))) with hP
  -- the three integrands
  have hwm := cmw_measurable (hhF Si) (hhF_measurable Si)
  have hwm' : Measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ((cmw (hhF Si) ω : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hwm
  have hpm := Ap_measurable (YF mf Si) (fun ω => bbF Si ω.1) hY hB
  have hmm := Ap_measurable (YF mf Si) (fun ω => -bbF Si ω.1) hY (fun a => (hB a).neg)
  have h0m := A0_measurable (YF mf Si) hY
  have hstar : Measurable (fun z : ℂ => star z) := continuous_star.measurable
  have fm : Measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ((cmw (hhF Si) ω : ℝ) : ℂ) *
        (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v))) :=
    hwm'.mul ((hpm u).mul (hstar.comp (hpm v)))
  have hneg_m : Measurable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ((-ω.1, ω.2) : EuclideanSpace ℝ (Fin n × Fin 2) ×
        EuclideanSpace ℝ (Fin n × Fin 2))) := by fun_prop
  -- integrability
  have i1 : Integrable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ((cmw (hhF Si) ω : ℝ) : ℂ) *
        (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v))) P := by
    refine Integrable.mono' (cmw_integrable (hhF Si) (hhF_measurable Si) _) fm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cmw_pos _ _)]
    exact mul_le_of_le_one_right (cmw_pos _ _).le (entry_norm_le_one _ (norm_Ap _ _) u v)
  have i2 : Integrable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => ((cmw (hhF Si) (-ω.1, ω.2) : ℝ) : ℂ) *
        (Ap (YF mf Si ω) (-bbF Si ω.1) u * star (Ap (YF mf Si ω) (-bbF Si ω.1) v))) P := by
    have hw2 : Integrable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
        EuclideanSpace ℝ (Fin n × Fin 2) => cmw (hhF Si) (-ω.1, ω.2)) P :=
      cmw_integrable (fun x => hhF Si (-x)) ((hhF_measurable Si).comp measurable_neg) _
    refine Integrable.mono' hw2 ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((Complex.measurable_ofReal.comp (hwm.comp hneg_m)).mul
        ((hmm u).mul (hstar.comp (hmm v)))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cmw_pos _ _)]
      exact mul_le_of_le_one_right (cmw_pos _ _).le (entry_norm_le_one _ (norm_Ap _ _) u v)
  have i3 : Integrable (fun ω : EuclideanSpace ℝ (Fin n × Fin 2) ×
      EuclideanSpace ℝ (Fin n × Fin 2) => A0 (YF mf Si ω) u * star (A0 (YF mf Si ω) v)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((h0m u).mul (hstar.comp (h0m v))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => entry_norm_le_one _ (norm_A0 _) u v)
  -- the two mixtures
  have e1 := mix_entry_tilt mf Si Δi hTi hΔi u v
  have e0 := mix_entry_base mf Si Δi u v
  have e2 := integral_neg_fst Δi hΔi _ fm
  have e3 : ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2),
      ((cmw (hhF Si) ω : ℝ) : ℂ) *
        (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v)) ∂P =
      ∫ ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2),
        ((cmw (hhF Si) (-ω.1, ω.2) : ℝ) : ℂ) *
          (Ap (YF mf Si ω) (-bbF Si ω.1) u * star (Ap (YF mf Si ω) (-bbF Si ω.1) v)) ∂P := by
    rw [e2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((cmw (hhF Si) (-ω.1, ω.2) : ℝ) : ℂ) *
        (Ap (YF mf Si ω) (bbF Si (-ω.1)) u * star (Ap (YF mf Si ω) (bbF Si (-ω.1)) v)) = _
    rw [bbF_neg]
  rw [e1, e0]
  have hpt : ∀ ω : EuclideanSpace ℝ (Fin n × Fin 2) × EuclideanSpace ℝ (Fin n × Fin 2),
      ((((wsf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i) +
          waf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i)) / 2 : ℝ) : ℂ) *
          (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v)) +
        (((wsf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i) -
          waf (∑ i, hhF Si ω.1 i ^ 2) (∑ i, hhF Si ω.1 i * ω.2 i)) / 2 : ℝ) : ℂ) *
          (Ap (YF mf Si ω) (-bbF Si ω.1) u * star (Ap (YF mf Si ω) (-bbF Si ω.1) v)) -
        A0 (YF mf Si ω) u * star (A0 (YF mf Si ω) v)) =
      (1 / 2 : ℂ) * (((cmw (hhF Si) ω : ℝ) : ℂ) *
          (Ap (YF mf Si ω) (bbF Si ω.1) u * star (Ap (YF mf Si ω) (bbF Si ω.1) v))) +
        (1 / 2 : ℂ) * (((cmw (hhF Si) (-ω.1, ω.2) : ℝ) : ℂ) *
          (Ap (YF mf Si ω) (-bbF Si ω.1) u * star (Ap (YF mf Si ω) (-bbF Si ω.1) v))) -
        A0 (YF mf Si ω) u * star (A0 (YF mf Si ω) v) := by
    intro ω
    rw [cmw_eq (hhF Si) ω, cmw_neg_eq (hhF Si) (hhF_neg Si) ω]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have h5 := integral_sub ((i1.const_mul (1 / 2 : ℂ)).add (i2.const_mul (1 / 2 : ℂ))) i3
  have h6 := integral_add (i1.const_mul (1 / 2 : ℂ)) (i2.const_mul (1 / 2 : ℂ))
  simp only [Pi.add_apply] at h5
  rw [h5, h6, integral_const_mul, integral_const_mul, ← e3]
  ring

end

/-! ### The statement -/

private theorem main {n : ℕ} (ρ ρ' : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (hord : (S' - S).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ S') :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (2 * (S⁻¹ * (S' - S)).trace) := by
  have hS' : (S' - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef := by
    have h1 := hS.add hord
    have h2 : S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) + (S' - S) =
        S' - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by abel
    rwa [h2] at h1
  have e1 := coeff_eq_mixArr ρ μ S hS h
  have e2 := coeff_eq_mixArr ρ' μ S' hS' h'
  have hT : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix
      (qe (n := n)) qe = S.submatrix (qe (n := n)) qe -
        (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      qe_inj]
  have hT' : (S' - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix
      (qe (n := n)) qe = S.submatrix (qe (n := n)) qe -
        (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) +
          (S' - S).submatrix (qe (n := n)) qe := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, qe_inj]
    ring
  rw [hT] at e1
  rw [hT'] at e2
  have hTi : (S.submatrix (qe (n := n)) qe -
      (1 / 2 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)).PosSemidef := by
    rw [← hT]
    exact hS.submatrix qe
  have hb := mix_bound (fun a => μ (qe a)) (S.submatrix (qe (n := n)) qe)
    ((S' - S).submatrix (qe (n := n)) qe) hTi (hord.submatrix qe)
  rw [← e1, ← e2, inv_mul_reindex, trace_reindex] at hb
  unfold traceDist
  calc traceSize (ρ'.coefficients - ρ.coefficients) / 2
      ≤ ENNReal.ofReal (4 * (S⁻¹ * (S' - S)).trace) / 2 := ENNReal.div_le_div_right hb 2
    _ = ENNReal.ofReal (2 * (S⁻¹ * (S' - S)).trace) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_div_of_pos (by norm_num)]
        congr 1
        ring

end PartF3

end CovPert

theorem solution {n : ℕ} (ρ ρ' : State (Occupation (Fin n)))
    (μ : Fin n ⊕ Fin n → ℝ) (S S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (hord : (S' - S).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ S') :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (2 * (S⁻¹ * (S' - S)).trace) :=
  CovPert.main ρ ρ' μ S S' hS hord h h'
