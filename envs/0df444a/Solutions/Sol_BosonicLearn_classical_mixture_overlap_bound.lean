-- Prove2me | solution 1 for BosonicLearn.classical_mixture_overlap_bound
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T21:30:42.94507+00:00
-- url     : https://prove2.me/submissions/09147cc5-2b05-425d-b76a-62ef5849040b

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_displacementMatrix_prod_mul
import Theorems.Thm_BosonicLearn_displacementMatrix_unitary
import Theorems.Thm_BosonicLearn_isDensity_of_posSemidef
import Theorems.Thm_BosonicLearn_vacuum_isGaussianState
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_BosonicLearn_traceDist_le_one

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

/-!
# Two classical states are as close as their mixing measures overlap

`Mix(A; η) u v := ∫ ⟨u|D(x) A D(x)⁻¹|v⟩ dη(x)` (`mixM`) for a nuclear operator `A` and a finite
measure `η` on phase space. For a probability measure and a density `A` it is a density with
characteristic function `η̂(ξ) χ_A(ξ)` (`mix_explicit`, copied from the Gaussian-family solution), so
by `state_ext_characteristic` the classical states are `σ = Mix(|0⟩⟨0|; γ)`,
`σ' = Mix(|0⟩⟨0|; γ')`. Splitting `γ = (γ - κ) + κ`, `γ' = (γ' - κ) + κ` and normalizing the two
remainders of mass `t = 1 - κ(univ)` gives `σ' - σ = t (ω' - ω)` for two states `ω, ω'`, whence
`½‖σ' - σ‖₁ ≤ t` by `traceDist_le_one` and homogeneity of the nuclear norm.
-/

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

/-! ### Trace size: zero and scaling -/

private def zeroExp {I : Type} : NuclearExpansion (0 : Matrix I I ℂ) :=
  ⟨fun _ => 0, fun _ => 0, by simp, fun i j => by simp⟩

private lemma traceSize_zero {I : Type} : traceSize (0 : Matrix I I ℂ) = 0 := by
  refine le_antisymm ((iInf_le _ zeroExp).trans ?_) bot_le
  simp [zeroExp]

private lemma traceDist_self {I : Type} (A : Matrix I I ℂ) : traceDist A A = 0 := by
  unfold traceDist
  rw [sub_self, traceSize_zero, ENNReal.zero_div]

/-- Scaling a nuclear expansion. -/
private def smulExp {I : Type} (c : ℂ) {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    NuclearExpansion (c • X) :=
  ⟨fun k => c • e.left k, e.right, by
      refine (e.summable.mul_left ‖c‖).congr fun k => ?_
      rw [norm_smul, mul_assoc], fun i j => by
      rw [Matrix.smul_apply, e.coefficients i j, smul_eq_mul, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp [mul_assoc]⟩

private lemma traceSize_smul_le {I : Type} (c : ℂ) (X : Matrix I I ℂ) :
    traceSize (c • X) ≤ ENNReal.ofReal ‖c‖ * traceSize X := by
  by_cases hc : c = 0
  · subst hc
    simp [traceSize_zero]
  · unfold traceSize
    rw [ENNReal.mul_iInf_of_ne (by simpa using hc) ENNReal.ofReal_ne_top]
    refine le_iInf fun e => (iInf_le _ (smulExp c e)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (norm_nonneg c), ← tsum_mul_left]
    congr 1
    refine tsum_congr fun k => ?_
    simp [smulExp, norm_smul, mul_assoc]

/-- If `A - B = t (ω' - ω)` for two states `ω, ω'` and `t ≥ 0`, then `½‖A - B‖₁ ≤ t`. -/
private lemma traceDist_scaled {I : Type} (A B : Matrix I I ℂ) (ω ω' : State I) (t : ℝ)
    (ht : 0 ≤ t) (h : A - B = (t : ℂ) • (ω'.coefficients - ω.coefficients)) :
    traceDist A B ≤ ENNReal.ofReal t := by
  have h1 := traceDist_le_one ω' ω
  unfold traceDist at h1 ⊢
  rw [h]
  calc traceSize ((t : ℂ) • (ω'.coefficients - ω.coefficients)) / 2
      ≤ (ENNReal.ofReal ‖(t : ℂ)‖ * traceSize (ω'.coefficients - ω.coefficients)) / 2 := by
        gcongr
        exact traceSize_smul_le _ _
    _ = ENNReal.ofReal t * (traceSize (ω'.coefficients - ω.coefficients) / 2) := by
        rw [mul_div_assoc, Complex.norm_real, Real.norm_of_nonneg ht]
    _ ≤ ENNReal.ofReal t * 1 := by gcongr
    _ = ENNReal.ofReal t := mul_one _

/-! ### Mixtures of displaced copies over a measure on phase space -/

/-- The mixture `∫ D(x) A D(x)⁻¹ dη(x)` of the displaced copies of an operator. -/
private def mixM {n : ℕ} (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ :=
  fun u v => ∫ x : EuclideanSpace ℝ (Fin n × Fin 2), matOf (cj A (fun a => x a)) u v ∂η

private lemma mixM_integrable {n : ℕ} (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsFiniteMeasure η] {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (u v : Fin n → ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      matOf (cj A (fun a => x a)) u v) η :=
  Integrable.of_bound
    (cj_measurable (fun (x : EuclideanSpace ℝ (Fin n × Fin 2)) a => x a) (fun a => by fun_prop)
      hA u v).aestronglyMeasurable ‖A‖
    (Filter.Eventually.of_forall fun x => (matOf_norm_le _ u v).trans (cj_norm_le A _))

private lemma mixM_add_measure {n : ℕ} (η₁ η₂ : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsFiniteMeasure η₁] [IsFiniteMeasure η₂] {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) :
    mixM (η₁ + η₂) A = mixM η₁ A + mixM η₂ A := by
  funext u v
  exact integral_add_measure (mixM_integrable η₁ hA u v) (mixM_integrable η₂ hA u v)

private lemma mixM_smul_measure {n : ℕ} (c : ℝ≥0∞) (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) :
    mixM (c • η) A = ((c.toReal : ℝ) : ℂ) • mixM η A := by
  funext u v
  simp only [mixM, Matrix.smul_apply, integral_smul_measure]
  rw [Complex.real_smul, smul_eq_mul]

private lemma mixM_zero_measure {n : ℕ} (A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)) :
    mixM (0 : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) A = 0 := by
  funext u v
  simp [mixM]

private lemma mixM_density {n : ℕ} (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsProbabilityMeasure η] {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (hd : IsDensity (matOf A)) :
    IsDensity (mixM η A) :=
  (mix_explicit η (fun x a => x a) (fun a => by fun_prop) hA hd).1

private lemma mixM_char {n : ℕ} (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsProbabilityMeasure η] {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (hd : IsDensity (matOf A))
    (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (mixM η A) ξ =
      charFun η (WithLp.toLp 2 ξ) * oscillatorCharacteristic (matOf A) ξ := by
  have h := (mix_explicit η (fun x a => x a) (fun a => by fun_prop) hA hd).2 ξ
  refine h.trans ?_
  congr 1
  rw [charFun_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 : inner ℝ x (WithLp.toLp 2 ξ) = meanForm (fun a => x a) ξ := by
    simp [meanForm, PiLp.inner_apply]
  simp only [h1]
  rw [mul_comm]

/-- A state with the characteristic function of a mixture is that mixture. -/
private lemma mixM_eq_of_char {n : ℕ} (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsProbabilityMeasure η] {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)}
    {l r : ℕ → Hilbert (Fin n → ℕ)} (hA : IsNuc A l r) (hd : IsDensity (matOf A))
    (σ : State (Occupation (Fin n)))
    (h : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ.coefficients ξ =
      charFun η (WithLp.toLp 2 ξ) * oscillatorCharacteristic (matOf A) ξ) :
    σ.coefficients = mixM η A :=
  state_ext_characteristic σ ⟨mixM η A, mixM_density η hA hd⟩
    (fun ξ => by rw [h, mixM_char η hA hd])

/-! ### The characteristic function of the vacuum -/

private lemma qe_inj {n : ℕ} : Function.Injective (qe (n := n)) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  unfold qe at h
  fin_cases k <;> fin_cases l <;> simp_all

private lemma vac_char' (n : ℕ) (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic (matOf (vacOp n)) ξ =
      ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ) := by
  rw [vac_char]
  have hv : varianceForm (fun a b => 2 * ((1 / 2 : ℝ) •
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) (qe a) (qe b)) ξ = ∑ a, ξ a ^ 2 := by
    unfold varianceForm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
      ring
    · intro b _ hb
      have hne : qe a ≠ qe b := fun h => hb (qe_inj h).symm
      simp [hne]
    · simp
  have hm : meanForm (fun a => (0 : Fin n ⊕ Fin n → ℝ) (qe a)) ξ = 0 := by
    simp [meanForm]
  rw [hv, hm]
  simp

/-! ### Normalizing a finite measure -/

/-- The mixture over a nonzero finite measure is its total mass times a state. -/
private lemma mixM_normalize {n : ℕ} (η : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsFiniteMeasure η] (hη : η Set.univ ≠ 0)
    {A : Hilbert (Fin n → ℕ) →L[ℂ] Hilbert (Fin n → ℕ)} {l r : ℕ → Hilbert (Fin n → ℕ)}
    (hA : IsNuc A l r) (hd : IsDensity (matOf A)) :
    ∃ ω : State (Occupation (Fin n)),
      mixM η A = (((η Set.univ).toReal : ℝ) : ℂ) • ω.coefficients := by
  have htop : η Set.univ ≠ ∞ := measure_ne_top η Set.univ
  have : IsProbabilityMeasure ((η Set.univ)⁻¹ • η) :=
    ⟨by simp [ENNReal.inv_mul_cancel hη htop]⟩
  refine ⟨⟨mixM ((η Set.univ)⁻¹ • η) A, mixM_density _ hA hd⟩, ?_⟩
  rw [← mixM_smul_measure, smul_smul, ENNReal.mul_inv_cancel hη htop, one_smul]

end

theorem solution {n : ℕ} (γ γ' κ : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
    [IsProbabilityMeasure γ] [IsProbabilityMeasure γ'] (hκ : κ ≤ γ) (hκ' : κ ≤ γ')
    (σ σ' : State (Occupation (Fin n)))
    (hσ : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ.coefficients ξ =
      charFun γ (WithLp.toLp 2 ξ) * ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ))
    (hσ' : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ'.coefficients ξ =
      charFun γ' (WithLp.toLp 2 ξ) * ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ)) :
    traceDist σ'.coefficients σ.coefficients ≤ ENNReal.ofReal (1 - (κ Set.univ).toReal) := by
  have hV := vacOp_isNuc n
  have hVd := vac_density n
  have e1 : σ.coefficients = mixM γ (vacOp n) :=
    mixM_eq_of_char γ hV hVd σ (fun ξ => by rw [hσ, vac_char'])
  have e2 : σ'.coefficients = mixM γ' (vacOp n) :=
    mixM_eq_of_char γ' hV hVd σ' (fun ξ => by rw [hσ', vac_char'])
  have : IsFiniteMeasure κ := isFiniteMeasure_of_le γ hκ
  have hη : γ - κ + κ = γ := Measure.sub_add_cancel_of_le hκ
  have hη' : γ' - κ + κ = γ' := Measure.sub_add_cancel_of_le hκ'
  have hm : (γ - κ) Set.univ = 1 - κ Set.univ := by
    rw [Measure.sub_apply MeasurableSet.univ hκ, measure_univ]
  have hm' : (γ' - κ) Set.univ = 1 - κ Set.univ := by
    rw [Measure.sub_apply MeasurableSet.univ hκ', measure_univ]
  have hle : κ Set.univ ≤ 1 := (hκ Set.univ).trans_eq measure_univ
  have hreal : (1 - κ Set.univ).toReal = 1 - (κ Set.univ).toReal := by
    rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one]
  have d1 : mixM γ (vacOp n) = mixM (γ - κ) (vacOp n) + mixM κ (vacOp n) := by
    rw [← mixM_add_measure _ _ hV, hη]
  have d2 : mixM γ' (vacOp n) = mixM (γ' - κ) (vacOp n) + mixM κ (vacOp n) := by
    rw [← mixM_add_measure _ _ hV, hη']
  by_cases ht : 1 - κ Set.univ = 0
  · have z1 : γ - κ = 0 := Measure.measure_univ_eq_zero.1 (hm.trans ht)
    have z2 : γ' - κ = 0 := Measure.measure_univ_eq_zero.1 (hm'.trans ht)
    have hEq : σ'.coefficients = σ.coefficients := by
      rw [e1, e2, d1, d2, z1, z2]
    rw [hEq, traceDist_self]
    exact bot_le
  · obtain ⟨ω, hω⟩ := mixM_normalize (γ - κ) (by rw [hm]; exact ht) hV hVd
    obtain ⟨ω', hω'⟩ := mixM_normalize (γ' - κ) (by rw [hm']; exact ht) hV hVd
    rw [← hreal]
    refine traceDist_scaled _ _ ω ω' _ ENNReal.toReal_nonneg ?_
    rw [e1, e2, d1, d2, hω, hω', hm, hm', smul_sub]
    abel
