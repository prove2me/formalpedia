-- Prove2me | solution 1 for BosonicLearn.state_displace_pair
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:30:44.677341+00:00
-- url     : https://prove2.me/submissions/64352684-152e-4a0f-84da-1839cc1ba460

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Theorems.Thm_BosonicLearn_displacementMatrix_prod_mul
import Theorems.Thm_BosonicLearn_displacementMatrix_unitary

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass
  NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory
open scoped ENNReal

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

/-! ### Trace norm -/

private lemma traceSize_conj_le {I : Type} (V : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    (A : Hilbert I →L[ℂ] Hilbert I) :
    traceSize (matOf ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L
      (V.symm : Hilbert I →L[ℂ] Hilbert I))) ≤ traceSize (matOf A) := by
  refine le_iInf fun e => ?_
  have h := isNuc_conj V (isNuc_of_exp A e)
  refine (iInf_le _ (expOf h)).trans (le_of_eq ?_)
  simp [expOf]

private lemma traceSize_conj {I : Type} (V : Hilbert I ≃ₗᵢ[ℂ] Hilbert I)
    (A : Hilbert I →L[ℂ] Hilbert I) :
    traceSize (matOf ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L
      (V.symm : Hilbert I →L[ℂ] Hilbert I))) = traceSize (matOf A) := by
  refine le_antisymm (traceSize_conj_le V A) ?_
  have h := traceSize_conj_le V.symm ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L
      (V.symm : Hilbert I →L[ℂ] Hilbert I))
  have h2 : (V.symm : Hilbert I →L[ℂ] Hilbert I) ∘L ((V : Hilbert I →L[ℂ] Hilbert I) ∘L A ∘L
      (V.symm : Hilbert I →L[ℂ] Hilbert I)) ∘L (V.symm.symm : Hilbert I →L[ℂ] Hilbert I) = A := by
    ext x
    simp
  rwa [h2] at h

private lemma matOf_sub {I : Type} (A B : Hilbert I →L[ℂ] Hilbert I) :
    matOf (A - B) = matOf A - matOf B := by
  funext u v
  simp [matOf]

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

theorem solution {n : ℕ} (ρ σ : State (Occupation (Fin n))) (δ : Fin n × Fin 2 → ℝ) :
    ∃ ρ' σ' : State (Occupation (Fin n)),
      (∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ'.coefficients ξ =
        Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) * oscillatorCharacteristic ρ.coefficients ξ) ∧
      (∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ'.coefficients ξ =
        Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) * oscillatorCharacteristic σ.coefficients ξ) ∧
      traceSize (ρ'.coefficients - σ'.coefficients) = traceSize (ρ.coefficients - σ.coefficients) := by
  obtain ⟨Tρ, lρ, rρ, hρ, hρm⟩ := exists_op ρ.coefficients ρ.density.1
  obtain ⟨Tσ, lσ, rσ, hσ, hσm⟩ := exists_op σ.coefficients σ.density.1
  have hρd : IsDensity (matOf Tρ) := hρm ▸ ρ.density
  have hσd : IsDensity (matOf Tσ) := hσm ▸ σ.density
  refine ⟨⟨_, density_conj (Deq (zOf δ)) hρ hρd⟩, ⟨_, density_conj (Deq (zOf δ)) hσ hσd⟩,
    fun ξ => ?_, fun ξ => ?_, ?_⟩
  · rw [← hρm]
    exact char_conj hρ δ ξ
  · rw [← hσm]
    exact char_conj hσ δ ξ
  · show traceSize (matOf _ - matOf _) = _
    rw [← hρm, ← hσm, ← matOf_sub, ← matOf_sub, ← traceSize_conj (Deq (zOf δ)) (Tρ - Tσ)]
    congr 2
    ext x
    simp
