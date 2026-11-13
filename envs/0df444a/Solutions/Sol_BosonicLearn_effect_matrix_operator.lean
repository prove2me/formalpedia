-- Prove2me | solution 1 for BosonicLearn.effect_matrix_operator
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T04:49:52.777173+00:00
-- url     : https://prove2.me/submissions/d92cee78-ba6a-49b7-a6d0-4d8b76833562

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal ComplexOrder
open Filter Topology

noncomputable section

/-! ### Finite quadratic forms of an effect matrix -/

/-- All finite quadratic forms of `E` are real, non-negative and at most `∑ |zᵢ|²`. -/
private def EffBound {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2

private lemma eff_diag_im {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i : I) :
    (E i i).im = 0 := by
  have h := (hE {i} (Pi.single i 1)).1
  simpa using h

/-- `E` is Hermitian: polarize the reality of the quadratic forms on `{i, j}`. -/
private lemma eff_herm {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i j : I) :
    E j i = star (E i j) := by
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (eff_diag_im hE i)).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := eff_diag_im hE i
    have hjj := eff_diag_im hE j
    have h1 := (hE {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hE {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-- Cauchy–Schwarz for finite complex vectors, in `dotProduct` form. -/
private lemma cs_dot {ι : Type} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2) := by
  have h1 : ‖star u ⬝ᵥ v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖) (fun i => ‖v i‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

open scoped MatrixOrder in
/-- Cauchy–Schwarz for the form of `E` on a finite set: the block is `Bᴴ B`, so the form is an inner product
of `B w` and `B z`, and `‖B z‖² = ⟨z, E z⟩ ≤ ‖z‖²`. -/
private lemma eff_cs {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (s : Finset I)
    (w z : I → ℂ) :
    ‖∑ i ∈ s, ∑ j ∈ s, star (w i) * E i j * z j‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ ^ 2) * (∑ j ∈ s, ‖z j‖ ^ 2) := by
  let M : Matrix s s ℂ := fun a b => E a b
  have form : ∀ x y : I → ℂ, star (fun a : s => x a) ⬝ᵥ M.mulVec (fun a : s => y a) =
      ∑ i ∈ s, ∑ j ∈ s, star (x i) * E i j * y j := by
    intro x y
    rw [← Finset.sum_coe_sort s]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [M, mul_assoc]
  have hM : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply]
      exact (eff_herm hE b a).symm
    · let x' : I → ℂ := fun i => if h : i ∈ s then x ⟨i, h⟩ else 0
      have hx : (fun a : s => x' a) = x := by
        funext a
        simp [x']
      have h := hE s x'
      rw [← hx, form x' x', Complex.nonneg_iff]
      exact ⟨h.2.1, h.1.symm⟩
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have key : ∀ x y : s → ℂ, star x ⬝ᵥ M.mulVec y = star (B.mulVec x) ⬝ᵥ B.mulVec y := by
    intro x y
    rw [hB, Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  have hq : ∀ x : s → ℂ, ∑ c, ‖B.mulVec x c‖ ^ 2 = (star x ⬝ᵥ M.mulVec x).re := by
    intro x
    rw [key x x]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have h1 := cs_dot (B.mulVec fun a : s => w a) (B.mulVec fun a : s => z a)
  rw [← form w z, key]
  refine h1.trans ?_
  rw [hq, hq, form w w, form z z]
  exact mul_le_mul (hE s w).2.2 (hE s z).2.2 (hE s z).2.1 (Finset.sum_nonneg fun i _ => by positivity)

/-- Two-set form of the same inequality. -/
private lemma eff_cs2 {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (s t : Finset I)
    (w z : I → ℂ) :
    ‖∑ i ∈ s, ∑ j ∈ t, star (w i) * E i j * z j‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ ^ 2) * (∑ j ∈ t, ‖z j‖ ^ 2) := by
  have h := eff_cs hE (s ∪ t) (fun i => if i ∈ s then w i else 0) (fun j => if j ∈ t then z j else 0)
  have e1 : ∑ i ∈ s ∪ t, ∑ j ∈ s ∪ t, star (if i ∈ s then w i else 0) * E i j * (if j ∈ t then z j else 0) =
      ∑ i ∈ s, ∑ j ∈ t, star (w i) * E i j * z j := by
    have inner : ∀ i, ∑ j ∈ s ∪ t, star (if i ∈ s then w i else 0) * E i j * (if j ∈ t then z j else 0) =
        if i ∈ s then ∑ j ∈ t, star (w i) * E i j * z j else 0 := by
      intro i
      by_cases hi : i ∈ s
      · simp only [hi, if_true, mul_ite, mul_zero]
        rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]
      · simp [hi]
    simp only [inner]
    rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  have e2 : ∑ i ∈ s ∪ t, ‖(if i ∈ s then w i else 0)‖ ^ 2 = ∑ i ∈ s, ‖w i‖ ^ 2 := by
    have : ∀ i, ‖(if i ∈ s then w i else 0)‖ ^ 2 = if i ∈ s then ‖w i‖ ^ 2 else 0 := by
      intro i
      by_cases hi : i ∈ s <;> simp [hi]
    simp only [this]
    rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  have e3 : ∑ j ∈ s ∪ t, ‖(if j ∈ t then z j else 0)‖ ^ 2 = ∑ j ∈ t, ‖z j‖ ^ 2 := by
    have : ∀ j, ‖(if j ∈ t then z j else 0)‖ ^ 2 = if j ∈ t then ‖z j‖ ^ 2 else 0 := by
      intro j
      by_cases hj : j ∈ t <;> simp [hj]
    simp only [this]
    rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]
  rw [e1, e2, e3] at h
  exact h

/-! ### Rows of `E` as vectors of `ℓ²`, and the operator -/

private lemma row_sum_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i : I)
    (s : Finset I) : ∑ j ∈ s, ‖E i j‖ ^ 2 ≤ 1 := by
  have h := eff_cs2 hE {i} s (fun _ => 1) (fun j => star (E i j))
  simp only [Finset.sum_singleton, star_one, one_mul, norm_one, one_pow, norm_star] at h
  have e : ∑ j ∈ s, E i j * star (E i j) = ((∑ j ∈ s, ‖E i j‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have hT : 0 ≤ ∑ j ∈ s, ‖E i j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  rw [e, Complex.norm_real, Real.norm_of_nonneg hT] at h
  by_contra hc
  rw [not_le] at hc
  nlinarith

/-- The conjugated `i`-th row of `E`, a vector of norm at most one. -/
private def rowVec {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i : I) : Hilbert I :=
  ⟨fun j => star (E i j), memℓp_gen' (C := 1) fun s => by simpa using row_sum_le hE i s⟩

private lemma rowVec_apply {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i j : I) :
    rowVec hE i j = star (E i j) := rfl

/-- `⟨rowᵢ, z⟩ = ∑ⱼ Eᵢⱼ zⱼ`. -/
private lemma hasSum_row {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i : I)
    (z : Hilbert I) : HasSum (fun j => E i j * z j) (inner ℂ (rowVec hE i) z) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (rowVec hE i) z
  have e : (fun j => inner ℂ (rowVec hE i j) (z j)) = fun j => E i j * z j := by
    funext j
    rw [RCLike.inner_apply, rowVec_apply, Complex.star_def, starRingEnd_self_apply, mul_comm]
  rwa [e] at h

/-- Bessel-type bound: `∑_{i ∈ s} |⟨rowᵢ, z⟩|² ≤ ‖z‖²`. -/
private lemma coord_bound {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E)
    (z : Hilbert I) (s : Finset I) : ∑ i ∈ s, ‖inner ℂ (rowVec hE i) z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  set c : I → ℂ := fun i => inner ℂ (rowVec hE i) z with hc
  set T : ℝ := ∑ i ∈ s, ‖c i‖ ^ 2 with hTdef
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => by positivity
  -- `T = ∑ⱼ (∑_{i ∈ s} conj(cᵢ) Eᵢⱼ) zⱼ`
  have hsum : HasSum (fun j => ∑ i ∈ s, star (c i) * (E i j * z j)) ((T : ℝ) : ℂ) := by
    have h := hasSum_sum (s := s) (f := fun i j => star (c i) * (E i j * z j))
      (a := fun i => star (c i) * c i) fun i _ => (hasSum_row hE i z).mul_left (star (c i))
    have e : ∑ i ∈ s, star (c i) * c i = ((T : ℝ) : ℂ) := by
      rw [hTdef]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rwa [e] at h
  -- every partial sum is bounded by Cauchy–Schwarz
  have hpart : ∀ t : Finset I, ‖∑ j ∈ t, ∑ i ∈ s, star (c i) * (E i j * z j)‖ ^ 2 ≤ T * ‖z‖ ^ 2 := by
    intro t
    have h := eff_cs2 hE s t c z
    have e : ∑ j ∈ t, ∑ i ∈ s, star (c i) * (E i j * z j) = ∑ i ∈ s, ∑ j ∈ t, star (c i) * E i j * z j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hT)
    have h2 := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) z t
    simpa using h2
  have hlim : ‖((T : ℝ) : ℂ)‖ ^ 2 ≤ T * ‖z‖ ^ 2 := by
    have htend : Tendsto (fun t : Finset I => ‖∑ j ∈ t, ∑ i ∈ s, star (c i) * (E i j * z j)‖ ^ 2)
        atTop (𝓝 (‖((T : ℝ) : ℂ)‖ ^ 2)) := (hsum.norm.pow 2)
    exact le_of_tendsto htend (Eventually.of_forall hpart)
  rw [Complex.norm_real, Real.norm_of_nonneg hT] at hlim
  -- `T² ≤ T ‖z‖²` gives `T ≤ ‖z‖²`
  rcases hT.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have : T * T ≤ T * ‖z‖ ^ 2 := by simpa [sq] using hlim
    exact le_of_mul_le_mul_left this hpos

/-- The operator of `E` on `ℓ²`, coordinatewise `(F z)ᵢ = ∑ⱼ Eᵢⱼ zⱼ`. -/
private def opFun {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (z : Hilbert I) :
    Hilbert I :=
  ⟨fun i => inner ℂ (rowVec hE i) z, memℓp_gen' (C := ‖z‖ ^ 2) fun s => by simpa using coord_bound hE z s⟩

private lemma opFun_apply {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E)
    (z : Hilbert I) (i : I) : opFun hE z i = inner ℂ (rowVec hE i) z := rfl

private lemma norm_opFun_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E)
    (z : Hilbert I) : ‖opFun hE z‖ ≤ ‖z‖ := by
  refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) (by norm_num) (norm_nonneg z) fun s => ?_
  simpa [opFun_apply] using coord_bound hE z s

private def opLin {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) :
    Hilbert I →ₗ[ℂ] Hilbert I where
  toFun := opFun hE
  map_add' x y := by
    ext i
    simp [opFun_apply]
  map_smul' a x := by
    ext i
    simp [opFun_apply]

private def opCLM {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) :
    Hilbert I →L[ℂ] Hilbert I :=
  (opLin hE).mkContinuous 1 fun z => by
    rw [one_mul]
    exact norm_opFun_le hE z

private lemma opCLM_apply {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E)
    (z : Hilbert I) (i : I) : opCLM hE z i = inner ℂ (rowVec hE i) z := rfl

private lemma norm_opCLM_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) :
    ‖opCLM hE‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

private lemma opCLM_entry {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) (i j : I) :
    inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (opCLM hE (lp.single 2 j (1 : ℂ))) = E i j := by
  rw [lp.inner_single_left, opCLM_apply, lp.inner_single_right, rowVec_apply]
  simp

/-! ### Positivity -/

/-- The vector with coordinates `g i` for `i ∈ s` and `0` elsewhere. -/
private def finVec {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) : Hilbert I :=
  ∑ i ∈ s, lp.single 2 i (g i)

private lemma finVec_apply {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) (j : I) :
    finVec s g j = if j ∈ s then g j else 0 := by
  unfold finVec
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  exact Finset.sum_pi_single j (fun i => g i) s

private lemma opCLM_finVec_apply {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E)
    (s : Finset I) (g : I → ℂ) (i : I) : opCLM hE (finVec s g) i = ∑ j ∈ s, E i j * g j := by
  have h1 := hasSum_row hE i (finVec s g)
  have h2 : HasSum (fun j => E i j * finVec s g j) (∑ j ∈ s, E i j * finVec s g j) :=
    hasSum_sum_of_ne_finset_zero fun j hj => by simp [finVec_apply, hj]
  rw [opCLM_apply, h1.unique h2]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [finVec_apply, hj]

/-- On finitely supported vectors `⟨F v, v⟩` is the (conjugated) quadratic form of `E`. -/
private lemma inner_opCLM_finVec {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E)
    (s : Finset I) (g : I → ℂ) :
    inner ℂ (opCLM hE (finVec s g)) (finVec s g) =
      star (∑ i ∈ s, ∑ j ∈ s, star (g i) * E i j * g j) := by
  have h1 := lp.hasSum_inner (𝕜 := ℂ) (opCLM hE (finVec s g)) (finVec s g)
  have h2 : HasSum (fun i => inner ℂ (opCLM hE (finVec s g) i) (finVec s g i))
      (∑ i ∈ s, inner ℂ (opCLM hE (finVec s g) i) (finVec s g i)) :=
    hasSum_sum_of_ne_finset_zero fun i hi => by simp [finVec_apply, hi]
  rw [h1.unique h2, star_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [opCLM_finVec_apply, finVec_apply, if_pos hi, RCLike.inner_apply, star_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul', Complex.star_def, map_mul, starRingEnd_self_apply]
  ring

private lemma opCLM_isPositive {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffBound E) :
    (opCLM hE).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  -- the set of real non-negative complex numbers is closed
  have hclosed : IsClosed {c : ℂ | c.im = 0 ∧ 0 ≤ c.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  -- finite truncations converge to `x`
  have hx : Tendsto (fun s : Finset I => finVec s x) atTop (𝓝 x) := by
    simpa [HasSum, finVec] using lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x
  have hlim : Tendsto (fun s : Finset I => inner ℂ (opCLM hE (finVec s x)) (finVec s x)) atTop
      (𝓝 (inner ℂ (opCLM hE x) x)) :=
    (((opCLM hE).continuous.tendsto x).comp hx).inner hx
  have hmem : inner ℂ (opCLM hE x) x ∈ {c : ℂ | c.im = 0 ∧ 0 ≤ c.re} := by
    refine hclosed.mem_of_tendsto hlim (Eventually.of_forall fun s => ?_)
    have h := hE s x
    rw [Set.mem_ofPred_eq, inner_opCLM_finVec]
    simp only [Complex.star_def, Complex.conj_im, Complex.conj_re, neg_eq_zero]
    exact ⟨h.1, h.2.1⟩
  exact ⟨Complex.ext rfl (by simpa using hmem.1.symm), hmem.2⟩

/-! ### The statement -/

theorem solution {I : Type} [DecidableEq I] (E : Matrix I I ℂ)
    (hE : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2) :
    ∃ F : Hilbert I →L[ℂ] Hilbert I, ‖F‖ ≤ 1 ∧ F.IsPositive ∧
      (∀ (z : Hilbert I) (i : I), HasSum (fun j => E i j * z j) (F z i)) ∧
      ∀ i j, inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ))) = E i j :=
  ⟨opCLM hE, norm_opCLM_le hE, opCLM_isPositive hE, fun z i => hasSum_row hE i z, opCLM_entry hE⟩
