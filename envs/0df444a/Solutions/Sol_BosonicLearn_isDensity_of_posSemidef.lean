-- Prove2me | solution 1 for BosonicLearn.isDensity_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:28:04.654557+00:00
-- url     : https://prove2.me/submissions/2e4656bd-eedd-4125-b70e-fcc0b7d6214d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal ComplexOrder
open Filter Topology

noncomputable section

/-! ### Elementary consequences of positivity of the finite quadratic forms -/

/-- All finite quadratic forms of `X` are real and non-negative, the diagonal is summable with sum `1`. -/
private structure PsdTr {I : Type} (X : Matrix I I ℂ) : Prop where
  psd : ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re
  summ : Summable (fun i => (X i i).re)
  tr : ∑' i, (X i i).re = 1

private lemma psd_diag_im {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i : I) :
    (X i i).im = 0 := by
  have h1 := (h.psd {i} (Pi.single i 1)).1
  simpa using h1

private lemma psd_diag_nonneg {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i : I) :
    0 ≤ (X i i).re := by
  have h1 := (h.psd {i} (Pi.single i 1)).2
  simpa using h1

/-- `X` is Hermitian: polarize the reality of the quadratic forms on `{i, j}`. -/
private lemma psd_herm {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i j : I) :
    X j i = star (X i j) := by
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (psd_diag_im h i)).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := psd_diag_im h i
    have hjj := psd_diag_im h j
    have h1 := (h.psd {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (h.psd {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-- The two-point Cauchy–Schwarz inequality `|X i j|² ≤ X i i * X j j`. -/
private lemma psd_cs {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i j : I) :
    ‖X i j‖ ^ 2 ≤ (X i i).re * (X j j).re := by
  by_cases hij : i = j
  · subst hij
    have him := psd_diag_im h i
    have : ‖X i i‖ ^ 2 = (X i i).re * (X i i).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
      ring
    rw [this]
  · have hji : j ≠ i := fun h => hij h.symm
    have ha := psd_diag_nonneg h i
    have hc := psd_diag_nonneg h j
    have hai := psd_diag_im h i
    have hci := psd_diag_im h j
    have hh := psd_herm h i j
    set a := (X i i).re with ha_def
    set c := (X j j).re with hc_def
    set t := ‖X i j‖ ^ 2 with ht_def
    have ht : 0 ≤ t := by positivity
    -- the quadratic form at `z i = X i j`, `z j = -l`
    have key : ∀ l : ℝ, 0 ≤ t * a - 2 * l * t + l ^ 2 * c := by
      intro l
      have h1 := (h.psd {i, j} (fun k => if k = i then X i j else if k = j then -(l : ℂ) else 0)).2
      rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij] at h1
      simp only [if_true, hji, if_false, hh] at h1
      have e : (star (X i j) * X i i * X i j + star (X i j) * X i j * -(l : ℂ) +
          (star (-(l : ℂ)) * star (X i j) * X i j + star (-(l : ℂ)) * X j j * -(l : ℂ))).re =
          t * a - 2 * l * t + l ^ 2 * c := by
        have e1 : star (X i j) * X i j = ((t : ℝ) : ℂ) := by
          rw [ht_def, Complex.star_def, Complex.conj_mul']
          push_cast
          rfl
        have e2 : X i i = ((a : ℝ) : ℂ) := Complex.ext rfl (by simpa using hai)
        have e3 : X j j = ((c : ℝ) : ℂ) := Complex.ext rfl (by simpa using hci)
        have e4 : star (X i j) * X i i * X i j = ((t * a : ℝ) : ℂ) := by
          rw [mul_right_comm, e1, e2]
          push_cast
          ring
        rw [e4, e1, mul_assoc (star (-(l : ℂ))), e1, e3]
        simp
        ring
      rw [e] at h1
      exact h1
    rcases ha.eq_or_lt with ha0 | hapos
    · -- `a = 0`
      rw [← ha0, zero_mul]
      by_contra hcon
      rw [not_le] at hcon
      have h1 := key (t / (c + 1))
      rw [← ha0] at h1
      have hc1 : 0 < c + 1 := by linarith
      have h2 : t * 0 - 2 * (t / (c + 1)) * t + (t / (c + 1)) ^ 2 * c =
          -(t ^ 2 * (c + 2)) / (c + 1) ^ 2 := by
        field_simp
        ring
      rw [h2] at h1
      have h3 : -(t ^ 2 * (c + 2)) / (c + 1) ^ 2 < 0 := by
        apply div_neg_of_neg_of_pos
        · have : 0 < t ^ 2 * (c + 2) := by positivity
          linarith
        · positivity
      linarith
    · have h1 := key a
      have h2 : t * a - 2 * a * t + a ^ 2 * c = a * (a * c - t) := by ring
      rw [h2] at h1
      have h3 : 0 ≤ a * c - t := by
        by_contra hcon
        rw [not_le] at hcon
        have := mul_neg_of_pos_of_neg hapos hcon
        linarith
      linarith

private lemma diag_sum_le {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (s : Finset I) :
    ∑ i ∈ s, (X i i).re ≤ 1 := by
  rw [← h.tr]
  exact h.summ.sum_le_tsum s fun i _ => psd_diag_nonneg h i

/-! ### Rows of `X` as vectors of `ℓ²`, and the operator -/

private lemma row_sum_le {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i : I)
    (s : Finset I) : ∑ j ∈ s, ‖X i j‖ ^ 2 ≤ (X i i).re := by
  calc ∑ j ∈ s, ‖X i j‖ ^ 2 ≤ ∑ j ∈ s, (X i i).re * (X j j).re :=
        Finset.sum_le_sum fun j _ => psd_cs h i j
    _ = (X i i).re * ∑ j ∈ s, (X j j).re := by rw [Finset.mul_sum]
    _ ≤ (X i i).re * 1 := mul_le_mul_of_nonneg_left (diag_sum_le h s) (psd_diag_nonneg h i)
    _ = (X i i).re := mul_one _

/-- The conjugated `i`-th row of `X`. -/
private def rowVec {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i : I) : Hilbert I :=
  ⟨fun j => star (X i j), memℓp_gen' (C := (X i i).re) fun s => by simpa using row_sum_le h i s⟩

private lemma rowVec_apply {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i j : I) :
    rowVec h i j = star (X i j) := rfl

private lemma norm_rowVec_sq_le {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i : I) :
    ‖rowVec h i‖ ^ 2 ≤ (X i i).re := by
  have h1 := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (rowVec h i)
  have h2 : ‖rowVec h i‖ ^ (2 : ℝ≥0∞).toReal ≤ (X i i).re :=
    hasSum_le_of_sum_le h1 fun s => by
      simpa [rowVec_apply] using row_sum_le h i s
  simpa using h2

/-- `⟨rowᵢ, z⟩ = ∑ⱼ Xᵢⱼ zⱼ`. -/
private lemma hasSum_row {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i : I)
    (z : Hilbert I) : HasSum (fun j => X i j * z j) (inner ℂ (rowVec h i) z) := by
  have h1 := lp.hasSum_inner (𝕜 := ℂ) (rowVec h i) z
  have e : (fun j => inner ℂ (rowVec h i j) (z j)) = fun j => X i j * z j := by
    funext j
    rw [RCLike.inner_apply, rowVec_apply, Complex.star_def, starRingEnd_self_apply, mul_comm]
  rwa [e] at h1

/-- `∑_{i ∈ s} |⟨rowᵢ, z⟩|² ≤ ‖z‖²` (Hilbert–Schmidt bound). -/
private lemma coord_bound {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X)
    (z : Hilbert I) (s : Finset I) : ∑ i ∈ s, ‖inner ℂ (rowVec h i) z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have h1 : ∀ i, ‖inner ℂ (rowVec h i) z‖ ^ 2 ≤ (X i i).re * ‖z‖ ^ 2 := by
    intro i
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (rowVec h i) z
    calc ‖inner ℂ (rowVec h i) z‖ ^ 2 ≤ (‖rowVec h i‖ * ‖z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = ‖rowVec h i‖ ^ 2 * ‖z‖ ^ 2 := mul_pow _ _ _
      _ ≤ (X i i).re * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_rowVec_sq_le h i) (by positivity)
  calc ∑ i ∈ s, ‖inner ℂ (rowVec h i) z‖ ^ 2 ≤ ∑ i ∈ s, (X i i).re * ‖z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = (∑ i ∈ s, (X i i).re) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]
    _ ≤ 1 * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right (diag_sum_le h s) (by positivity)
    _ = ‖z‖ ^ 2 := one_mul _

/-- The operator of `X` on `ℓ²`, coordinatewise `(A z)ᵢ = ∑ⱼ Xᵢⱼ zⱼ`. -/
private def opFun {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (z : Hilbert I) :
    Hilbert I :=
  ⟨fun i => inner ℂ (rowVec h i) z, memℓp_gen' (C := ‖z‖ ^ 2) fun s => by simpa using coord_bound h z s⟩

private lemma opFun_apply {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X)
    (z : Hilbert I) (i : I) : opFun h z i = inner ℂ (rowVec h i) z := rfl

private lemma norm_opFun_le {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X)
    (z : Hilbert I) : ‖opFun h z‖ ≤ ‖z‖ := by
  refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) (by norm_num) (norm_nonneg z) fun s => ?_
  simpa [opFun_apply] using coord_bound h z s

private def opLin {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) :
    Hilbert I →ₗ[ℂ] Hilbert I where
  toFun := opFun h
  map_add' x y := by
    ext i
    simp [opFun_apply]
  map_smul' a x := by
    ext i
    simp [opFun_apply]

private def opCLM {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) :
    Hilbert I →L[ℂ] Hilbert I :=
  (opLin h).mkContinuous 1 fun z => by
    rw [one_mul]
    exact norm_opFun_le h z

private lemma opCLM_apply {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X)
    (z : Hilbert I) (i : I) : opCLM h z i = inner ℂ (rowVec h i) z := rfl

private lemma opCLM_entry {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) (i j : I) :
    inner ℂ (lp.single 2 i (1 : ℂ) : Hilbert I) (opCLM h (lp.single 2 j (1 : ℂ))) = X i j := by
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

private lemma opCLM_finVec_apply {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X)
    (s : Finset I) (g : I → ℂ) (i : I) : opCLM h (finVec s g) i = ∑ j ∈ s, X i j * g j := by
  have h1 := hasSum_row h i (finVec s g)
  have h2 : HasSum (fun j => X i j * finVec s g j) (∑ j ∈ s, X i j * finVec s g j) :=
    hasSum_sum_of_ne_finset_zero fun j hj => by simp [finVec_apply, hj]
  rw [opCLM_apply, h1.unique h2]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [finVec_apply, hj]

/-- On finitely supported vectors `⟨A v, v⟩` is the (conjugated) quadratic form of `X`. -/
private lemma inner_opCLM_finVec {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X)
    (s : Finset I) (g : I → ℂ) :
    inner ℂ (opCLM h (finVec s g)) (finVec s g) =
      star (∑ i ∈ s, ∑ j ∈ s, star (g i) * X i j * g j) := by
  have h1 := lp.hasSum_inner (𝕜 := ℂ) (opCLM h (finVec s g)) (finVec s g)
  have h2 : HasSum (fun i => inner ℂ (opCLM h (finVec s g) i) (finVec s g i))
      (∑ i ∈ s, inner ℂ (opCLM h (finVec s g) i) (finVec s g i)) :=
    hasSum_sum_of_ne_finset_zero fun i hi => by simp [finVec_apply, hi]
  rw [h1.unique h2, star_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [opCLM_finVec_apply, finVec_apply, if_pos hi, RCLike.inner_apply, star_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul', Complex.star_def, map_mul, starRingEnd_self_apply]
  ring

private lemma opCLM_isPositive {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (h : PsdTr X) :
    (opCLM h).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  -- the set of real non-negative complex numbers is closed
  have hclosed : IsClosed {c : ℂ | c.im = 0 ∧ 0 ≤ c.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  -- finite truncations converge to `x`
  have hx : Tendsto (fun s : Finset I => finVec s x) atTop (𝓝 x) := by
    simpa [HasSum, finVec] using lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x
  have hlim : Tendsto (fun s : Finset I => inner ℂ (opCLM h (finVec s x)) (finVec s x)) atTop
      (𝓝 (inner ℂ (opCLM h x) x)) :=
    (((opCLM h).continuous.tendsto x).comp hx).inner hx
  have hmem : inner ℂ (opCLM h x) x ∈ {c : ℂ | c.im = 0 ∧ 0 ≤ c.re} := by
    refine hclosed.mem_of_tendsto hlim (Eventually.of_forall fun s => ?_)
    have h3 := h.psd s x
    rw [Set.mem_ofPred_eq, inner_opCLM_finVec]
    simp only [Complex.star_def, Complex.conj_im, Complex.conj_re, neg_eq_zero]
    exact ⟨h3.1, h3.2⟩
  exact ⟨Complex.ext rfl (by simpa using hmem.1.symm), hmem.2⟩

/-! ### Square root -/

/-- A positive operator on a complex Hilbert space has a self-adjoint square root. -/
private lemma exists_sqrt_op {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : A.IsPositive) :
    ∃ B : H →L[ℂ] H, (∀ x y, inner ℂ (B x) y = inner ℂ x (B y)) ∧ ∀ x, B (B x) = A x := by
  have h0 : 0 ≤ A := (ContinuousLinearMap.nonneg_iff_isPositive A).mpr hA
  have hsa : IsSelfAdjoint (CFC.sqrt A) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hmul : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  refine ⟨CFC.sqrt A, fun x y => ?_, fun x => ?_⟩
  · have h := ContinuousLinearMap.adjoint_inner_left (CFC.sqrt A) y x
    rw [hsa.adjoint_eq] at h
    exact h
  · conv_rhs => rw [← hmul]
    rfl

/-! ### Nuclear expansions from countable families -/

/-- A countable rank-one family with summable weights gives a nuclear expansion. -/
private lemma isTraceClass_of_family {I ι : Type} [Countable ι] {X : Matrix I I ℂ}
    (L R : ι → Hilbert I) (hw : Summable fun a => ‖L a‖ * ‖R a‖)
    (hX : ∀ i j, HasSum (fun a => L a i * star (R a j)) (X i j)) : IsTraceClass X := by
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  have key1 : (fun k => ‖Function.extend g L 0 k‖ * ‖Function.extend g R 0 k‖) =
      Function.extend g (fun a => ‖L a‖ * ‖R a‖) 0 := by
    funext k
    by_cases hk : ∃ a, g a = k
    · obtain ⟨a, rfl⟩ := hk
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hk]
  have key2 : ∀ i j, (fun k => (Function.extend g L 0 k) i * star ((Function.extend g R 0 k) j)) =
      Function.extend g (fun a => L a i * star (R a j)) 0 := by
    intro i j
    funext k
    by_cases hk : ∃ a, g a = k
    · obtain ⟨a, rfl⟩ := hk
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hk]
  exact ⟨{ left := Function.extend g L 0
           right := Function.extend g R 0
           summable := by
             rw [key1]
             exact (summable_extend_zero hg).mpr hw
           coefficients := by
             intro i j
             rw [key2 i j, tsum_extend_zero hg]
             exact (hX i j).tsum_eq.symm }⟩

/-- Trace class from positivity and a summable diagonal: `X i j = ∑ₘ (B eₘ) i * conj ((B eₘ) j)` with
`B = X^{1/2}`. -/
private lemma isTraceClass_of_psdTr {I : Type} [Countable I] [DecidableEq I] {X : Matrix I I ℂ}
    (h : PsdTr X) : IsTraceClass X := by
  obtain ⟨B, hBsa, hBB⟩ := exists_sqrt_op (opCLM h) (opCLM_isPositive h)
  have hentry : ∀ i j, inner ℂ (B (lp.single 2 i (1 : ℂ))) (B (lp.single 2 j (1 : ℂ))) = X i j := by
    intro i j
    rw [hBsa, hBB, opCLM_entry]
  have hcoord : ∀ m i, (B (lp.single 2 i (1 : ℂ))) m = star ((B (lp.single 2 m (1 : ℂ))) i) := by
    intro m i
    have h1 : inner ℂ (lp.single 2 m (1 : ℂ) : Hilbert I) (B (lp.single 2 i (1 : ℂ))) =
        (B (lp.single 2 i (1 : ℂ))) m := by
      rw [lp.inner_single_left]
      simp
    have h2 : inner ℂ (B (lp.single 2 m (1 : ℂ))) (lp.single 2 i (1 : ℂ) : Hilbert I) =
        star ((B (lp.single 2 m (1 : ℂ))) i) := by
      rw [lp.inner_single_right]
      simp
    rw [← h1, ← hBsa, h2]
  refine isTraceClass_of_family (ι := I) (fun m => B (lp.single 2 m (1 : ℂ)))
    (fun m => B (lp.single 2 m (1 : ℂ))) ?_ ?_
  · refine h.summ.congr fun m => ?_
    have h1 := hentry m m
    rw [inner_self_eq_norm_sq_to_K] at h1
    rw [← h1]
    simp [sq]
  · intro i j
    have hs := lp.hasSum_inner (𝕜 := ℂ) (B (lp.single 2 i (1 : ℂ))) (B (lp.single 2 j (1 : ℂ)))
    rw [hentry] at hs
    refine hs.congr_fun fun m => ?_
    rw [RCLike.inner_apply, hcoord m i, hcoord m j, Complex.star_def,
      starRingEnd_self_apply, mul_comm]

/-! ### The statement -/

theorem solution {I : Type} [Countable I] (X : Matrix I I ℂ)
    (hpsd : ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re)
    (hsum : Summable (fun i => (X i i).re)) (htr : ∑' i, (X i i).re = 1) : IsDensity X := by
  classical
  exact ⟨isTraceClass_of_psdTr ⟨hpsd, hsum, htr⟩, hpsd, hsum, htr⟩
