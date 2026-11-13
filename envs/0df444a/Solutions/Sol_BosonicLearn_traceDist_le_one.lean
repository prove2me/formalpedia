-- Prove2me | solution 1 for BosonicLearn.traceDist_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T04:03:10.984202+00:00
-- url     : https://prove2.me/submissions/972adb7a-7c5f-41fe-9cdd-7800078a4ae3

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open scoped ENNReal

open BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsDensity IsTraceClass)
open QAlgorithms.RealRegisters (Hilbert)
open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Rank-one representations with a countable index set -/

/-- `NucRep X w`: the matrix `X` is a sum `∑ₐ |Lₐ⟩⟨Rₐ|` over a countable index set, with total weight
`∑ₐ ‖Lₐ‖‖Rₐ‖ = w`. -/
private def NucRep {I : Type} (X : Matrix I I ℂ) (w : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (L R : ι → Hilbert I),
    HasSum (fun a => ‖L a‖ * ‖R a‖) w ∧ ∀ i j, HasSum (fun a => L a i * star (R a j)) (X i j)

/-- A representation of weight `w` bounds the trace size by `w`: re-index it by `ℕ`. -/
private lemma rep_traceSize {I : Type} {X : Matrix I I ℂ} {w : ℝ} (h : NucRep X w) :
    traceSize X ≤ ENNReal.ofReal w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := h
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  have key1 : (fun n => ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖) =
      Function.extend g (fun a => ‖L a‖ * ‖R a‖) 0 := by
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  have key2 : ∀ i j, (fun n => (Function.extend g L 0 n) i * star ((Function.extend g R 0 n) j)) =
      Function.extend g (fun a => L a i * star (R a j)) 0 := by
    intro i j
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  let e : NuclearExpansion X :=
    { left := Function.extend g L 0
      right := Function.extend g R 0
      summable := by
        rw [key1]
        exact (summable_extend_zero hg).mpr hw.summable
      coefficients := by
        intro i j
        rw [key2 i j, tsum_extend_zero hg]
        exact (hX i j).tsum_eq.symm }
  refine (iInf_le _ e).trans (le_of_eq ?_)
  congr 1
  show ∑' n, ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖ = w
  rw [key1, tsum_extend_zero hg]
  exact hw.tsum_eq

private lemma rep_add {I : Type} {X Y : Matrix I I ℂ} {w v : ℝ} (hX : NucRep X w) (hY : NucRep Y v) :
    NucRep (X + Y) (w + v) := by
  obtain ⟨ι₁, hι₁, L₁, R₁, hw, hX⟩ := hX
  obtain ⟨ι₂, hι₂, L₂, R₂, hv, hY⟩ := hY
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim L₁ L₂, Sum.elim R₁ R₂, ?_, fun i j => ?_⟩
  · exact HasSum.sum (f := fun a => ‖Sum.elim L₁ L₂ a‖ * ‖Sum.elim R₁ R₂ a‖) hw hv
  · exact HasSum.sum (f := fun a => Sum.elim L₁ L₂ a i * star (Sum.elim R₁ R₂ a j)) (hX i j) (hY i j)

private lemma rep_neg {I : Type} {X : Matrix I I ℂ} {w : ℝ} (hX : NucRep X w) : NucRep (-X) w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := hX
  refine ⟨ι, hι, fun a => -L a, R, ?_, fun i j => ?_⟩
  · simpa using hw
  · have h := (hX i j).neg
    simpa [neg_mul] using h

/-- A countable family with summable weights represents the matrix of its entrywise sums. -/
private lemma rep_of_family {I ι : Type} [Countable ι] (L R : ι → Hilbert I)
    (hs : Summable fun a => ‖L a‖ * ‖R a‖) :
    NucRep (fun i j => ∑' a, L a i * star (R a j)) (∑' a, ‖L a‖ * ‖R a‖) := by
  refine ⟨ι, inferInstance, L, R, hs.hasSum, fun i j => ?_⟩
  have h : Summable fun a => L a i * star (R a j) := by
    refine Summable.of_norm_bounded hs fun a => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (L a) i)
      (lp.norm_apply_le_norm (by norm_num) (R a) j) (norm_nonneg _) (norm_nonneg _)
  exact h.hasSum

/-! ### Vectors supported on a finite set, and truncation -/

/-- The vector with coordinates `g i` for `i ∈ F` and `0` elsewhere. -/
private def finVec {I : Type} (F : Finset I) (g : I → ℂ) : Hilbert I := ∑ i ∈ F, lp.single 2 i (g i)

private lemma fin_apply {I : Type} (F : Finset I) (g : I → ℂ) (j : I) :
    finVec F g j = if j ∈ F then g j else 0 := by
  unfold finVec
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  exact Finset.sum_pi_single j (fun i => g i) F

private lemma norm_fin_sq {I : Type} (F : Finset I) (g : I → ℂ) :
    ‖finVec F g‖ ^ 2 = ∑ i ∈ F, ‖g i‖ ^ 2 := by
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (E := fun _ : I => ℂ) (by norm_num) g F
  simpa [finVec] using h

private lemma norm_fin_le {I : Type} (F : Finset I) (f : Hilbert I) : ‖finVec F f‖ ≤ ‖f‖ := by
  have h := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) f F
  have h2 : ‖finVec F f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_fin_sq]
    simpa using h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

private lemma norm_sub_fin_le {I : Type} (F : Finset I) (f : Hilbert I) : ‖f - finVec F f‖ ≤ ‖f‖ := by
  have h := lp.norm_compl_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) f F
  have h2 : ‖f - finVec F f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have h3 : ‖f - finVec F f‖ ^ 2 = ‖f‖ ^ 2 - ∑ i ∈ F, ‖f i‖ ^ 2 := by simpa [finVec] using h
    rw [h3]
    have : 0 ≤ ∑ i ∈ F, ‖f i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

private lemma tendsto_norm_sub_fin {I : Type} (f : Hilbert I) :
    Tendsto (fun F : Finset I => ‖f - finVec F f‖) atTop (𝓝 0) := by
  have h : Tendsto (fun F : Finset I => ∑ i ∈ F, lp.single 2 i (f i)) atTop (𝓝 f) := by
    simpa [HasSum] using lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp h
  simpa [finVec, norm_sub_rev] using h2

/-! ### Density operators: diagonal entries, Hermitian symmetry, finite blocks -/

private lemma density_diag {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (i : I) :
    (X i i).im = 0 ∧ 0 ≤ (X i i).re := by
  have h := hX.2.1 {i} (Pi.single i 1)
  simpa using h

private lemma density_herm {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (i j : I) :
    X j i = star (X i j) := by
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (density_diag hX i).1).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := (density_diag hX i).1
    have hjj := (density_diag hX j).1
    have h1 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)).1
    have h2 := (hX.2.1 {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)).1
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

open scoped MatrixOrder ComplexOrder in
/-- The block of a density operator on a finite set `F` is a sum of `|v⟩⟨v|` with total weight equal to its
trace: the block is a positive semidefinite matrix, hence of the form `Bᴴ B`. -/
private lemma rep_block {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (F : Finset I) :
    NucRep (fun i j => if i ∈ F ∧ j ∈ F then X i j else 0) (∑ i ∈ F, (X i i).re) := by
  let M : Matrix F F ℂ := fun a b => X a b
  have hM : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply]
      exact (density_herm hX b a).symm
    · let z : I → ℂ := fun i => if h : i ∈ F then x ⟨i, h⟩ else 0
      have h := hX.2.1 F z
      have e : star x ⬝ᵥ M.mulVec x = ∑ i ∈ F, ∑ j ∈ F, star (z i) * X i j * z j := by
        rw [← Finset.sum_coe_sort F]
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_coe_sort F]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp [z, M, mul_assoc]
      rw [e, Complex.nonneg_iff]
      exact ⟨h.2, h.1.symm⟩
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have hMB : ∀ a b : F, X a b = ∑ c, star (B c a) * B c b := by
    intro a b
    have h := congrFun (congrFun hB a) b
    simpa [M, Matrix.mul_apply, Matrix.star_apply] using h
  let g : F → I → ℂ := fun c i => if h : i ∈ F then star (B c ⟨i, h⟩) else 0
  have hg : ∀ (c : F) (i : I) (hi : i ∈ F), g c i = star (B c ⟨i, hi⟩) := by
    intro c i hi
    simp [g, hi]
  refine ⟨F, inferInstance, fun c => finVec F (g c), fun c => finVec F (g c), ?_, fun i j => ?_⟩
  · have hw : ∀ c : F, ‖finVec F (g c)‖ * ‖finVec F (g c)‖ = ∑ a : F, ‖B c a‖ ^ 2 := by
      intro c
      rw [← sq, norm_fin_sq, ← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hg c a a.2, norm_star]
    have htr : ∑ i ∈ F, (X i i).re = ∑ c : F, ∑ a : F, ‖B c a‖ ^ 2 := by
      rw [← Finset.sum_coe_sort F, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hMB a a, Complex.re_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h : star (B c a) * B c a = ((‖B c a‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        rfl
      rw [h, Complex.ofReal_re]
    rw [htr]
    have h := hasSum_fintype (fun c : F => ‖finVec F (g c)‖ * ‖finVec F (g c)‖)
    simpa only [hw] using h
  · have h := hasSum_fintype (fun c : F => finVec F (g c) i * star (finVec F (g c) j))
    convert h using 1
    simp only [fin_apply]
    by_cases hi : i ∈ F
    · by_cases hj : j ∈ F
      · simp only [hi, hj, and_self, if_true]
        rw [hMB ⟨i, hi⟩ ⟨j, hj⟩]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hg c i hi, hg c j hj, star_star]
      · simp [hi, hj]
    · simp [hi]

/-! ### The trace size of a density operator is at most one -/

/-- A density operator has rank-one representations of total weight arbitrarily close to (at most) one:
cut it to a finite block, whose weight is its trace, and control the rest by dominated convergence. -/
private lemma density_rep {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) {η : ℝ} (hη : 0 < η) :
    ∃ w, w ≤ 1 + η ∧ NucRep X w := by
  obtain ⟨e⟩ := hX.1
  have hs : Summable fun k => ‖e.left k‖ * ‖e.right k‖ := e.summable
  -- the two remainders tend to zero along finite sets
  have t1 : Tendsto (fun F : Finset I => ∑' k, ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖)
      atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (F : Finset I) k => ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖)
      (g := fun _ => (0 : ℝ)) (bound := fun k => ‖e.left k‖ * ‖e.right k‖) hs
      (fun k => by simpa using (tendsto_norm_sub_fin (e.left k)).mul_const ‖e.right k‖)
      (Eventually.of_forall fun F k => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (norm_sub_fin_le F (e.left k)) (norm_nonneg _))
    simpa using h
  have t2 : Tendsto (fun F : Finset I => ∑' k, ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖)
      atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (F : Finset I) k => ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖)
      (g := fun _ => (0 : ℝ)) (bound := fun k => ‖e.left k‖ * ‖e.right k‖) hs
      (fun k => squeeze_zero (fun F => by positivity)
        (fun F => mul_le_mul_of_nonneg_right (norm_fin_le F (e.left k)) (norm_nonneg _))
        (by simpa using (tendsto_norm_sub_fin (e.right k)).const_mul ‖e.left k‖))
      (Eventually.of_forall fun F k => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul (norm_fin_le F (e.left k)) (norm_sub_fin_le F (e.right k))
          (norm_nonneg _) (norm_nonneg _))
    simpa using h
  have hη2 : (0 : ℝ) < η / 2 := by linarith
  obtain ⟨F, hF1, hF2⟩ :=
    (((tendsto_order.1 t1).2 _ hη2).and ((tendsto_order.1 t2).2 _ hη2)).exists
  -- the three pieces
  have hs1 : Summable fun k => ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖ :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_right (norm_sub_fin_le F (e.left k)) (norm_nonneg _)) hs
  have hs2 : Summable fun k => ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖ :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul (norm_fin_le F (e.left k)) (norm_sub_fin_le F (e.right k))
        (norm_nonneg _) (norm_nonneg _)) hs
  have R0 := rep_block hX F
  have R1 := rep_of_family (fun k => e.left k - finVec F (e.left k)) e.right hs1
  have R2 := rep_of_family (fun k => finVec F (e.left k))
    (fun k => e.right k - finVec F (e.right k)) hs2
  have Rtot := rep_add (rep_add R0 R1) R2
  have hXeq : X = (fun i j => if i ∈ F ∧ j ∈ F then X i j else 0) +
      (fun i j => ∑' k, (e.left k - finVec F (e.left k)) i * star (e.right k j)) +
      (fun i j => ∑' k, finVec F (e.left k) i * star ((e.right k - finVec F (e.right k)) j)) := by
    funext i j
    have hc := e.coefficients i j
    by_cases hi : i ∈ F
    · by_cases hj : j ∈ F
      · simp [fin_apply, hi, hj]
      · simp [fin_apply, hi, hj]
        exact hc
    · simp [fin_apply, hi]
      exact hc
  have Rtot' : NucRep X (∑ i ∈ F, (X i i).re +
      (∑' k, ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖) +
      ∑' k, ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖) := by
    convert Rtot using 1
    exact hXeq
  refine ⟨_, ?_, Rtot'⟩
  have htr : ∑ i ∈ F, (X i i).re ≤ 1 := by
    rw [← hX.2.2.2]
    exact Summable.sum_le_tsum F (fun i _ => (density_diag hX i).2) hX.2.2.1
  linarith

theorem solution {I : Type} (ρ σ : State I) :
    traceDist ρ.coefficients σ.coefficients ≤ 1 := by
  unfold traceDist
  have key : traceSize (ρ.coefficients - σ.coefficients) ≤ 2 := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
    obtain ⟨w₁, hw₁, R₁⟩ := density_rep ρ.density hε2
    obtain ⟨w₂, hw₂, R₂⟩ := density_rep σ.density hε2
    have R := rep_add R₁ (rep_neg R₂)
    rw [← sub_eq_add_neg] at R
    refine (rep_traceSize R).trans ?_
    have h : w₁ + w₂ ≤ 2 + (ε : ℝ) := by linarith
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by norm_num) ε.coe_nonneg]
    simp
  calc traceSize (ρ.coefficients - σ.coefficients) / 2 ≤ 2 / 2 := ENNReal.div_le_div_right key 2
    _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)
