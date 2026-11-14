-- Prove2me | solution 1 for BosonicLearn.density_tendsto_of_entrywise
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T09:44:07.80945+00:00
-- url     : https://prove2.me/submissions/e99a797c-9b6f-428e-85de-3862d7032063

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity traceSize NuclearExpansion IsTraceClass)
open QAlgorithms.RealRegisters (Hilbert)
open Filter Topology
open scoped ENNReal

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

/-- A nuclear expansion is a representation with the same weight. -/
private lemma rep_of_expansion {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    NucRep X (∑' n, ‖e.left n‖ * ‖e.right n‖) := by
  refine ⟨ℕ, inferInstance, e.left, e.right, e.summable.hasSum, fun i j => ?_⟩
  rw [e.coefficients i j]
  have h : Summable fun a => e.left a i * star (e.right a j) := by
    refine Summable.of_norm_bounded e.summable fun a => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (e.left a) i)
      (lp.norm_apply_le_norm (by norm_num) (e.right a) j) (norm_nonneg _) (norm_nonneg _)
  exact h.hasSum

/-- Subadditivity of the trace norm. -/
private lemma traceSize_add_le {I : Type} (X Y : Matrix I I ℂ) :
    traceSize (X + Y) ≤ traceSize X + traceSize Y := by
  have key : ∀ (eX : NuclearExpansion X) (eY : NuclearExpansion Y), traceSize (X + Y) ≤
      ENNReal.ofReal (∑' n, ‖eX.left n‖ * ‖eX.right n‖) +
        ENNReal.ofReal (∑' n, ‖eY.left n‖ * ‖eY.right n‖) := by
    intro eX eY
    refine (rep_traceSize (rep_add (rep_of_expansion eX) (rep_of_expansion eY))).trans ?_
    rw [ENNReal.ofReal_add (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  show traceSize (X + Y) ≤
    (⨅ e : NuclearExpansion X, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)) +
      ⨅ e : NuclearExpansion Y, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)
  rw [ENNReal.iInf_add]
  refine le_iInf fun eX => ?_
  rw [ENNReal.add_iInf]
  exact le_iInf fun eY => key eX eY

private lemma rep_neg {I : Type} {X : Matrix I I ℂ} {w : ℝ} (hX : NucRep X w) : NucRep (-X) w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := hX
  refine ⟨ι, hι, fun a => -L a, R, ?_, fun i j => ?_⟩
  · simpa using hw
  · have h := (hX i j).neg
    simpa [neg_mul] using h

/-- Symmetry of the trace norm under negation. -/
private lemma traceSize_neg {I : Type} (X : Matrix I I ℂ) : traceSize (-X) = traceSize X := by
  have key : ∀ Y : Matrix I I ℂ, traceSize (-Y) ≤ traceSize Y := by
    intro Y
    show traceSize (-Y) ≤ ⨅ e : NuclearExpansion Y, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)
    exact le_iInf fun e => rep_traceSize (rep_neg (rep_of_expansion e))
  refine le_antisymm (key X) ?_
  have h := key (-X)
  rwa [neg_neg] at h

private lemma traceSize_sub_comm {I : Type} (A B : Matrix I I ℂ) :
    traceSize (A - B) = traceSize (B - A) := by
  rw [← neg_sub B A, traceSize_neg]

private lemma traceSize_sub_le {I : Type} (A B C : Matrix I I ℂ) :
    traceSize (A - C) ≤ traceSize (A - B) + traceSize (B - C) := by
  rw [← sub_add_sub_cancel A B C]
  exact traceSize_add_le _ _

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

/-- A finite family represents the matrix of its entrywise sums. -/
private lemma rep_of_fintype {I ι : Type} [Fintype ι] (L R : ι → Hilbert I) :
    NucRep (fun i j => ∑ a, L a i * star (R a j)) (∑ a, ‖L a‖ * ‖R a‖) :=
  ⟨ι, inferInstance, L, R, hasSum_fintype _, fun _ _ => hasSum_fintype _⟩

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

private lemma norm_fin_le_sum {I : Type} (F : Finset I) (g : I → ℂ) :
    ‖finVec F g‖ ≤ ∑ i ∈ F, ‖g i‖ := by
  unfold finVec
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lp.norm_single (E := fun _ : I => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) i (g i)

/-! ### Blocks of an array on a finite set of indices -/

/-- The array equal to `X` on `F × F` and zero elsewhere. -/
private def blk {I : Type} (F : Finset I) (X : Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => if i ∈ F ∧ j ∈ F then X i j else 0

private lemma blk_sub {I : Type} (F : Finset I) (X Y : Matrix I I ℂ) :
    blk F X - blk F Y = blk F (X - Y) := by
  funext i j
  by_cases hij : i ∈ F ∧ j ∈ F
  · simp [blk, hij]
  · simp [blk, hij]

/-- A finite array has trace norm at most the sum of the moduli of its entries. -/
private lemma blk_traceSize_le {I : Type} (F : Finset I) (D : Matrix I I ℂ) :
    traceSize (blk F D) ≤ ENNReal.ofReal (∑ a ∈ F, ∑ b ∈ F, ‖D a b‖) := by
  have R := rep_of_fintype (I := I) (ι := F) (fun a => lp.single 2 (a : I) (1 : ℂ))
    (fun a => finVec F (fun j => star (D a j)))
  have hEq : (fun i j => ∑ a : F, (lp.single 2 (a : I) (1 : ℂ) : Hilbert I) i *
      star (finVec F (fun j => star (D a j)) j)) = blk F D := by
    funext i j
    simp only [fin_apply, lp.single_apply]
    rw [Finset.sum_coe_sort F (fun a : I => (Pi.single a (1 : ℂ) : I → ℂ) i *
      star (if j ∈ F then star (D a j) else 0))]
    by_cases hj : j ∈ F
    · by_cases hi : i ∈ F
      · rw [Finset.sum_eq_single i]
        · simp [blk, hi, hj]
        · intro b _ hb
          simp [Ne.symm hb]
        · intro h
          exact absurd hi h
      · rw [Finset.sum_eq_zero]
        · simp [blk, hi]
        · intro b hb
          have : i ≠ b := fun h => hi (h ▸ hb)
          simp [this]
    · simp [blk, hj]
  rw [hEq] at R
  refine (rep_traceSize R).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Finset.sum_coe_sort F (fun a : I => ‖(lp.single 2 a (1 : ℂ) : Hilbert I)‖ *
    ‖finVec F (fun j => star (D a j))‖)]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [lp.norm_single (by norm_num), norm_one, one_mul]
  refine (norm_fin_le_sum F _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun b _ => norm_star _

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

private lemma density_sum_le_one {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (F : Finset I) :
    ∑ i ∈ F, (X i i).re ≤ 1 := by
  rw [← hX.2.2.2]
  exact Summable.sum_le_tsum F (fun i _ => (density_diag hX i).2) hX.2.2.1

open scoped MatrixOrder ComplexOrder in
/-- The block of a density operator on a finite set `F` is a Gram matrix: the block is a positive
semidefinite matrix, hence of the form `Bᴴ B`. -/
private lemma gram_block {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (F : Finset I) :
    ∃ g : F → I → ℂ, ∀ i ∈ F, ∀ j ∈ F, X i j = ∑ c, g c i * star (g c j) := by
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
  refine ⟨fun c i => if h : i ∈ F then star (B c ⟨i, h⟩) else 0, fun i hi j hj => ?_⟩
  rw [hMB ⟨i, hi⟩ ⟨j, hj⟩]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [hi, hj]

/-- Entries of the rank-one sums built from the Gram vectors cut to subsets of `F`. -/
private lemma gram_entry {I : Type} {X : Matrix I I ℂ} {F : Finset I} {g : F → I → ℂ}
    (hg : ∀ i ∈ F, ∀ j ∈ F, X i j = ∑ c, g c i * star (g c j)) {G G' : Finset I}
    (hG : G ⊆ F) (hG' : G' ⊆ F) (i j : I) :
    ∑ c, finVec G (g c) i * star (finVec G' (g c) j) = if i ∈ G ∧ j ∈ G' then X i j else 0 := by
  simp only [fin_apply]
  by_cases hi : i ∈ G
  · by_cases hj : j ∈ G'
    · simp only [hi, hj, and_self, if_true]
      exact (hg i (hG hi) j (hG' hj)).symm
    · simp [hi, hj]
  · simp [hi]

/-- Total squared norm of the Gram vectors cut to a subset `G` of `F`: the trace of the block on `G`. -/
private lemma gram_norm {I : Type} {X : Matrix I I ℂ} {F : Finset I} {g : F → I → ℂ}
    (hg : ∀ i ∈ F, ∀ j ∈ F, X i j = ∑ c, g c i * star (g c j)) {G : Finset I} (hG : G ⊆ F) :
    ∑ c, ‖finVec G (g c)‖ ^ 2 = ∑ i ∈ G, (X i i).re := by
  simp only [norm_fin_sq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hg i (hG hi) i (hG hi), Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h : g c i * star (g c i) = ((‖g c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

/-- **Key estimate.** For a density operator and finite sets `F ⊆ F'`, the difference of the blocks on `F'`
and on `F` has trace norm at most `2 √τ`, `τ` the diagonal mass on `F' \ F`. -/
private lemma block_diff {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) {F F' : Finset I}
    (hFF : F ⊆ F') :
    traceSize (blk F' X - blk F X) ≤ ENNReal.ofReal (2 * √(∑ i ∈ F' \ F, (X i i).re)) := by
  obtain ⟨g, hg⟩ := gram_block hX F'
  have hsd : F' \ F ⊆ F' := Finset.sdiff_subset
  have R1 := rep_of_fintype (fun c => finVec F (g c)) (fun c => finVec (F' \ F) (g c))
  have R2 := rep_of_fintype (fun c => finVec (F' \ F) (g c)) (fun c => finVec F' (g c))
  have R := rep_add R1 R2
  have hEq : (fun i j => ∑ c, finVec F (g c) i * star (finVec (F' \ F) (g c) j)) +
      (fun i j => ∑ c, finVec (F' \ F) (g c) i * star (finVec F' (g c) j)) = blk F' X - blk F X := by
    funext i j
    show ∑ c, finVec F (g c) i * star (finVec (F' \ F) (g c) j) +
      ∑ c, finVec (F' \ F) (g c) i * star (finVec F' (g c) j) = blk F' X i j - blk F X i j
    rw [gram_entry hg hFF hsd, gram_entry hg hsd (Finset.Subset.refl F')]
    simp only [blk, Finset.mem_sdiff]
    by_cases hi : i ∈ F
    · have hi' : i ∈ F' := hFF hi
      by_cases hj : j ∈ F
      · have hj' : j ∈ F' := hFF hj
        simp [hi, hi', hj, hj']
      · by_cases hj' : j ∈ F'
        · simp [hi, hi', hj, hj']
        · simp [hi, hi', hj, hj']
    · by_cases hi' : i ∈ F'
      · by_cases hj : j ∈ F
        · have hj' : j ∈ F' := hFF hj
          simp [hi, hi', hj, hj']
        · by_cases hj' : j ∈ F'
          · simp [hi, hi', hj, hj']
          · simp [hi, hi', hj, hj']
      · simp [hi, hi']
  have R' : NucRep (blk F' X - blk F X) (∑ c, ‖finVec F (g c)‖ * ‖finVec (F' \ F) (g c)‖ +
      ∑ c, ‖finVec (F' \ F) (g c)‖ * ‖finVec F' (g c)‖) := by
    convert R using 1
    exact hEq.symm
  refine (rep_traceSize R').trans (ENNReal.ofReal_le_ofReal ?_)
  set τ := ∑ i ∈ F' \ F, (X i i).re with hτ
  have hq : ∑ c, ‖finVec (F' \ F) (g c)‖ ^ 2 = τ := gram_norm hg hsd
  have hp : ∑ c, ‖finVec F (g c)‖ ^ 2 ≤ 1 := by
    rw [gram_norm hg hFF]
    exact density_sum_le_one hX F
  have hv : ∑ c, ‖finVec F' (g c)‖ ^ 2 ≤ 1 := by
    rw [gram_norm hg (Finset.Subset.refl F')]
    exact density_sum_le_one hX F'
  have c1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun c => ‖finVec F (g c)‖)
    (fun c => ‖finVec (F' \ F) (g c)‖)
  have c2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun c => ‖finVec (F' \ F) (g c)‖)
    (fun c => ‖finVec F' (g c)‖)
  simp only [hq] at c1 c2
  have s0 : 0 ≤ √τ := Real.sqrt_nonneg _
  have s1 : √(∑ c, ‖finVec F (g c)‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hp
  have s2 : √(∑ c, ‖finVec F' (g c)‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hv
  have b1 : √(∑ c, ‖finVec F (g c)‖ ^ 2) * √τ ≤ √τ := by
    calc √(∑ c, ‖finVec F (g c)‖ ^ 2) * √τ ≤ 1 * √τ := mul_le_mul_of_nonneg_right s1 s0
      _ = √τ := one_mul _
  have b2 : √τ * √(∑ c, ‖finVec F' (g c)‖ ^ 2) ≤ √τ := by
    calc √τ * √(∑ c, ‖finVec F' (g c)‖ ^ 2) ≤ √τ * 1 := mul_le_mul_of_nonneg_left s2 s0
      _ = √τ := mul_one _
  linarith

/-! ### Tails of a trace-class array -/

/-- For a trace-class array the part outside the block on `F` has small trace norm for large `F`. -/
private lemma tail_small {I : Type} {X : Matrix I I ℂ} (hX : IsTraceClass X) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ F : Finset I in atTop, traceSize (X - blk F X) ≤ ENNReal.ofReal η := by
  obtain ⟨e⟩ := hX
  have hs : Summable fun k => ‖e.left k‖ * ‖e.right k‖ := e.summable
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
  have t12 : Tendsto (fun F : Finset I => (∑' k, ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖) +
      ∑' k, ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖) atTop (𝓝 0) := by
    simpa using t1.add t2
  filter_upwards [(tendsto_order.1 t12).2 η hη] with F hF
  have hs1 : Summable fun k => ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖ :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_right (norm_sub_fin_le F (e.left k)) (norm_nonneg _)) hs
  have hs2 : Summable fun k => ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖ :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul (norm_fin_le F (e.left k)) (norm_sub_fin_le F (e.right k))
        (norm_nonneg _) (norm_nonneg _)) hs
  have R1 := rep_of_family (fun k => e.left k - finVec F (e.left k)) e.right hs1
  have R2 := rep_of_family (fun k => finVec F (e.left k))
    (fun k => e.right k - finVec F (e.right k)) hs2
  have Rtot := rep_add R1 R2
  have hXeq : X - blk F X =
      (fun i j => ∑' k, (e.left k - finVec F (e.left k)) i * star (e.right k j)) +
      (fun i j => ∑' k, finVec F (e.left k) i * star ((e.right k - finVec F (e.right k)) j)) := by
    funext i j
    have hc := e.coefficients i j
    by_cases hi : i ∈ F
    · by_cases hj : j ∈ F
      · simp [blk, fin_apply, hi, hj]
      · simp [blk, fin_apply, hi, hj]
        exact hc
    · simp [blk, fin_apply, hi]
      exact hc
  have Rtot' : NucRep (X - blk F X) ((∑' k, ‖e.left k - finVec F (e.left k)‖ * ‖e.right k‖) +
      ∑' k, ‖finVec F (e.left k)‖ * ‖e.right k - finVec F (e.right k)‖) := by
    convert Rtot using 1
    exact hXeq
  exact (rep_traceSize Rtot').trans (ENNReal.ofReal_le_ofReal hF.le)

/-- **Uniform tail bound.** For every density operator and every finite `F`, the part outside the block on
`F` has trace norm at most `2 √τ`, `τ = 1 − ∑_{i ∈ F} X_ii`. -/
private lemma tail_bound {I : Type} {X : Matrix I I ℂ} (hX : IsDensity X) (F : Finset I) :
    traceSize (X - blk F X) ≤ ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X i i).re)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨F', hF', hsmall⟩ := ((eventually_ge_atTop F).and (tail_small hX.1 hε')).exists
  have hFF : F ⊆ F' := hF'
  have hmono : ∑ i ∈ F' \ F, (X i i).re ≤ 1 - ∑ i ∈ F, (X i i).re := by
    have h1 := Finset.sum_sdiff (f := fun i => (X i i).re) hFF
    have h2 := density_sum_le_one hX F'
    linarith
  calc traceSize (X - blk F X) ≤ traceSize (X - blk F' X) + traceSize (blk F' X - blk F X) :=
        traceSize_sub_le _ _ _
    _ ≤ ENNReal.ofReal (ε : ℝ) + ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X i i).re)) := by
        refine add_le_add hsmall ((block_diff hX hFF).trans (ENNReal.ofReal_le_ofReal ?_))
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by norm_num)
    _ = ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X i i).re)) + ε := by
        rw [add_comm, ENNReal.ofReal_coe_nnreal]

theorem solution {I : Type} (X : ℕ → Matrix I I ℂ) (X₀ : Matrix I I ℂ)
    (hX : ∀ k, IsDensity (X k)) (hX₀ : IsDensity X₀)
    (h : ∀ i j, Tendsto (fun k => X k i j) atTop (𝓝 (X₀ i j))) :
    Tendsto (fun k => traceSize (X k - X₀)) atTop (𝓝 0) := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, traceSize (X k - X₀) ≤ ENNReal.ofReal ε := by
    intro ε hε
    -- choose the cutoff
    have hsum : Tendsto (fun F : Finset I => ∑ i ∈ F, (X₀ i i).re) atTop (𝓝 1) := by
      have h1 := hX₀.2.2.1.hasSum
      rw [hX₀.2.2.2] at h1
      exact h1
    have hcut : Tendsto (fun F : Finset I => 4 * √(1 - ∑ i ∈ F, (X₀ i i).re)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun F : Finset I => 4 * √(1 - ∑ i ∈ F, (X₀ i i).re)) atTop
          (𝓝 (4 * √(1 - 1))) :=
        ((Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.sub hsum)).const_mul 4
      simpa using h1
    obtain ⟨F, hF⟩ := ((tendsto_order.1 hcut).2 ε hε).exists
    -- the real bound
    have hd : Tendsto (fun k => 2 * √(1 - ∑ i ∈ F, (X k i i).re)) atTop
        (𝓝 (2 * √(1 - ∑ i ∈ F, (X₀ i i).re))) :=
      ((Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.sub
        (tendsto_finsetSum F fun i _ => (Complex.continuous_re.tendsto _).comp (h i i)))).const_mul 2
    have hm : Tendsto (fun k => ∑ a ∈ F, ∑ b ∈ F, ‖X k a b - X₀ a b‖) atTop (𝓝 0) := by
      have h0 : (0 : ℝ) = ∑ a ∈ F, ∑ b ∈ F, (0 : ℝ) := by simp
      rw [h0]
      exact tendsto_finsetSum F fun a _ => tendsto_finsetSum F fun b _ =>
        tendsto_iff_norm_sub_tendsto_zero.mp (h a b)
    have hr : Tendsto (fun k => 2 * √(1 - ∑ i ∈ F, (X k i i).re) +
        ∑ a ∈ F, ∑ b ∈ F, ‖X k a b - X₀ a b‖ + 2 * √(1 - ∑ i ∈ F, (X₀ i i).re)) atTop
        (𝓝 (2 * √(1 - ∑ i ∈ F, (X₀ i i).re) + 0 + 2 * √(1 - ∑ i ∈ F, (X₀ i i).re))) :=
      (hd.add hm).add tendsto_const_nhds
    have hlt := (tendsto_order.1 hr).2 ε (by linarith)
    filter_upwards [hlt] with k hk
    have b1 := tail_bound (hX k) F
    have b2 : traceSize (blk F (X k) - blk F X₀) ≤
        ENNReal.ofReal (∑ a ∈ F, ∑ b ∈ F, ‖X k a b - X₀ a b‖) := by
      rw [blk_sub]
      exact blk_traceSize_le F (X k - X₀)
    have b3 : traceSize (blk F X₀ - X₀) ≤ ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X₀ i i).re)) := by
      rw [traceSize_sub_comm]
      exact tail_bound hX₀ F
    have n1 : 0 ≤ 2 * √(1 - ∑ i ∈ F, (X k i i).re) := by positivity
    have n2 : 0 ≤ ∑ a ∈ F, ∑ b ∈ F, ‖X k a b - X₀ a b‖ :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
    calc traceSize (X k - X₀)
        ≤ traceSize (X k - blk F X₀) + traceSize (blk F X₀ - X₀) := traceSize_sub_le _ _ _
      _ ≤ traceSize (X k - blk F (X k)) + traceSize (blk F (X k) - blk F X₀) +
          traceSize (blk F X₀ - X₀) := add_le_add_left (traceSize_sub_le _ _ _) _
      _ ≤ ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X k i i).re)) +
          ENNReal.ofReal (∑ a ∈ F, ∑ b ∈ F, ‖X k a b - X₀ a b‖) +
          ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X₀ i i).re)) := add_le_add (add_le_add b1 b2) b3
      _ = ENNReal.ofReal (2 * √(1 - ∑ i ∈ F, (X k i i).re) +
          ∑ a ∈ F, ∑ b ∈ F, ‖X k a b - X₀ a b‖ + 2 * √(1 - ∑ i ∈ F, (X₀ i i).re)) := by
          rw [ENNReal.ofReal_add (add_nonneg n1 n2) (by positivity), ENNReal.ofReal_add n1 n2]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hk.le
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · simp [htop]
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    filter_upwards [key ε.toReal hpos] with k hk
    rwa [ENNReal.ofReal_toReal htop] at hk
