-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_5_4
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:19:02.689008+00:00
-- url     : https://prove2.me/submissions/9eb6c17e-36c0-4581-b116-37c592928e0d

import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_GEPPGrowth_Main_lemma_4_13
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GEPPGrowth.Main.Prop54

open GEPPGrowth.Main

/-! ### One-dimensional Gaussian bound: `P(Z² ≥ 1/2) ≥ 0.47` -/

lemma gauss_small : (gaussianReal 0 1 (Set.Ioo (-0.7072) 0.7072)).toReal ≤ 0.53 := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun x _ => gaussianPDFReal_nonneg _ _ _)]
  set p : ℝ → ℝ := fun x => (1 - x^2/2 + x^4/4) / 2.5 with hp
  have hpc : Continuous p := by rw [hp]; fun_prop
  calc ∫ x in Set.Ioo (-0.7072) 0.7072, gaussianPDFReal 0 1 x
      ≤ ∫ x in Set.Ioo (-0.7072) 0.7072, p x := by
        refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          ((hpc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self) measurableSet_Ioo fun x hx => ?_
        obtain ⟨h1, h2⟩ := hx
        have hx2 : x ^ 2 ≤ 1 := by nlinarith
        have he := Real.abs_exp_sub_one_sub_id_le (x := -x^2/2) (by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg x])
        have he' : Real.exp (-x^2/2) ≤ 1 - x^2/2 + x^4/4 := by
          have := (abs_le.1 he).2; nlinarith
        have hpi : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_d2]
        simp only [gaussianPDFReal, hp, NNReal.coe_one, mul_one, sub_zero]
        have key := mul_le_mul (inv_anti₀ (by norm_num) hpi) he' (Real.exp_pos _).le (by norm_num)
        rw [div_eq_inv_mul (1 - x^2/2 + x^4/4)]; exact key
    _ = ∫ x in (-0.7072)..0.7072, p x := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    _ ≤ 0.53 := by
        simp only [hp]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add, intervalIntegral.integral_sub]
        · simp only [intervalIntegral.integral_div, integral_pow, intervalIntegral.integral_const]
          norm_num
        all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma gauss_tail : ENNReal.ofReal 0.47 ≤ gaussianReal 0 1 {x : ℝ | 1/2 ≤ x^2} := by
  apply ENNReal.ofReal_le_of_le_toReal
  have hs : {x : ℝ | 1/2 ≤ x^2} = {x : ℝ | x^2 < 1/2}ᶜ := by ext x; simp
  have hm : MeasurableSet {x : ℝ | x^2 < 1/2} := measurableSet_lt (by fun_prop) measurable_const
  rw [hs, ← measureReal_def, measureReal_compl hm, measureReal_def, measureReal_def, measure_univ,
    ENNReal.toReal_one]
  have hsub : {x : ℝ | x^2 < 1/2} ⊆ Set.Ioo (-0.7072) 0.7072 := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    constructor <;> nlinarith [sq_nonneg (x - 0.7072), sq_nonneg (x + 0.7072)]
  have := (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := gaussianReal 0 1) hsub)).trans
    gauss_small
  linarith

lemma gauss_tail_var (v g : ℝ) (hg : 0 < g) (hgv : g ≤ v) :
    ENNReal.ofReal 0.47 ≤ gaussianReal 0 v.toNNReal {x : ℝ | g/2 ≤ x^2} := by
  have hv : 0 < v := hg.trans_le hgv
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
  have hmap' : gaussianReal 0 v.toNNReal = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [hmap]; congr 1
    · simp
    · apply NNReal.eq
      simp [Real.sq_sqrt hv.le, hv.le]
  rw [hmap', Measure.map_apply (by fun_prop) (measurableSet_le measurable_const (by fun_prop))]
  refine gauss_tail.trans (measure_mono fun x hx => ?_)
  simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hx ⊢
  rw [mul_pow, Real.sq_sqrt hv.le]
  nlinarith


/-- `w ⬝ y` for `y ~ N(0,S)` is `N(0, wᵀ S w)`. -/
lemma normal_map_dot {d : ℕ} (S : Mat d) (hS : S.PosSemidef) (w : Vec d) :
    (normal S).map (fun y => w ⬝ᵥ y) = gaussianReal 0 (w ⬝ᵥ (S *ᵥ w)).toNNReal := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ (WithLp.toLp 2 w)
  unfold normal
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hL : (fun y : Vec d => w ⬝ᵥ y) ∘ (fun x : EuclideanSpace ℝ (Fin d) => fun i => x i) = L := by
    ext x; simp [L, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hL, IsGaussian.map_eq_gaussianReal L]
  congr 1
  · exact (L.integral_comp_comm IsGaussian.integrable_id).trans (by simp)
  · congr 1
    have h := covarianceBilin_self (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)
      IsGaussian.memLp_two_id (WithLp.toLp 2 w)
    rw [covarianceBilin_multivariateGaussian hS] at h
    rw [h]
    rfl

instance matOpens (d m : ℕ) : OpensMeasurableSpace (Matrix (Fin d) (Fin m) ℝ) :=
  inferInstanceAs (OpensMeasurableSpace (Fin d → Fin m → ℝ))

/-! ### Multivariate Gaussian with large covariance -/

/-- A PSD matrix has a unit vector whose Rayleigh quotient reaches the spectral norm. -/

lemma exists_top {d : ℕ} (hd : 0 < d) (S : Mat d) (hS : S.PosSemidef) :
    ∃ v : Vec d, v ⬝ᵥ v = 1 ∧ GaussianMatrix.specNorm S ≤ v ⬝ᵥ (S *ᵥ v) := by
  have hH := hS.1
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (Mat d) := inferInstance
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => |hH.eigenvalues i|)
    Finset.univ_nonempty
  set v := hH.eigenvectorBasis i0
  have hv1 : (v : Vec d) ⬝ᵥ (v : Vec d) = 1 := by
    have h := (hH.eigenvectorBasis.orthonormal.1 i0)
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simpa [dotProduct, sq] using h
  refine ⟨v, hv1, ?_⟩
  rw [hH.mulVec_eigenvectorBasis i0, dotProduct_smul, hv1, smul_eq_mul, mul_one]
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU := hH.eigenvectorUnitary.2
  unfold GaussianMatrix.specNorm
  calc ‖S‖ ≤ ‖(hH.eigenvectorUnitary : Mat d)‖ * ‖Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)‖ *
        ‖(star hH.eigenvectorUnitary : Mat d)‖ := by
          conv_lhs => rw [hspec]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖(RCLike.ofReal ∘ hH.eigenvalues : Fin d → ℝ)‖ := by
          rw [norm_star, CStarRing.norm_of_mem_unitary hU,
            Matrix.l2_opNorm_diagonal]; ring
    _ ≤ hH.eigenvalues i0 := by
          refine (pi_norm_le_iff_of_nonneg (hS.eigenvalues_nonneg i0)).2 fun i => ?_
          have := hi0 i (Finset.mem_univ _)
          simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs]
          rwa [abs_of_nonneg (hS.eigenvalues_nonneg i0)] at this

/-- A `N(0,S)` vector with `‖S‖ ≥ g` has squared length at least `g/2` with probability `≥ 0.47`. -/
lemma normal_sqLength_bound {d : ℕ} (hd : 0 < d) (S : Mat d) (hS : S.PosSemidef) (g : ℝ) (hg : 0 < g)
    (hgS : g ≤ GaussianMatrix.specNorm S) :
    ENNReal.ofReal 0.47 ≤ normal S {y | g/2 ≤ ∑ i, y i ^ 2} := by
  obtain ⟨v, hv1, hvS⟩ := exists_top hd S hS
  have hmeas : MeasurableSet {x : ℝ | g/2 ≤ x^2} := measurableSet_le measurable_const (by fun_prop)
  calc ENNReal.ofReal 0.47 ≤ gaussianReal 0 (v ⬝ᵥ (S *ᵥ v)).toNNReal {x : ℝ | g/2 ≤ x^2} :=
        gauss_tail_var _ g hg (hgS.trans hvS)
    _ = normal S ((fun y => v ⬝ᵥ y) ⁻¹' {x : ℝ | g/2 ≤ x^2}) := by
        rw [← normal_map_dot S hS v, Measure.map_apply (by fun_prop) hmeas]
    _ ≤ normal S {y | g/2 ≤ ∑ i, y i ^ 2} := by
        refine measure_mono fun y hy => ?_
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v y
        have hv1' : ∑ i, v i ^ 2 = 1 := by simpa [dotProduct, sq] using hv1
        rw [hv1', one_mul] at hcs
        exact hy.trans (by simpa [dotProduct] using hcs)

/-- The event only sees column `i0`, whose law is `N(0,S)`. -/
lemma columnsLaw_col_bound {d m : ℕ} (hd : 0 < d) (S : Mat d) (hS : S.PosSemidef) (g : ℝ)
    (hg : 0 < g) (hgS : g ≤ GaussianMatrix.specNorm S) (i0 : Fin m) :
    ENNReal.ofReal 0.47 ≤ columnsLaw S m {R | g/2 ≤ ∑ j, R j i0 ^ 2} := by
  have hF : MeasurableSet {y : Vec d | g/2 ≤ ∑ i, y i ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hmap : Measurable (fun z : Fin m → Vec d => (fun i j => z j i : Matrix (Fin d) (Fin m) ℝ)) := by
    fun_prop
  have hE : MeasurableSet {R : Matrix (Fin d) (Fin m) ℝ | g/2 ≤ ∑ j, R j i0 ^ 2} := by
    change MeasurableSet {R : Fin d → Fin m → ℝ | g/2 ≤ ∑ j, R j i0 ^ 2}
    exact measurableSet_le measurable_const (by fun_prop)
  have hpre : (fun z : Fin m → Vec d => (fun i j => z j i : Matrix (Fin d) (Fin m) ℝ)) ⁻¹'
      {R | g/2 ≤ ∑ j, R j i0 ^ 2} = (fun z : Fin m → Vec d => z i0) ⁻¹' {y | g/2 ≤ ∑ i, y i ^ 2} := by
    ext z; simp
  have h1 : columnsLaw S m {R | g/2 ≤ ∑ j, R j i0 ^ 2} =
      (Measure.pi fun _ : Fin m => normal S) ((fun z : Fin m → Vec d => z i0) ⁻¹'
        {y | g/2 ≤ ∑ i, y i ^ 2}) := by
    rw [← hpre]; exact Measure.map_apply hmap hE
  rw [h1, (measurePreserving_eval (fun _ : Fin m => normal S) i0).measure_preimage hF.nullMeasurableSet]
  exact normal_sqLength_bound hd S hS g hg hgS

/-! ### GEPP facts -/

/-- `rowPivot` lands at or below `k` and maximizes `|A j k|` over `j ≥ k`. -/
lemma rowPivot_spec {n : ℕ} (A : Mat n) (k : Fin n) :
    k ≤ rowPivot A k ∧ ∀ j, k ≤ j → |A j k| ≤ |A (rowPivot A k) k| := by
  have key : ∀ (l : List (Fin n)) (b : Fin n), k ≤ b →
      k ≤ l.foldl (fun b j => if k ≤ j ∧ (|A b k| < |A j k| ∨ (|A b k| = |A j k| ∧ j < b))
        then j else b) b ∧
      |A b k| ≤ |A (l.foldl (fun b j => if k ≤ j ∧ (|A b k| < |A j k| ∨ (|A b k| = |A j k| ∧ j < b))
        then j else b) b) k| ∧
      ∀ j ∈ l, k ≤ j → |A j k| ≤ |A (l.foldl (fun b j => if k ≤ j ∧
        (|A b k| < |A j k| ∨ (|A b k| = |A j k| ∧ j < b)) then j else b) b) k| := by
    intro l
    induction l with
    | nil => intro b hb; simp [hb]
    | cons a l ih =>
      intro b hb
      simp only [List.foldl_cons, List.mem_cons]
      by_cases h : k ≤ a ∧ (|A b k| < |A a k| ∨ (|A b k| = |A a k| ∧ a < b))
      · rw [if_pos h]
        obtain ⟨h1, h2, h3⟩ := ih a h.1
        have hba : |A b k| ≤ |A a k| := by
          rcases h.2 with h' | h'
          · exact h'.le
          · exact h'.1.le
        refine ⟨h1, hba.trans h2, fun j hj hkj => ?_⟩
        rcases hj with rfl | hj
        · exact h2
        · exact h3 j hj hkj
      · rw [if_neg h]
        obtain ⟨h1, h2, h3⟩ := ih b hb
        refine ⟨h1, h2, fun j hj hkj => ?_⟩
        rcases hj with rfl | hj
        · have : |A j k| ≤ |A b k| := by
            by_contra hc; exact h ⟨hkj, Or.inl (lt_of_not_ge hc)⟩
          exact this.trans h2
        · exact h3 j hj hkj
  obtain ⟨h1, -, h3⟩ := key (List.finRange n) k le_rfl
  exact ⟨h1, fun j hj => h3 j (List.mem_finRange j) hj⟩

/-- Row `t` is frozen once step `t` has been performed. -/
lemma run_row_stable {n : ℕ} (A : Mat n) (t : ℕ) (ht : t < n) (b : Fin n) :
    ∀ s, t + 1 ≤ s → (run A s).matrix ⟨t, ht⟩ b = (run A (t+1)).matrix ⟨t, ht⟩ b := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ s hs ih =>
    rw [← ih]
    simp only [run]
    split_ifs with hsn
    · have hp := (rowPivot_spec (run A s).matrix ⟨s, hsn⟩).1
      have hne1 : (⟨t, ht⟩ : Fin n) ≠ ⟨s, hsn⟩ := by
        intro h; simp [Fin.ext_iff] at h; omega
      have hne2 : (⟨t, ht⟩ : Fin n) ≠ rowPivot (run A s).matrix ⟨s, hsn⟩ := by
        intro h; rw [← h] at hp; simp [Fin.le_def] at hp; omega
      have hlt : ¬ (⟨s, hsn⟩ : Fin n) < ⟨t, ht⟩ := by simp [Fin.lt_def]; omega
      simp [stepAt, Equiv.swap_apply_of_ne_of_ne hne1 hne2, hlt]
    · rfl

/-- The `t`-th diagonal entry of `U` dominates the `t`-th residual column. -/
lemma col_le_maxEntry {n : ℕ} (A : Mat n) (t : ℕ) (ht : t < n) (i : Fin n) (hi : t ≤ i.val) :
    |(run A t).matrix i ⟨t, ht⟩| ≤ maxEntry (upper A) := by
  have hdiag : upper A ⟨t, ht⟩ ⟨t, ht⟩ =
      (run A t).matrix (rowPivot (run A t).matrix ⟨t, ht⟩) ⟨t, ht⟩ := by
    simp only [upper, le_refl, if_true]
    rw [run_row_stable A t ht _ n (by omega)]
    simp [run, ht, stepAt]
  have hle : ‖upper A ⟨t, ht⟩ ⟨t, ht⟩‖₊ ≤ (Finset.univ : Finset (Fin n × Fin n)).sup
      (fun ij => ‖upper A ij.1 ij.2‖₊) :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => ‖upper A ij.1 ij.2‖₊) (Finset.mem_univ (⟨t, ht⟩, ⟨t, ht⟩))
  have hle' : |upper A ⟨t, ht⟩ ⟨t, ht⟩| ≤ maxEntry (upper A) := by
    unfold maxEntry
    have := NNReal.coe_le_coe.2 hle
    simpa using this
  rw [hdiag] at hle'
  exact ((rowPivot_spec (run A t).matrix ⟨t, ht⟩).2 i (by simp [Fin.le_def]; omega)).trans hle'


lemma block_embed {d : ℕ} (M : Mat d) : block (embed M) d = M := by
  ext i j; simp [block, embed]

/-- The actual covariance after `t` steps is a zero-padded PSD matrix of size `n - t`. -/
lemma actualCov_embed {n : ℕ} (A : Mat n) : ∀ t, t ≤ n → ∀ m, n - t = m →
    ∃ M : Mat m, M.PosSemidef ∧ actualCov A t = embed M := by
  intro t
  induction t with
  | zero =>
    intro _ m hm
    obtain rfl : m = n := by omega
    exact ⟨1, Matrix.PosSemidef.one, rfl⟩
  | succ t ih =>
    intro ht m hm
    obtain ⟨M, hM, hE⟩ := ih (by omega) (m+1) (by omega)
    refine ⟨update M (fun j => actualColumn A t j.val), ?_, ?_⟩
    · have h := hM.mul_mul_conjTranspose_same
        (compressionAt (fun j => actualColumn A t j.val) (pivot (fun j => actualColumn A t j.val)))
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
      exact h
    · show stateUpdate (n - t) (actualCov A t) (actualColumn A t) = _
      rw [hE, show n - t = m + 1 by omega]
      simp only [stateUpdate, block_embed]

lemma cov_psd {n : ℕ} (A : Mat n) (t : ℕ) (ht : t ≤ n) :
    (block (actualCov A t) (n - t)).PosSemidef := by
  obtain ⟨M, hM, hE⟩ := actualCov_embed A t ht (n - t) rfl
  rw [hE, block_embed]; exact hM

/-! ### Main argument -/

lemma measurable_specNorm_block (m : ℕ) :
    Measurable (fun S : CovState => GaussianMatrix.specNorm (block S m)) := by
  unfold GaussianMatrix.specNorm
  exact continuous_norm.measurable.comp (by unfold block; fun_prop)

/-- Conditional bound integrated over the conditioning event, for `1 ≤ t < n`. -/
lemma main_pos (n t : ℕ) (ht : t < n) (hR : HasResidualLaw n t ht.le) (g : ℝ) (hg : 0 < g) :
    ENNReal.ofReal 0.47 * GaussianMatrix.gaussianMatrix n n
        {A | g ≤ GaussianMatrix.specNorm (block (actualCov A t) (n-t))} ≤
      GaussianMatrix.gaussianMatrix n n
        {A | Real.sqrt (g/(2*((n-t : ℕ):ℝ))) ≤ maxEntry (upper A) ∧
          g ≤ GaussianMatrix.specNorm (block (actualCov A t) (n-t))} := by
  obtain ⟨⟨c, hc, hcA⟩, hlaw⟩ := hR
  have h0 : 0 < n - t := by omega
  set H : Set (Matrix (Fin n) (Fin t) ℝ) := {F | g ≤ GaussianMatrix.specNorm (block (c F) (n-t))}
  have hH : MeasurableSet H := measurableSet_le measurable_const ((measurable_specNorm_block _).comp hc)
  set E : Set (Mat (n-t)) := {R | g/2 ≤ ∑ j, R j ⟨0, h0⟩ ^ 2}
  have hE : MeasurableSet E := by
    change MeasurableSet {R : Fin (n-t) → Fin (n-t) → ℝ | g/2 ≤ ∑ j, R j ⟨0, h0⟩ ^ 2}
    exact measurableSet_le measurable_const (by fun_prop)
  have hfc : Measurable (firstColumns (n := n) ht.le) := by
    change Measurable (fun A : Fin n → Fin n → ℝ => fun i (j : Fin t) => A i ⟨j.val, by omega⟩)
    fun_prop
  have : Nonempty (Fin (n-t)) := ⟨⟨0, h0⟩⟩
  have hC : {A : Fin n → Fin n → ℝ | g ≤ GaussianMatrix.specNorm (block (actualCov A t) (n-t))} =
      {A | firstColumns ht.le A ∈ H} := by
    ext A
    exact Iff.of_eq (congrArg (fun S => g ≤ GaussianMatrix.specNorm (block S (n-t))) (hcA A).symm)
  have hJ : {A | firstColumns ht.le A ∈ H ∧ residual A t ∈ E} ⊆
      {A | Real.sqrt (g/(2*((n-t : ℕ):ℝ))) ≤ maxEntry (upper A) ∧
        g ≤ GaussianMatrix.specNorm (block (actualCov A t) (n-t))} := by
    rintro A ⟨hA1, hA2⟩
    refine ⟨?_, by simpa [H, hcA] using hA1⟩
    simp only [E, Set.mem_ofPred_eq] at hA2
    have hdpos : (0:ℝ) < ((n-t : ℕ):ℝ) := Nat.cast_pos.2 h0
    have hsum : ∑ _j : Fin (n-t), g / (2*((n-t : ℕ):ℝ)) ≤ ∑ j : Fin (n-t), residual A t j ⟨0, h0⟩ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      convert hA2 using 1
      field_simp
    obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    have hres : residual A t j ⟨0, h0⟩ = (run A t).matrix ⟨j.val + t, by omega⟩ ⟨t, ht⟩ := by
      simp [residual]
    rw [hres] at hj
    calc Real.sqrt (g/(2*((n-t : ℕ):ℝ)))
        ≤ Real.sqrt ((run A t).matrix ⟨j.val + t, by omega⟩ ⟨t, ht⟩ ^ 2) := Real.sqrt_le_sqrt hj
      _ = |(run A t).matrix ⟨j.val + t, by omega⟩ ⟨t, ht⟩| := Real.sqrt_sq_eq_abs _
      _ ≤ maxEntry (upper A) := col_le_maxEntry A t ht _ (by simp)
  rw [hC]
  calc ENNReal.ofReal 0.47 * GaussianMatrix.gaussianMatrix n n {A | firstColumns ht.le A ∈ H}
      = ∫⁻ _A in {A | firstColumns ht.le A ∈ H}, ENNReal.ofReal 0.47
          ∂(GaussianMatrix.gaussianMatrix n n) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ A in {A | firstColumns ht.le A ∈ H},
          columnsLaw (block (actualCov A t) (n-t)) (n-t) E ∂(GaussianMatrix.gaussianMatrix n n) := by
        refine setLIntegral_mono' (hfc hH) fun A hA => ?_
        have hA' : g ≤ GaussianMatrix.specNorm (block (c (firstColumns ht.le A)) (n-t)) := hA
        replace hA' := Eq.mp (congrArg (fun S => g ≤ GaussianMatrix.specNorm (block S (n-t))) (hcA A)) hA'
        exact columnsLaw_col_bound h0 _ (cov_psd A t ht.le) g hg hA' _
    _ = GaussianMatrix.gaussianMatrix n n {A | firstColumns ht.le A ∈ H ∧ residual A t ∈ E} :=
        (hlaw H E hH hE).symm
    _ ≤ _ := measure_mono hJ

end GEPPGrowth.Main.Prop54

open GEPPGrowth.Main GEPPGrowth.Main.Prop54 in
theorem solution (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (g : ℝ) (hg : 0 < g)
    (hpos : 0 < prob (GaussianMatrix.gaussianMatrix n n)
      {A | g ≤ GaussianMatrix.specNorm (block (actualCov A (n-d)) d)}) :
    (0.47:ℝ) ≤
      prob (GaussianMatrix.gaussianMatrix n n)
        {A | Real.sqrt (g/(2*(d:ℝ))) ≤ maxEntry (upper A) ∧
          g ≤ GaussianMatrix.specNorm (block (actualCov A (n-d)) d)} /
      prob (GaussianMatrix.gaussianMatrix n n)
        {A | g ≤ GaussianMatrix.specNorm (block (actualCov A (n-d)) d)} := by
  rcases Nat.lt_or_ge (n - d) 1 with h0 | h1
  · have hnd : n = d := by omega
    subst hnd
    have hn : 0 < n := by omega
    simp only [Nat.sub_self] at hpos ⊢
    have hval : ∀ A : Mat n, GaussianMatrix.specNorm (block (actualCov A 0) n) = 1 := fun A => by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      show GaussianMatrix.specNorm (block (embed (1 : Mat n)) n) = 1
      rw [block_embed]; exact CStarRing.norm_one
    have hg1 : g ≤ 1 := by
      by_contra h
      have : {A : Fin n → Fin n → ℝ | g ≤ GaussianMatrix.specNorm (block (actualCov A 0) n)} = ∅ := by
        ext A
        simp only [Set.mem_empty_iff_false, iff_false]
        exact fun hA => h ((hA : g ≤ _).trans_eq (hval A))
      rw [this] at hpos; simp [prob] at hpos
    have hC : {A : Fin n → Fin n → ℝ | g ≤ GaussianMatrix.specNorm (block (actualCov A 0) n)} =
        Set.univ := by
      ext A
      simp only [Set.mem_univ, iff_true]
      exact hg1.trans_eq (hval A).symm
    rw [hC]
    simp only [prob, measure_univ, ENNReal.toReal_one, div_one]
    have hsubT : {A : Fin n → Fin n → ℝ | Real.sqrt (g/(2*(n:ℝ))) ≤ maxEntry (upper A)} ⊆
        {A : Fin n → Fin n → ℝ | Real.sqrt (g/(2*(n:ℝ))) ≤ maxEntry (upper A) ∧
          g ≤ GaussianMatrix.specNorm (block (actualCov A 0) n)} :=
      fun A hA => ⟨hA, hg1.trans_eq (hval A).symm⟩
    refine le_trans ?_ (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubT))
    set i0 : Fin n := ⟨0, hn⟩
    have hF : MeasurableSet {x : ℝ | 1/2 ≤ x^2} := measurableSet_le measurable_const (by fun_prop)
    have hF' : MeasurableSet ((fun r : Fin n → ℝ => r i0) ⁻¹' {x : ℝ | 1/2 ≤ x^2}) :=
      (measurable_pi_apply i0) hF
    have hlaw : GaussianMatrix.gaussianMatrix n n ((fun A : Fin n → Fin n → ℝ => A i0) ⁻¹'
        ((fun r : Fin n → ℝ => r i0) ⁻¹' {x : ℝ | 1/2 ≤ x^2})) = gaussianReal 0 1 {x : ℝ | 1/2 ≤ x^2} := by
      unfold GaussianMatrix.gaussianMatrix
      rw [(measurePreserving_eval _ i0).measure_preimage hF'.nullMeasurableSet,
        (measurePreserving_eval _ i0).measure_preimage hF.nullMeasurableSet]
    have hsub : (fun A : Fin n → Fin n → ℝ => A i0) ⁻¹' ((fun r : Fin n → ℝ => r i0) ⁻¹'
        {x : ℝ | 1/2 ≤ x^2}) ⊆ {A | Real.sqrt (g/(2*(n:ℝ))) ≤ maxEntry (upper A)} := by
      intro A hA
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hA ⊢
      have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hgn : g/(2*(n:ℝ)) ≤ 1/2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      calc Real.sqrt (g/(2*(n:ℝ))) ≤ Real.sqrt (A i0 i0 ^ 2) := Real.sqrt_le_sqrt (hgn.trans hA)
        _ = |(run A 0).matrix i0 ⟨0, hn⟩| := Real.sqrt_sq_eq_abs _
        _ ≤ maxEntry (upper A) := col_le_maxEntry A 0 hn i0 (by simp)
    have h1 := measure_mono (μ := GaussianMatrix.gaussianMatrix n n) hsub
    rw [hlaw] at h1
    have h2 := gauss_tail.trans h1
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h2
  · obtain ⟨t, rfl⟩ : ∃ t, d = n - t := ⟨n - d, by omega⟩
    have e : n - (n - t) = t := by omega
    simp only [e] at hpos ⊢
    have hR : HasResidualLaw n t (by omega) := (lemma_4_13 n (t+1) (by omega) (by omega)).1
    have key := main_pos n t (by omega) hR g hg
    unfold prob at *
    rw [le_div_iff₀ hpos]
    have := ENNReal.toReal_mono (measure_ne_top _ _) key
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at this
