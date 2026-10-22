-- Prove2me | solution 1 for ExtraConsensus.Linear.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T04:44:23.68401+00:00
-- url     : https://prove2.me/submissions/d169299d-b547-4627-b1a5-537f3e78205f

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

set_option autoImplicit false

namespace EC37

open Matrix ExtraConsensus.Sublinear ExtraConsensus.Linear

variable {n p : ℕ}

/-! ### frob algebra -/

lemma frob_add_left (x y z : Stack n p) : frob (x + y) z = frob x z + frob y z := by
  simp [frob, inner_add_left, Finset.sum_add_distrib]

lemma frob_add_right (x y z : Stack n p) : frob z (x + y) = frob z x + frob z y := by
  simp [frob, inner_add_right, Finset.sum_add_distrib]

lemma frob_sub_left (x y z : Stack n p) : frob (x - y) z = frob x z - frob y z := by
  simp [frob, inner_sub_left, Finset.sum_sub_distrib]

lemma frob_sub_right (x y z : Stack n p) : frob z (x - y) = frob z x - frob z y := by
  simp [frob, inner_sub_right, Finset.sum_sub_distrib]

lemma frob_smul_left (c : ℝ) (x z : Stack n p) : frob (c • x) z = c * frob x z := by
  simp [frob, real_inner_smul_left, Finset.mul_sum]

lemma frob_smul_right (c : ℝ) (x z : Stack n p) : frob z (c • x) = c * frob z x := by
  simp [frob, real_inner_smul_right, Finset.mul_sum]

lemma frob_comm (x y : Stack n p) : frob x y = frob y x := by
  simp [frob, real_inner_comm]

lemma frob_self_nonneg (x : Stack n p) : 0 ≤ frob x x := by
  unfold frob
  exact Finset.sum_nonneg fun i _ => real_inner_self_nonneg

lemma frob_two_mul_le (t : ℝ) (ht : 0 < t) (x y : Stack n p) :
    2 * t * frob x y ≤ t ^ 2 * frob x x + frob y y := by
  have h := frob_self_nonneg (t • x - y)
  simp only [frob_sub_left, frob_sub_right, frob_smul_left, frob_smul_right] at h
  have := frob_comm x y
  nlinarith

lemma frob_add_sq_le (x y : Stack n p) :
    frob (x + y) (x + y) ≤ 2 * frob x x + 2 * frob y y := by
  have h := frob_two_mul_le 1 one_pos x y
  simp only [frob_add_left, frob_add_right]
  have := frob_comm x y
  nlinarith

/-! ### mix algebra -/

lemma mix_add (A : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix A (x + y) = mix A x + mix A y := by
  funext i; simp [mix, smul_add, Finset.sum_add_distrib]

lemma mix_sub (A : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix A (x - y) = mix A x - mix A y := by
  funext i; simp [mix, smul_sub, Finset.sum_sub_distrib]

lemma mix_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Stack n p) :
    mix A (c • x) = c • mix A x := by
  funext i; simp [mix, Finset.smul_sum, smul_smul, mul_comm]

lemma mix_zero (A : Matrix (Fin n) (Fin n) ℝ) : mix A (0 : Stack n p) = 0 := by
  funext i; simp [mix]

lemma mix_sum (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset ℕ) (x : ℕ → Stack n p) :
    mix A (∑ t ∈ s, x t) = ∑ t ∈ s, mix A (x t) := by
  induction s using Finset.induction_on with
  | empty => simp [mix_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mix_add, ih]

lemma mix_add_mat (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A + B) x = mix A x + mix B x := by
  funext i; simp [mix, add_smul, Finset.sum_add_distrib]

lemma mix_sub_mat (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A - B) x = mix A x - mix B x := by
  funext i; simp [mix, sub_smul, Finset.sum_sub_distrib]

lemma mix_smul_mat (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Stack n p) :
    mix (c • A) x = c • mix A x := by
  funext i; simp [mix, Finset.smul_sum, smul_smul]

lemma mix_one (x : Stack n p) : mix (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  funext i; simp [mix, Matrix.one_apply]

lemma mix_mul (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A * B) x = mix A (mix B x) := by
  funext i
  simp only [mix, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma mix_const (A : Matrix (Fin n) (Fin n) ℝ) (xs : EuclideanSpace ℝ (Fin p)) :
    mix A (fun _ => xs : Stack n p) = fun i => (∑ j, A i j) • xs := by
  funext i; simp [mix, Finset.sum_smul]

/-! ### columns -/

/-- column `c` of a stack -/
noncomputable def col (x : Stack n p) (c : Fin p) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (x i) c)

lemma frob_eq_col (x y : Stack n p) : frob x y = ∑ c, inner ℝ (col x c) (col y c) := by
  simp only [frob, col, PiLp.inner_apply]
  rw [Finset.sum_comm]

lemma col_mix (A : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) (c : Fin p) :
    col (mix A x) c = Matrix.toEuclideanLin A (col x c) := by
  ext i
  simp [col, mix, Matrix.mulVec, dotProduct]

/-! ### spectral facts for symmetric matrices -/

lemma herm_of_symm {A : Matrix (Fin n) (Fin n) ℝ} (h : Aᵀ = A) : A.IsHermitian := by
  show Aᴴ = A
  rw [conjTranspose_eq_transpose_of_trivial]; exact h

lemma isSym_of_symm {A : Matrix (Fin n) (Fin n) ℝ} (h : Aᵀ = A) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (herm_of_symm h)

lemma basis_inner (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v w = ∑ i, b.repr v i * b.repr w i := by
  rw [← b.repr.inner_map_map v w]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma hn_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin

lemma sym_repr {T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)} (hT : T.IsSymmetric)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (hT.eigenvectorBasis hn_fin).repr (T v) i =
      hT.eigenvalues hn_fin i * (hT.eigenvectorBasis hn_fin).repr v i := by
  have := hT.eigenvectorBasis_apply_self_apply hn_fin v i
  simpa using this

lemma vec_lmin {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) {l : ℝ} (hl : IsLamMin A l)
    (v : EuclideanSpace ℝ (Fin n)) :
    l * inner ℝ v v ≤ inner ℝ v (Matrix.toEuclideanLin A v) := by
  set hT := isSym_of_symm hs
  set b := hT.eigenvectorBasis hn_fin
  have hle : ∀ i, l ≤ hT.eigenvalues hn_fin i := by
    intro i
    apply hl.2
    refine ⟨WithLp.ofLp (b i), ?_, ?_⟩
    · intro h0
      have hne := b.orthonormal.ne_zero i
      apply hne
      ext j
      have := congrFun h0 j
      simpa using this
    · have h1 := hT.apply_eigenvectorBasis hn_fin i
      rw [show A *ᵥ WithLp.ofLp (b i) = WithLp.ofLp (Matrix.toEuclideanLin A (b i)) from rfl, h1]
      simp
      rfl
  rw [basis_inner b, basis_inner b, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [sym_repr hT v i]
  have := hle i
  have h3 := mul_self_nonneg (b.repr v i)
  nlinarith

lemma vec_range {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin A v) ≤
        K * inner ℝ (Matrix.toEuclideanLin A (Matrix.toEuclideanLin A v))
          (Matrix.toEuclideanLin A (Matrix.toEuclideanLin A v)) := by
  set hT := isSym_of_symm hs
  set b := hT.eigenvectorBasis hn_fin
  set lam := hT.eigenvalues hn_fin
  have hb : ∀ v i, b.repr (Matrix.toEuclideanLin A v) i = lam i * b.repr v i :=
    fun v i => sym_repr hT v i
  refine ⟨∑ j, (lam j ^ 2)⁻¹, Finset.sum_nonneg fun j _ => by positivity, fun v => ?_⟩
  rw [basis_inner b, basis_inner b, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [hb]
  have hK : (lam i ^ 2)⁻¹ ≤ ∑ j, (lam j ^ 2)⁻¹ :=
    Finset.single_le_sum (f := fun j => (lam j ^ 2)⁻¹) (fun j _ => by positivity)
      (Finset.mem_univ i)
  by_cases h0 : lam i = 0
  · simp [h0]
  · have hpos : 0 < lam i ^ 2 := by positivity
    have key : lam i * b.repr v i * (lam i * b.repr v i) =
        (lam i ^ 2)⁻¹ * (lam i * (lam i * b.repr v i) * (lam i * (lam i * b.repr v i))) := by
      field_simp
    rw [key]
    have h4 := mul_self_nonneg (lam i * (lam i * b.repr v i))
    exact mul_le_mul_of_nonneg_right hK h4

lemma vec_bound {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin A v) (Matrix.toEuclideanLin A v) ≤ K * inner ℝ v v := by
  set hT := isSym_of_symm hs
  set b := hT.eigenvectorBasis hn_fin
  set lam := hT.eigenvalues hn_fin
  have hb : ∀ v i, b.repr (Matrix.toEuclideanLin A v) i = lam i * b.repr v i :=
    fun v i => sym_repr hT v i
  refine ⟨∑ j, lam j ^ 2, Finset.sum_nonneg fun j _ => by positivity, fun v => ?_⟩
  rw [basis_inner b, basis_inner b, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [hb]
  have hK : lam i ^ 2 ≤ ∑ j, lam j ^ 2 :=
    Finset.single_le_sum (f := fun j => lam j ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h4 := mul_self_nonneg (b.repr v i)
  nlinarith

lemma vec_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ inner ℝ v (Matrix.toEuclideanLin A v) := by
  have := hA.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using this

/-! ### stack versions -/

lemma frob_mix_symm {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) (x y : Stack n p) :
    frob (mix A x) y = frob x (mix A y) := by
  rw [frob_eq_col, frob_eq_col]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [col_mix, col_mix]
  exact isSym_of_symm hs _ _

lemma frob_mix_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (x : Stack n p) :
    0 ≤ frob x (mix A x) := by
  rw [frob_eq_col]
  refine Finset.sum_nonneg fun c _ => ?_
  rw [col_mix]
  exact vec_psd hA _

lemma frob_lmin {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) {l : ℝ} (hl : IsLamMin A l)
    (x : Stack n p) : l * frob x x ≤ frob x (mix A x) := by
  rw [frob_eq_col, frob_eq_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [col_mix]
  exact vec_lmin hs hl _

lemma frob_range {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Stack n p,
      frob (mix A w) (mix A w) ≤ K * frob (mix A (mix A w)) (mix A (mix A w)) := by
  obtain ⟨K, hK0, hK⟩ := vec_range hs
  refine ⟨K, hK0, fun w => ?_⟩
  rw [frob_eq_col, frob_eq_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [col_mix]
  exact hK _

lemma frob_bound {A : Matrix (Fin n) (Fin n) ℝ} (hs : Aᵀ = A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Stack n p, frob (mix A x) (mix A x) ≤ K * frob x x := by
  obtain ⟨K, hK0, hK⟩ := vec_bound hs
  refine ⟨K, hK0, fun w => ?_⟩
  rw [frob_eq_col, frob_eq_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  simp only [col_mix]
  exact hK _

/-! ### gradient Lipschitz bound in Frobenius norm -/

lemma frob_grad_lip {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ} {Lf : ℝ}
    (hA2 : ConvexLipschitzGrad f Lf) (a b : Stack n p) :
    frob (gradF f a - gradF f b) (gradF f a - gradF f b) ≤ Lf ^ 2 * frob (a - b) (a - b) := by
  unfold frob
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply, gradF, real_inner_self_eq_norm_sq]
  have h1 := hA2.lipschitz i (a i) (b i)
  have h0 := norm_nonneg (gradient (f i) (a i) - gradient (f i) (b i))
  have h2 := norm_nonneg (a i - b i)
  have hL := hA2.Lf_nonneg
  have h3 : ‖gradient (f i) (a i) - gradient (f i) (b i)‖ ^ 2 ≤ (Lf * ‖a i - b i‖) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  rw [mul_pow] at h3
  exact h3

/-! ### the EXTRA recursion in `(q, x)` form -/

lemma iter_rec (α : ℝ) (W Wt U : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x0 : Stack n p) (hU2 : U * U = Wt - W) (k : ℕ) :
    extraIter α W Wt f x0 (k + 1) =
      mix Wt (extraIter α W Wt f x0 k) - mix U (qSeq U (extraIter α W Wt f x0) k)
        - α • gradF f (extraIter α W Wt f x0 k) := by
  induction k with
  | zero =>
    have h1 : extraIter α W Wt f x0 (0 + 1) = mix W x0 - α • gradF f x0 := rfl
    have h0 : extraIter α W Wt f x0 0 = x0 := rfl
    have hq : qSeq U (extraIter α W Wt f x0) 0 = mix U x0 := by simp [qSeq, h0]
    rw [h1, h0, hq, ← mix_mul, hU2, mix_sub_mat]
    abel
  | succ k ih =>
    have h2 : extraIter α W Wt f x0 (k + 1 + 1) =
        mix (1 + W) (extraIter α W Wt f x0 (k + 1)) - mix Wt (extraIter α W Wt f x0 k)
          - α • (gradF f (extraIter α W Wt f x0 (k + 1)) - gradF f (extraIter α W Wt f x0 k)) :=
      rfl
    have hq : qSeq U (extraIter α W Wt f x0) (k + 1) =
        qSeq U (extraIter α W Wt f x0) k + mix U (extraIter α W Wt f x0 (k + 1)) := by
      simp [qSeq, Finset.sum_range_succ]
    have hk : mix U (qSeq U (extraIter α W Wt f x0) k) =
        mix Wt (extraIter α W Wt f x0 k) - α • gradF f (extraIter α W Wt f x0 k)
          - extraIter α W Wt f x0 (k + 1) := by
      rw [ih]; abel
    rw [h2, hq, mix_add, ← mix_mul, hU2, mix_sub_mat, mix_add_mat, mix_one, hk, smul_sub]
    abel

/-! ### one-step lower bound for the decrease -/

lemma delta_lower {α μg lmin Lf t : ℝ} {W Wt U : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    (hUs : Uᵀ = U) (hU2 : U * U = Wt - W) (hWts : Wtᵀ = Wt)
    (hB : ((1 / 2 : ℝ) • (1 + W) - Wt).PosSemidef) (hlmin : IsLamMin Wt lmin)
    (hLip : ∀ a b : Stack n p,
      frob (gradF f a - gradF f b) (gradF f a - gradF f b) ≤ Lf ^ 2 * frob (a - b) (a - b))
    (hα0 : 0 < α) (ht : 0 < t)
    (a b Xs r : Stack n p)
    (hrscb : μg * frob (b - Xs) (b - Xs) ≤
      frob (gradG α W Wt f b - gradG α W Wt f Xs) (b - Xs))
    (hUr : mix U r = mix Wt (a - Xs) - (b - Xs) + mix (Wt - W) (b - Xs)
        - α • (gradF f a - gradF f Xs)) :
    (t * lmin - α * Lf ^ 2) * frob (b - a) (b - a) + α * t * (2 * μg - t) * frob (b - Xs) (b - Xs)
      ≤ t * ((frob (r - mix U (b - Xs)) (r - mix U (b - Xs)) + frob (a - Xs) (mix Wt (a - Xs)))
        - (frob r r + frob (b - Xs) (mix Wt (b - Xs)))) := by
  have hDe : b - a = (b - Xs) - (a - Xs) := by abel
  have hG : gradG α W Wt f b - gradG α W Wt f Xs =
      ((gradF f a - gradF f Xs) + (gradF f b - gradF f a)) + (1 / (2 * α)) • mix (Wt - W) (b - Xs) := by
    simp only [gradG, mix_sub, smul_sub]
    abel
  have hLp : frob (gradF f b - gradF f a) (gradF f b - gradF f a) ≤ Lf ^ 2 * frob (b - a) (b - a) :=
    hLip b a
  have hL := frob_lmin hWts hlmin (b - a)
  have hP0 := frob_mix_psd hB (b - Xs)
  rw [hG] at hrscb
  rw [hDe] at hL hLp ⊢
  generalize b - Xs = d at hrscb hUr hL hLp hP0 ⊢
  generalize a - Xs = e at hrscb hUr hL hLp hP0 ⊢
  generalize gradF f a - gradF f Xs = gk at hrscb hUr hL hLp hP0 ⊢
  generalize gradF f b - gradF f a = h at hrscb hUr hL hLp hP0 ⊢
  -- E1
  have E1 : frob (r - mix U d) (r - mix U d) =
      frob r r - 2 * frob (mix U r) d + frob (mix U d) (mix U d) := by
    rw [frob_sub_left, frob_sub_right, frob_sub_right, frob_comm (mix U d) r,
      frob_mix_symm hUs r d]
    ring
  -- E2
  have E2 : frob (mix U d) (mix U d) = frob d (mix Wt d) - frob d (mix W d) := by
    rw [frob_mix_symm hUs, ← mix_mul, hU2, mix_sub_mat, frob_sub_right]
  -- E3
  have E3 : frob (mix U r) d = frob (mix Wt e) d - frob d d
      + (frob d (mix Wt d) - frob d (mix W d)) - α * frob gk d := by
    rw [hUr, frob_sub_left, frob_add_left, frob_sub_left, frob_smul_left,
      frob_comm (mix (Wt - W) d) d, mix_sub_mat, frob_sub_right (mix Wt d) (mix W d) d]
  -- E4
  have E4 : frob (d - e) (mix Wt (d - e)) =
      frob d (mix Wt d) - 2 * frob (mix Wt e) d + frob e (mix Wt e) := by
    rw [mix_sub, frob_sub_left, frob_sub_right, frob_sub_right, frob_comm d (mix Wt e),
      ← frob_mix_symm hWts e d]
    ring
  -- RSC
  rw [frob_add_left, frob_add_left, frob_smul_left, mix_sub_mat, frob_comm (mix Wt d - mix W d) d,
    frob_sub_right (mix Wt d) (mix W d) d] at hrscb
  have hR2 : 2 * α * (μg * frob d d) ≤
      2 * α * frob gk d + 2 * α * frob h d + (frob d (mix Wt d) - frob d (mix W d)) := by
    have := mul_le_mul_of_nonneg_left hrscb (by positivity : (0 : ℝ) ≤ 2 * α)
    have heq : 2 * α * (frob gk d + frob h d + 1 / (2 * α) * (frob d (mix Wt d) - frob d (mix W d)))
        = 2 * α * frob gk d + 2 * α * frob h d + (frob d (mix Wt d) - frob d (mix W d)) := by
      field_simp
    linarith
  -- PSD
  rw [mix_sub_mat, mix_smul_mat, mix_add_mat, mix_one, frob_sub_right, frob_smul_right,
    frob_add_right] at hP0
  rw [E4] at hL
  -- AM-GM and Lipschitz
  have hAM := frob_two_mul_le t ht d h
  rw [frob_comm d h] at hAM
  have hAM' := mul_le_mul_of_nonneg_left hAM hα0.le
  have hLp' := mul_le_mul_of_nonneg_left hLp hα0.le
  rw [E1, E2, E3]
  have hΔ : lmin * frob (d - e) (d - e) + 2 * α * μg * frob d d - 2 * α * frob h d ≤
      (frob r r - 2 * (frob (mix Wt e) d - frob d d + (frob d (mix Wt d) - frob d (mix W d))
        - α * frob gk d) + (frob d (mix Wt d) - frob d (mix W d)) + frob e (mix Wt e))
        - (frob r r + frob d (mix Wt d)) := by
    linarith
  have := mul_le_mul_of_nonneg_left hΔ ht.le
  nlinarith

/-! ### one-step upper bound for the Lyapunov value -/

lemma V_upper {α Lf KR KW KA : ℝ} {W Wt U : Matrix (Fin n) (Fin n) ℝ}
    {f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ}
    (hKR0 : 0 ≤ KR) (hKW0 : 0 ≤ KW) (hKA0 : 0 ≤ KA)
    (hKW : ∀ x : Stack n p, frob (mix Wt x) (mix Wt x) ≤ KW * frob x x)
    (hKA : ∀ x : Stack n p, frob (mix (Wt - W) x) (mix (Wt - W) x) ≤ KA * frob x x)
    (hLip : ∀ a b : Stack n p,
      frob (gradF f a - gradF f b) (gradF f a - gradF f b) ≤ Lf ^ 2 * frob (a - b) (a - b))
    (a b Xs r : Stack n p)
    (hr : frob r r ≤ KR * frob (mix U r) (mix U r))
    (hUr : mix U r = mix Wt (a - Xs) - (b - Xs) + mix (Wt - W) (b - Xs)
        - α • (gradF f a - gradF f Xs)) :
    frob r r + frob (b - Xs) (mix Wt (b - Xs)) ≤
      (KR * (8 * KW + 8 * α ^ 2 * Lf ^ 2 + 4 + 4 * KA) + (1 + KW) / 2 + 1)
        * (frob (b - Xs) (b - Xs) + frob (b - a) (b - a)) := by
  have hed : a - Xs = (b - Xs) - (b - a) := by abel
  have hg := hLip a Xs
  rw [hed] at hg hUr
  generalize b - Xs = d at hg hUr ⊢
  generalize b - a = D at hg hUr ⊢
  generalize gradF f a - gradF f Xs = gk at hg hUr ⊢
  have hsub : ∀ x y : Stack n p, frob (x - y) (x - y) ≤ 2 * frob x x + 2 * frob y y := by
    intro x y
    rw [sub_eq_add_neg]
    have := frob_add_sq_le x (-y)
    have hneg : frob (-y) (-y) = frob y y := by
      rw [← neg_one_smul ℝ y, frob_smul_left, frob_smul_right]; ring
    linarith
  have hdd := frob_self_nonneg d
  have hDD := frob_self_nonneg D
  have hee := hsub d D
  generalize d - D = e at hg hUr hee ⊢
  -- Ur bound
  have hU1 : frob (mix U r) (mix U r) ≤
      2 * frob (mix Wt e - d) (mix Wt e - d) + 2 * frob (mix (Wt - W) d - α • gk)
        (mix (Wt - W) d - α • gk) := by
    rw [hUr, show mix Wt e - d + mix (Wt - W) d - α • gk =
      (mix Wt e - d) + (mix (Wt - W) d - α • gk) by abel]
    exact frob_add_sq_le _ _
  have hU2' := hsub (mix Wt e) d
  have hU3 := hsub (mix (Wt - W) d) (α • gk)
  rw [frob_smul_left, frob_smul_right] at hU3
  have hWe := hKW e
  have hAd := hKA d
  have h1 : KW * frob e e ≤ KW * (2 * frob d d + 2 * frob D D) :=
    mul_le_mul_of_nonneg_left hee hKW0
  have h2 : Lf ^ 2 * frob e e ≤ Lf ^ 2 * (2 * frob d d + 2 * frob D D) :=
    mul_le_mul_of_nonneg_left hee (by positivity)
  have hgg0 := frob_self_nonneg gk
  have h3 : α * (α * frob gk gk) ≤ α ^ 2 * (Lf ^ 2 * frob e e) := by
    have := mul_le_mul_of_nonneg_left hg (sq_nonneg α)
    nlinarith
  have h4 : α ^ 2 * (Lf ^ 2 * frob e e) ≤
      α ^ 2 * (Lf ^ 2 * (2 * frob d d + 2 * frob D D)) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg α)
  have hKAD : 0 ≤ KA * frob D D := mul_nonneg hKA0 hDD
  have hUr' : frob (mix U r) (mix U r) ≤
      (8 * KW + 8 * α ^ 2 * Lf ^ 2 + 4 + 4 * KA) * (frob d d + frob D D) := by
    nlinarith
  have hrr : frob r r ≤ KR * ((8 * KW + 8 * α ^ 2 * Lf ^ 2 + 4 + 4 * KA) * (frob d d + frob D D)) :=
    le_trans hr (mul_le_mul_of_nonneg_left hUr' hKR0)
  have hdW : frob d (mix Wt d) ≤ (1 + KW) / 2 * (frob d d + frob D D) := by
    have := frob_two_mul_le 1 one_pos d (mix Wt d)
    have := hKW d
    have : 0 ≤ KW * frob D D := mul_nonneg hKW0 hDD
    nlinarith
  nlinarith

/-! ### main argument -/

set_option maxHeartbeats 1000000 in
theorem main_core {n p : ℕ} (W Wt U : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α μg : ℝ) (Gr : SimpleGraph (Fin n))
    (hA1 : ExtraConsensus.Linear.MixingAssumption Gr W Wt) (hA2 : ConvexLipschitzGrad f Lf)
    (hUs : Uᵀ = U) (hU2 : U * U = Wt - W)
    (lmin : ℝ) (hlmin : IsLamMin Wt lmin) (hα0 : 0 < α)
    (xs : EuclideanSpace ℝ (Fin p))
    (qs : Stack n p) (hopt : IsOptimalPair U α f qs (fun _ => xs))
    (hrsc : RSCAtStack (gradG α W Wt f) (fun _ => xs) μg)
    (hα : α * Lf ^ 2 < 2 * μg * lmin)
    (x0 : Stack n p) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ k : ℕ, (1 + δ) * zNormSq Wt (qSeq U (extraIter α W Wt f x0) (k + 1) - qs)
          (extraIter α W Wt f x0 (k + 1) - fun _ => xs)
          ≤ zNormSq Wt (qSeq U (extraIter α W Wt f x0) k - qs) (extraIter α W Wt f x0 k - fun _ => xs)) ∧
      ∃ C : ℝ, ∀ k : ℕ, mnormSq Wt (extraIter α W Wt f x0 k - fun _ => xs) ≤ C * ((1 + δ)⁻¹) ^ k := by
  obtain ⟨⟨pp, hpp⟩, hoptU, hUX⟩ := hopt
  obtain ⟨hμ, hrsc'⟩ := hrsc
  generalize hXs : (fun _ => xs : Stack n p) = Xs at hoptU hUX hrsc' ⊢
  generalize hx : extraIter α W Wt f x0 = x
  have hWts : Wtᵀ = Wt := hA1.symm_Wt
  have hWs : Wᵀ = W := hA1.symm_W
  have hAs : (Wt - W)ᵀ = Wt - W := by rw [transpose_sub, hWts, hWs]
  have hLf := hA2.Lf_nonneg
  have hl0 : 0 < lmin := by
    have : 0 ≤ α * Lf ^ 2 := by positivity
    by_contra hcon
    have hc : lmin ≤ 0 := le_of_not_gt hcon
    nlinarith
  have hrow : ∀ i, ∑ j, Wt i j = 1 := by
    intro i
    have h := congrFun hA1.null_one_sub_Wt i
    simp [Matrix.mulVec, dotProduct, Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.one_apply] at h
    linarith
  have hWtX : mix Wt Xs = Xs := by
    rw [← hXs, mix_const]
    funext i
    rw [hrow i, one_smul]
  have hUUX : mix (Wt - W) Xs = 0 := by rw [← hU2, mix_mul, hUX, mix_zero]
  obtain ⟨KR, hKR0, hKR⟩ := frob_range (p := p) hUs
  obtain ⟨KW, hKW0, hKW⟩ := frob_bound (p := p) hWts
  obtain ⟨KA, hKA0, hKA⟩ := frob_bound (p := p) hAs
  have hLip := frob_grad_lip hA2
  have hq0 : 0 ≤ α * Lf ^ 2 / (2 * lmin) := by positivity
  have hq1 : α * Lf ^ 2 / (2 * lmin) < μg := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hq2 : α * Lf ^ 2 / (2 * lmin) * lmin = α * Lf ^ 2 / 2 := by
    field_simp
  obtain ⟨t, ht_def⟩ : ∃ t, t = μg + α * Lf ^ 2 / (2 * lmin) := ⟨_, rfl⟩
  have ht : 0 < t := by linarith
  have ht1 : t < 2 * μg := by linarith
  have ht2 : α * Lf ^ 2 < t * lmin := by
    have : t * lmin = μg * lmin + α * Lf ^ 2 / 2 := by rw [ht_def, add_mul, hq2]
    nlinarith
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = min (t * lmin - α * Lf ^ 2) (α * t * (2 * μg - t)) := ⟨_, rfl⟩
  have hc0a : c0 ≤ t * lmin - α * Lf ^ 2 := hc0 ▸ min_le_left _ _
  have hc0b : c0 ≤ α * t * (2 * μg - t) := hc0 ▸ min_le_right _ _
  have hc0pos : 0 < c0 := by
    rw [hc0]
    refine lt_min (by linarith) ?_
    have : 0 < 2 * μg - t := by linarith
    positivity
  obtain ⟨KV, hKVdef⟩ : ∃ KV, KV = KR * (8 * KW + 8 * α ^ 2 * Lf ^ 2 + 4 + 4 * KA) + (1 + KW) / 2 + 1 :=
    ⟨_, rfl⟩
  have hKV : 0 < KV := by rw [hKVdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = c0 / (t * KV) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have step : ∀ k : ℕ, (1 + δ) * zNormSq Wt (qSeq U x (k + 1) - qs) (x (k + 1) - Xs)
      ≤ zNormSq Wt (qSeq U x k - qs) (x k - Xs) := by
    intro k
    have hR : x (k + 1) = mix Wt (x k) - mix U (qSeq U x k) - α • gradF f (x k) := by
      rw [← hx]; exact iter_rec α W Wt U f x0 hU2 k
    have hQ : qSeq U x (k + 1) = qSeq U x k + mix U (x (k + 1)) := by
      simp [qSeq, Finset.sum_range_succ]
    have hqs : mix U qs = -(α • gradF f Xs) := eq_neg_of_add_eq_zero_left hoptU
    have hk : mix U (qSeq U x k) = mix Wt (x k) - α • gradF f (x k) - x (k + 1) := by
      rw [hR]; abel
    have hUr : mix U (qSeq U x (k + 1) - qs) = mix Wt (x k - Xs) - (x (k + 1) - Xs)
        + mix (Wt - W) (x (k + 1) - Xs) - α • (gradF f (x k) - gradF f Xs) := by
      rw [hQ, mix_sub, mix_add, hk, hqs, ← mix_mul, hU2, mix_sub Wt, mix_sub (Wt - W), hWtX, hUUX,
        smul_sub]
      abel
    have hw : qSeq U x (k + 1) - qs = mix U (∑ t ∈ Finset.range (k + 1 + 1), x t - pp) := by
      rw [mix_sub, mix_sum, ← hpp]
      rfl
    have hr : frob (qSeq U x (k + 1) - qs) (qSeq U x (k + 1) - qs) ≤
        KR * frob (mix U (qSeq U x (k + 1) - qs)) (mix U (qSeq U x (k + 1) - qs)) := by
      rw [hw]; exact hKR _
    have hlow := delta_lower (t := t) hUs hU2 hWts hA1.half_sub_Wt_psd hlmin hLip hα0 ht (x k)
      (x (k + 1)) Xs (qSeq U x (k + 1) - qs) (hrsc' (x (k + 1))) hUr
    have hup := V_upper hKR0 hKW0 hKA0 hKW hKA hLip (x k) (x (k + 1)) Xs
      (qSeq U x (k + 1) - qs) hr hUr
    have hqk : qSeq U x k - qs = (qSeq U x (k + 1) - qs) - mix U (x (k + 1) - Xs) := by
      rw [mix_sub, hUX, sub_zero, hQ]; abel
    rw [← hKVdef] at hup
    unfold zNormSq mnormSq
    rw [hqk]
    generalize qSeq U x (k + 1) - qs = r at hlow hup ⊢
    have hdd := frob_self_nonneg (x (k + 1) - Xs)
    have hDD := frob_self_nonneg (x (k + 1) - x k)
    generalize frob (x (k + 1) - Xs) (x (k + 1) - Xs) = A at hlow hup hdd
    generalize frob (x (k + 1) - x k) (x (k + 1) - x k) = B at hlow hup hDD
    generalize frob r r + frob (x (k + 1) - Xs) (mix Wt (x (k + 1) - Xs)) = V1 at hlow hup ⊢
    generalize frob (r - mix U (x (k + 1) - Xs)) (r - mix U (x (k + 1) - Xs)) +
      frob (x k - Xs) (mix Wt (x k - Xs)) = V0 at hlow hup ⊢
    have hS : c0 * (A + B) ≤ t * (V0 - V1) := by
      have h1 := mul_le_mul_of_nonneg_right hc0a hDD
      have h2 := mul_le_mul_of_nonneg_right hc0b hdd
      nlinarith
    have h3 : δ * V1 ≤ δ * (KV * (A + B)) := mul_le_mul_of_nonneg_left hup hδ.le
    have h4 : δ * (KV * (A + B)) = c0 * (A + B) / t := by
      rw [hδdef]; field_simp
    have h5 : c0 * (A + B) / t ≤ V0 - V1 := by
      rw [div_le_iff₀ ht]; linarith
    linarith
  refine ⟨δ, hδ, step, zNormSq Wt (qSeq U x 0 - qs) (x 0 - Xs), fun k => ?_⟩
  have hV : ∀ k : ℕ, zNormSq Wt (qSeq U x k - qs) (x k - Xs) ≤
      zNormSq Wt (qSeq U x 0 - qs) (x 0 - Xs) * ((1 + δ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : zNormSq Wt (qSeq U x (k + 1) - qs) (x (k + 1) - Xs) ≤
          (1 + δ)⁻¹ * zNormSq Wt (qSeq U x k - qs) (x k - Xs) := by
        rw [le_inv_mul_iff₀ (by positivity)]; exact step k
      calc _ ≤ (1 + δ)⁻¹ * zNormSq Wt (qSeq U x k - qs) (x k - Xs) := h1
        _ ≤ (1 + δ)⁻¹ * (zNormSq Wt (qSeq U x 0 - qs) (x 0 - Xs) * ((1 + δ)⁻¹) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
  have := hV k
  have hq := frob_self_nonneg (qSeq U x k - qs)
  have hz : zNormSq Wt (qSeq U x k - qs) (x k - Xs) =
      frob (qSeq U x k - qs) (qSeq U x k - qs) + mnormSq Wt (x k - Xs) := rfl
  linarith

end EC37

open ExtraConsensus.Linear Matrix in
theorem solution {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α μg : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ExtraConsensus.Sublinear.ConvexLipschitzGrad f Lf) (hA3 : ExtraConsensus.Sublinear.SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (lmin : ℝ) (hlmin : ExtraConsensus.Sublinear.IsLamMin Wt lmin)
    (hα0 : 0 < α)
    (xs : EuclideanSpace ℝ (Fin p)) (hsol : ∀ y, ExtraConsensus.Sublinear.fbar f xs ≤ ExtraConsensus.Sublinear.fbar f y)
    (qs : ExtraConsensus.Sublinear.Stack n p) (hopt : ExtraConsensus.Sublinear.IsOptimalPair U α f qs (fun _ => xs))
    (hrsc : RSCAtStack (gradG α W Wt f) (fun _ => xs) μg)
    (hα : α * Lf ^ 2 < 2 * μg * lmin)
    (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    let q := ExtraConsensus.Sublinear.qSeq U x
    let Xs : ExtraConsensus.Sublinear.Stack n p := fun _ => xs
    ∃ δ : ℝ, 0 < δ ∧
      (∀ k : ℕ, (1 + δ) * ExtraConsensus.Sublinear.zNormSq Wt (q (k + 1) - qs) (x (k + 1) - Xs)
          ≤ ExtraConsensus.Sublinear.zNormSq Wt (q k - qs) (x k - Xs)) ∧
      ∃ C : ℝ, ∀ k : ℕ, ExtraConsensus.Sublinear.mnormSq Wt (x k - Xs) ≤ C * ((1 + δ)⁻¹) ^ k := by
  intro x q Xs
  exact EC37.main_core W Wt U f Lf α μg Gr hA1 hA2 hUs hU2 lmin hlmin hα0 xs qs hopt hrsc hα x0
