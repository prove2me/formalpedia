-- Prove2me | solution 1 for ByrdHansenNocedalSinger2016.cor3_3_paper_constant_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:02:27.061681+00:00
-- url     : https://prove2.me/submissions/4b8d442e-feb6-4c59-be0b-a1728e8aa3e2

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS
import Definitions.Def_StochQuasiNewton_SQN_Algorithm
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike
import Theorems.Thm_StochQuasiNewton_SQN_hessian_approx_eigenvalue_bounds
import Theorems.Thm_StochQuasiNewton_SQN_suboptimality_le_gradient_sq

open scoped RealInnerProductSpace
open StochQuasiNewton.SQN

namespace BHAux

variable {n N : ℕ}

lemma lbfgsStage_congr (M t : ℕ) (s y s' y' : ℕ → EuclideanSpace ℝ (Fin n))
    (h : ∀ j ≤ t, s j = s' j ∧ y j = y' j) :
    ∀ i ≤ min t M, lbfgsInverseStage M t s y i = lbfgsInverseStage M t s' y' i := by
  intro i
  induction i with
  | zero => intro _; simp only [lbfgsInverseStage, (h t le_rfl).1, (h t le_rfl).2]
  | succ i ih =>
    intro hi
    have hj : t - min t M + 1 + i ≤ t := by omega
    simp only [lbfgsInverseStage, ih (by omega), (h _ hj).1, (h _ hj).2]

lemma lbfgsMatrix_congr (M t : ℕ) (s y s' y' : ℕ → EuclideanSpace ℝ (Fin n))
    (h : ∀ j ≤ t, s j = s' j ∧ y j = y' j) :
    lbfgsMatrix M t s y = lbfgsMatrix M t s' y' :=
  lbfgsStage_congr M t s y s' y' h _ le_rfl

lemma blockAverage_congr (L : ℕ) (h h' : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ)
    (hh : ∀ j ≤ (t+1)*L, h j = h' j) : blockAverage L h t = blockAverage L h' t := by
  unfold blockAverage
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hh j (Finset.mem_Icc.mp hj).2

lemma corrS_congr (L : ℕ) (h h' : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ)
    (hh : ∀ j ≤ (t+1)*L, h j = h' j) : corrS L h t = corrS L h' t := by
  unfold corrS
  rw [blockAverage_congr L h h' t hh, blockAverage_congr L h h' (t-1)]
  intro j hj; apply hh
  have : (t - 1 + 1) * L ≤ (t+1)*L := Nat.mul_le_mul_right _ (by omega)
  omega

lemma corrY_congr (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (L : ℕ)
    (SH SH' : ℕ → Finset (Fin N)) (h h' : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ)
    (hh : ∀ j ≤ (t+1)*L, h j = h' j) (hS : SH t = SH' t) :
    corrY f L SH h t = corrY f L SH' h' t := by
  unfold corrY
  rw [corrS_congr L h h' t hh, blockAverage_congr L h h' t hh, hS]

lemma stepMatrix_congr_SH (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
    (SH SH' : ℕ → Finset (Fin N)) (h : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hS : ∀ j < k, SH j = SH' j) : stepMatrix f M L SH h k = stepMatrix f M L SH' h k := by
  unfold stepMatrix
  split_ifs with h2
  · rfl
  · apply lbfgsMatrix_congr
    intro j hj
    refine ⟨rfl, corrY_congr f L SH SH' h h j (fun _ _ => rfl) (hS j ?_)⟩
    have : (k-1)/L ≤ k - 1 := Nat.div_le_self _ _
    omega

section SA
variable (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ) (α : ℕ → ℝ)
  (w1 : EuclideanSpace ℝ (Fin n))

lemma hist_succ_eq (S SH : ℕ → Finset (Fin N)) (m j : ℕ) (hj : j ≤ m+1) :
    sqnHistory f M L α w1 S SH (m+1) j = sqnHistory f M L α w1 S SH m j := by
  simp only [sqnHistory]
  rw [if_neg (by omega)]

lemma hist_mono (S SH : ℕ → Finset (Fin N)) (m m' : ℕ) (hm : m ≤ m') (j : ℕ) (hj : j ≤ m+1) :
    sqnHistory f M L α w1 S SH m' j = sqnHistory f M L α w1 S SH m j := by
  induction m', hm using Nat.le_induction with
  | base => rfl
  | succ m' hmm ih => rw [hist_succ_eq f M L α w1 S SH m' j (by omega), ih]

lemma hist_congr (S SH S' SH' : ℕ → Finset (Fin N)) (m : ℕ)
    (hS : ∀ j ≤ m, S j = S' j) (hH : ∀ j < m, SH j = SH' j) :
    sqnHistory f M L α w1 S SH m = sqnHistory f M L α w1 S' SH' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e := ih (fun j hj => hS j (by omega)) (fun j hj => hH j (by omega))
    funext j
    simp only [sqnHistory]
    rw [e, stepMatrix_congr_SH f M L SH SH' _ (m+1) hH, hS (m+1) le_rfl]

lemma iter_congr (S SH S' SH' : ℕ → Finset (Fin N)) (k : ℕ) (hk : 1 ≤ k)
    (hS : ∀ j < k, S j = S' j) (hH : ∀ j < k, SH j = SH' j) :
    sqnIterate f M L α w1 S SH k = sqnIterate f M L α w1 S' SH' k := by
  unfold sqnIterate
  rw [hist_congr f M L α w1 S SH S' SH' (k-1) (fun j hj => hS j (by omega))
    (fun j hj => hH j (by omega))]

lemma applied_congr (S SH S' SH' : ℕ → Finset (Fin N)) (k : ℕ) (hk : 1 ≤ k)
    (hS : ∀ j < k, S j = S' j) (hH : ∀ j < k, SH j = SH' j) :
    sqnAppliedMatrix f M L α w1 S SH k = sqnAppliedMatrix f M L α w1 S' SH' k := by
  unfold sqnAppliedMatrix
  rw [hist_congr f M L α w1 S SH S' SH' (k-1) (fun j hj => hS j (by omega))
    (fun j hj => hH j (by omega)), stepMatrix_congr_SH f M L SH SH' _ k hH]

/-- the recursion -/
lemma iter_succ (S SH : ℕ → Finset (Fin N)) (k : ℕ) (hk : 1 ≤ k) :
    sqnIterate f M L α w1 S SH (k+1) = sqnIterate f M L α w1 S SH k -
      α k • Matrix.toEuclideanLin (sqnAppliedMatrix f M L α w1 S SH k)
        (miniBatchGrad f (S k) (sqnIterate f M L α w1 S SH k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold sqnIterate sqnAppliedMatrix
  simp only [Nat.add_sub_cancel]
  conv_lhs => simp only [sqnHistory]
  rw [if_pos trivial]

lemma applied_eq_approx (S SH : ℕ → Finset (Fin N)) (k : ℕ) (hk : ¬ (k-1)/L < 2) :
    sqnAppliedMatrix f M L α w1 S SH k = sqnHessianApprox f M L α w1 S SH ((k-1)/L - 1) := by
  unfold sqnAppliedMatrix stepMatrix sqnHessianApprox
  rw [if_neg hk]
  apply lbfgsMatrix_congr
  intro j hj
  have hle : (j+1)*L ≤ k - 1 := by
    have h1 : (j+1)*L ≤ ((k-1)/L)*L := Nat.mul_le_mul_right _ (by omega)
    have h2 : ((k-1)/L)*L ≤ k-1 := Nat.div_mul_le_self _ _
    omega
  have hh : ∀ i ≤ (j+1)*L, sqnHistory f M L α w1 S SH (k-1) i =
      sqnHistory f M L α w1 S SH ((j+1)*L) i :=
    fun i hi => hist_mono f M L α w1 S SH ((j+1)*L) (k-1) hle i (by omega)
  exact ⟨corrS_congr L _ _ j hh, corrY_congr f L SH SH _ _ j hh rfl⟩

lemma posDef_shift_lo {A : Matrix (Fin n) (Fin n) ℝ} {μ μ' : ℝ}
    (h : (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) (hle : μ' ≤ μ) :
    (A - μ' • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have : A - μ' • (1 : Matrix (Fin n) (Fin n) ℝ) =
      (A - μ • 1) + (μ - μ') • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [sub_smul]; abel
  rw [this]
  exact h.add_posSemidef (Matrix.PosSemidef.one.smul (by linarith))

lemma posDef_shift_hi {A : Matrix (Fin n) (Fin n) ℝ} {μ μ' : ℝ}
    (h : (μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosDef) (hle : μ ≤ μ') :
    (μ' • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosDef := by
  have : μ' • (1 : Matrix (Fin n) (Fin n) ℝ) - A =
      (μ • 1 - A) + (μ' - μ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [sub_smul]; abel
  rw [this]
  exact h.add_posSemidef (Matrix.PosSemidef.one.smul (by linarith))

theorem partI (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w)) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ 1/2 ∧ 2 ≤ μ₂ ∧
      (∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ t, (SH t).card = bH) →
        (∀ t, 1 ≤ t → sqnPairS f M L α w1 S SH t ≠ 0) →
        ∀ k, 1 ≤ k →
          (sqnAppliedMatrix f M L α w1 S SH k -
              μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) -
              sqnAppliedMatrix f M L α w1 S SH k).PosDef) := by
  obtain ⟨m1, m2, hm1, hm12, hB⟩ := hessian_approx_eigenvalue_bounds f hf lam Lam hlam hLam
    M L bH hM hL hbH hbHN hHess
  refine ⟨min m1 (1/2), max m2 2, lt_min hm1 (by norm_num), min_le_right _ _,
    le_max_right _ _, ?_⟩
  intro α w1 S SH hSH hpair k hk
  by_cases h2 : (k-1)/L < 2
  · have e : sqnAppliedMatrix f M L α w1 S SH k = 1 := by
      unfold sqnAppliedMatrix stepMatrix; rw [if_pos h2]
    rw [e]
    constructor
    · have : (1 : Matrix (Fin n) (Fin n) ℝ) - min m1 (1/2) • 1 =
          (1 - min m1 (1/2)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [sub_smul, one_smul]
      rw [this]
      exact Matrix.PosDef.one.smul (by have := min_le_right m1 (1/2:ℝ); linarith)
    · have : max m2 2 • (1 : Matrix (Fin n) (Fin n) ℝ) - 1 =
          (max m2 2 - 1) • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [sub_smul, one_smul]
      rw [this]
      exact Matrix.PosDef.one.smul (by have := le_max_right m2 (2:ℝ); linarith)
  · rw [applied_eq_approx f M L α w1 S SH k h2]
    have ht : 1 ≤ (k-1)/L - 1 := by omega
    obtain ⟨h1, h3⟩ := hB α w1 S SH hSH _ ht (fun j hj _ => hpair j hj)
    exact ⟨posDef_shift_lo h1 (min_le_left _ _), posDef_shift_hi h3 (le_max_left _ _)⟩

end SA

lemma quad_eq (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanLin A v, v⟫ = dotProduct (star v.ofLp) (A.mulVec v.ofLp) := by
  simp [PiLp.inner_apply, dotProduct, Matrix.mulVec]

lemma norm_sq_eq (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ^ 2 = dotProduct (star v.ofLp) v.ofLp := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [dotProduct, sq]

lemma quad_lo {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (h : (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    μ * ‖v‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A v, v⟫ := by
  have := h.posSemidef.dotProduct_mulVec_nonneg v.ofLp
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at this
  rw [quad_eq, norm_sq_eq]; linarith

lemma quad_hi {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (h : (μ • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanLin A v, v⟫ ≤ μ * ‖v‖ ^ 2 := by
  have := h.posSemidef.dotProduct_mulVec_nonneg v.ofLp
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at this
  rw [quad_eq, norm_sq_eq]; linarith

lemma herm_of {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (h : (A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) : A.IsHermitian := by
  have h1 := h.isHermitian
  have h2 : (μ • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    unfold Matrix.IsHermitian; simp
  have := h1.add h2
  simpa using this

lemma norm_apply_le {A : Matrix (Fin n) (Fin n) ℝ} {μ₁ μ₂ : ℝ} (hμ : 0 ≤ μ₁)
    (h1 : (A - μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (h2 : (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosDef) (v : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A v‖ ≤ μ₂ * ‖v‖ := by
  set T := Matrix.toEuclideanLin A
  have hsym : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (herm_of h1)
  have hpsd : ∀ x, 0 ≤ ⟪T x, x⟫ := fun x =>
    le_trans (by positivity) (quad_lo h1 x)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have hμ₂ : 0 ≤ μ₂ := by
    have := (quad_lo h1 v).trans (quad_hi h2 v)
    have : μ₁ ≤ μ₂ := le_of_mul_le_mul_right this hv2
    linarith
  -- Cauchy–Schwarz for the form ⟪T x, y⟫
  have cs : ∀ x y, ⟪T x, y⟫ ^ 2 ≤ ⟪T x, x⟫ * ⟪T y, y⟫ := by
    intro x y
    have hq : ∀ t : ℝ, 0 ≤ ⟪T y, y⟫ * (t * t) + (2 * ⟪T x, y⟫) * t + ⟪T x, x⟫ := by
      intro t
      have := hpsd (x + t • y)
      have e1 : ⟪T y, x⟫ = ⟪T x, y⟫ := by rw [hsym y x, real_inner_comm]
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, RCLike.conj_to_real, e1] at this
      nlinarith [this]
    have := discrim_le_zero hq
    unfold discrim at this
    nlinarith [this]
  have e : ⟪T v, T v⟫ = ‖T v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have c1 := cs v (T v)
  rw [e] at c1
  have c2 := quad_hi h2 (T v)
  have c3 := quad_hi h2 v
  have hTv : 0 ≤ ⟪T v, v⟫ := hpsd v
  have hTT : 0 ≤ ⟪T (T v), T v⟫ := hpsd _
  have key : (‖T v‖ ^ 2) ^ 2 ≤ (μ₂ * ‖v‖ ^ 2) * (μ₂ * ‖T v‖ ^ 2) :=
    c1.trans (mul_le_mul c3 c2 hTT (by nlinarith))
  by_contra hc
  push Not at hc
  have h0 : 0 ≤ μ₂ * ‖v‖ := by positivity
  have : (μ₂ * ‖v‖) ^ 2 < ‖T v‖ ^ 2 := by nlinarith
  nlinarith

lemma one_dim (φ ψ ψ' : ℝ → ℝ) (K : ℝ) (hφ : ∀ t, HasDerivAt φ (ψ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hK : ∀ t, ψ' t ≤ K) :
    φ 1 ≤ φ 0 + ψ 0 + K / 2 := by
  have hanti : Antitone (fun t => ψ t - K * t) := by
    apply antitone_of_hasDerivAt_nonpos (f' := fun t => ψ' t - K)
    · intro t
      exact ((hψ t).sub ((hasDerivAt_id t).const_mul K)).congr_deriv (by simp)
    · intro t; show ψ' t - K ≤ 0; linarith [hK t]
  let g : ℝ → ℝ := fun t => φ t - t * ψ 0 - K / 2 * t ^ 2
  have hg : ∀ t, HasDerivAt g (ψ t - ψ 0 - K * t) t := by
    intro t
    have h1 := ((hφ t).sub ((hasDerivAt_id t).mul_const (ψ 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (K / 2))
    exact h1.congr_deriv (by simp; ring)
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g (fun t => ψ t - ψ 0 - K * t)
    (by norm_num : (0:ℝ) < 1) (fun t _ => (hg t).continuousAt.continuousWithinAt)
    (fun t _ => hg t)
  have hc0 : ψ c - ψ 0 - K * c ≤ 0 := by
    have := hanti (le_of_lt hc.1); simp only at this; linarith
  rw [hcd] at hc0
  simp only [g] at hc0
  norm_num at hc0
  linarith

lemma grad_diff {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (gradient F) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have : gradient F = fun x => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ F x) := by
    funext x; rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp h1

lemma fderiv_eq_inner {F : EuclideanSpace ℝ (Fin n) → ℝ} (x d : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ F x d = ⟪gradient F x, d⟫ := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma descent (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (Λ : ℝ)
    (hH : ∀ x d, ⟪fderiv ℝ (gradient F) x d, d⟫ ≤ Λ * ‖d‖ ^ 2) (w d : EuclideanSpace ℝ (Fin n)) :
    F (w + d) ≤ F w + ⟪gradient F w, d⟫ + Λ / 2 * ‖d‖ ^ 2 := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hGd : Differentiable ℝ (gradient F) := (grad_diff hF).differentiable (by norm_num)
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w + t • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add w
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (w + t • d)) ⟪gradient F (w + t • d), d⟫ t := by
    intro t
    have := (hFd (w + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [fderiv_eq_inner] at this
    exact this
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ⟪gradient F (w + t • d), d⟫)
      ⟪fderiv ℝ (gradient F) (w + t • d) d, d⟫ t := by
    intro t
    have := ((hGd (w + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)).inner ℝ
      (hasDerivAt_const t d)
    simpa using this
  have := one_dim _ _ _ (Λ * ‖d‖ ^ 2) h1 h2 (fun t => hH _ _)
  simp only [one_smul, zero_smul, add_zero] at this
  linarith

section SB
variable (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)

lemma obj_contDiff (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (objective f) := by
  unfold objective
  exact contDiff_const.mul (ContDiff.sum fun i _ => hf i)

lemma grad_obj (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (objective f) x = (1 / (N : ℝ)) • ∑ i, gradient (f i) x := by
  have hd : ∀ i, DifferentiableAt ℝ (f i) x := fun i => (hf i).differentiable (by norm_num) x
  have hfd : HasFDerivAt (objective f) ((1 / (N : ℝ)) • ∑ i, fderiv ℝ (f i) x) x := by
    unfold objective
    exact (HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt).const_mul (1 / (N : ℝ))
  apply ext_inner_right ℝ
  intro v
  rw [← fderiv_eq_inner, hfd.fderiv, inner_smul_left, sum_inner]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    smul_eq_mul, fderiv_eq_inner, RCLike.conj_to_real]

lemma hess_obj (hf : ∀ i, ContDiff ℝ 2 (f i)) (x d : EuclideanSpace ℝ (Fin n)) :
    ⟪fderiv ℝ (gradient (objective f)) x d, d⟫ =
      (1 / (N : ℝ)) * ∑ i, ⟪fderiv ℝ (gradient (f i)) x d, d⟫ := by
  have e : gradient (objective f) = fun y => (1 / (N : ℝ)) • ∑ i, gradient (f i) y := by
    funext y; exact grad_obj f hf y
  have hd : ∀ i, DifferentiableAt ℝ (gradient (f i)) x := fun i =>
    (grad_diff (hf i)).differentiable (by norm_num) x
  have hfd : HasFDerivAt (gradient (objective f))
      ((1 / (N : ℝ)) • ∑ i, fderiv ℝ (gradient (f i)) x) x := by
    rw [e]
    exact (HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt).const_smul (1 / (N : ℝ))
  rw [hfd.fderiv]
  simp [inner_smul_left, sum_inner]

lemma hess_sub (SH : Finset (Fin N)) (x d : EuclideanSpace ℝ (Fin n)) :
    ⟪subsampledHessian f SH x d, d⟫ =
      (1 / (SH.card : ℝ)) * ∑ i ∈ SH, ⟪fderiv ℝ (gradient (f i)) x d, d⟫ := by
  unfold subsampledHessian
  simp [inner_smul_left, sum_inner]

end SB

abbrev PC (N b : ℕ) : Finset (Finset (Fin N)) := Finset.powersetCard b Finset.univ

lemma card_PC (b : ℕ) : (PC N b).card = N.choose b := by
  simp [PC, Finset.card_powersetCard]

lemma card_PC_pos (b : ℕ) (hbN : b ≤ N) : (0 : ℝ) < (PC N b).card := by
  rw [card_PC]; exact_mod_cast Nat.choose_pos hbN

lemma card_filter_mem (b : ℕ) (hb : 1 ≤ b) (i : Fin N) :
    ((PC N b).filter (fun s => i ∈ s)).card = (N-1).choose (b-1) := by
  have : ((PC N b).filter (fun s => i ∈ s)).card =
      (Finset.powersetCard (b-1) (Finset.univ.erase i)).card := by
    apply Finset.card_nbij' (fun s => s.erase i) (fun u => insert i u)
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
        true_and] at hs ⊢
      refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
      rw [Finset.card_erase_of_mem hs.2, hs.1]
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
        true_and] at hu ⊢
      have hi : i ∉ u := fun h => by simpa using hu.1 h
      refine ⟨?_, Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hi, hu.2]; omega
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter] at hs
      exact Finset.insert_erase hs.2
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hu
      have hi : i ∉ u := fun h => by simpa using hu.1 h
      exact Finset.erase_insert hi
  rw [this, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

lemma sum_sum_mem {V : Type*} [AddCommGroup V] [Module ℝ V] (b : ℕ) (hb : 1 ≤ b)
    (v : Fin N → V) :
    ∑ s ∈ PC N b, ∑ i ∈ s, v i = (((N-1).choose (b-1) : ℕ) : ℝ) • ∑ i, v i := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i => (PC N b).filter (fun s => i ∈ s))]
  · rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_const, card_filter_mem b hb i, Nat.cast_smul_eq_nsmul]
  · intro s i; simp [Finset.mem_filter]

lemma avg_vec {V : Type*} [AddCommGroup V] [Module ℝ V] (b : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N)
    (v : Fin N → V) :
    (1 / ((PC N b).card : ℝ)) • ∑ s ∈ PC N b, (1 / (b : ℝ)) • ∑ i ∈ s, v i =
      (1 / (N : ℝ)) • ∑ i, v i := by
  rw [← Finset.smul_sum, sum_sum_mem b hb, smul_smul, smul_smul, card_PC]
  congr 1
  have key := Nat.add_one_mul_choose_eq (N-1) (b-1)
  rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel hb] at key
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb' : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hC : (0:ℝ) < N.choose b := by exact_mod_cast Nat.choose_pos hbN
  have key' : (N:ℝ) * ((N-1).choose (b-1) : ℕ) = (N.choose b : ℕ) * b := by exact_mod_cast key
  field_simp
  linarith

lemma avg_real (b : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N) (r : Fin N → ℝ) :
    (∑ s ∈ PC N b, (1 / (b : ℝ)) * ∑ i ∈ s, r i) / ((PC N b).card : ℝ) =
      (1 / (N : ℝ)) * ∑ i, r i := by
  have := avg_vec b hb hbN r
  simp only [smul_eq_mul] at this
  rw [div_eq_inv_mul, ← one_div, this]

lemma norm_avg_sq_le {ι : Type*} (s : Finset ι) (hs : 0 < s.card)
    (v : ι → EuclideanSpace ℝ (Fin n)) :
    ‖(1 / (s.card : ℝ)) • ∑ i ∈ s, v i‖ ^ 2 ≤ (1 / (s.card : ℝ)) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hc : (0:ℝ) < s.card := by exact_mod_cast hs
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖v i‖)
  calc (1 / (s.card:ℝ)) ^ 2 * ‖∑ i ∈ s, v i‖ ^ 2
      ≤ (1 / (s.card:ℝ)) ^ 2 * (s.card * ∑ i ∈ s, ‖v i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = (1 / (s.card : ℝ)) * ∑ i ∈ s, ‖v i‖ ^ 2 := by field_simp

lemma sum_piFinset_snoc {X β : Type*} [DecidableEq X] [AddCommMonoid β] (t : Finset X) (k : ℕ)
    (G : (Fin (k+1) → X) → β) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin (k+1) => t), G σ =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin k => t), ∑ s ∈ t, G (Fin.snoc σ s) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => (Fin.snoc p.1 p.2 : Fin (k+1) → X))
    (fun σ => (Fin.init σ, σ (Fin.last k)))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hp.2
    · simpa using hp.1 j
  · intro σ hσ
    simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hσ ⊢
    exact ⟨fun j => hσ _, hσ _⟩
  · intro p _; simp
  · intro σ _; simp
  · intro p _; rfl

lemma ext_snoc {k : ℕ} (σ : Fin k → Finset (Fin N)) (s : Finset (Fin N)) :
    extendSamples (Fin.snoc σ s : Fin (k+1) → Finset (Fin N)) =
      Function.update (extendSamples σ) k s := by
  funext j
  unfold extendSamples
  rcases lt_trichotomy j k with h | rfl | h
  · rw [Function.update_of_ne (by omega), dif_pos (by omega), dif_pos h]
    exact Fin.snoc_castSucc (α := fun _ => Finset (Fin N)) (i := ⟨j, h⟩) ..
  · rw [Function.update_self, dif_pos (by omega)]
    exact Fin.snoc_last (α := fun _ => Finset (Fin N)) ..
  · rw [Function.update_of_ne (by omega), dif_neg (by omega), dif_neg (by omega)]

lemma card_PS (b k : ℕ) :
    (Fintype.piFinset (fun _ : Fin k => PC N b)).card = (PC N b).card ^ k := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem E_succ (b bH k : ℕ) (Φ : (ℕ → Finset (Fin N)) → (ℕ → Finset (Fin N)) → ℝ) :
    sampleExpectation N b bH (k+1) Φ = sampleExpectation N b bH k (fun S SH =>
      (∑ s ∈ PC N b, ∑ t ∈ PC N bH, Φ (Function.update S k s) (Function.update SH k t)) /
        (((PC N b).card : ℝ) * (PC N bH).card)) := by
  unfold sampleExpectation
  simp only [card_PS]
  rw [sum_piFinset_snoc]
  have e : ∀ σ : Fin k → Finset (Fin N), ∀ s ∈ PC N b,
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin (k+1) => PC N bH),
        Φ (extendSamples (Fin.snoc σ s : Fin (k+1) → Finset (Fin N))) (extendSamples τ) =
      ∑ τ ∈ Fintype.piFinset (fun _ : Fin k => PC N bH), ∑ t ∈ PC N bH,
        Φ (Function.update (extendSamples σ) k s) (Function.update (extendSamples τ) k t) := by
    intro σ s _
    rw [sum_piFinset_snoc]
    simp only [ext_snoc]
  rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (e σ))]
  simp only [← Finset.sum_div]
  rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_comm)]
  rw [div_div, pow_succ, pow_succ]
  congr 1
  push_cast
  ring

lemma E_const (b bH k : ℕ) (hbN : b ≤ N) (hbHN : bH ≤ N) (c : ℝ) :
    sampleExpectation N b bH k (fun _ _ => c) = c := by
  unfold sampleExpectation
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h1 := card_PC_pos (N := N) b hbN
  have h2 := card_PC_pos (N := N) bH hbHN
  simp only [card_PS]
  push_cast
  field_simp

lemma E_le (b bH k : ℕ) (hbN : b ≤ N) (hbHN : bH ≤ N)
    (Φ Ψ : (ℕ → Finset (Fin N)) → (ℕ → Finset (Fin N)) → ℝ)
    (h : ∀ σ ∈ Fintype.piFinset (fun _ : Fin k => PC N b),
      ∀ τ ∈ Fintype.piFinset (fun _ : Fin k => PC N bH),
        Φ (extendSamples σ) (extendSamples τ) ≤ Ψ (extendSamples σ) (extendSamples τ)) :
    sampleExpectation N b bH k Φ ≤ sampleExpectation N b bH k Ψ := by
  unfold sampleExpectation
  have h1 := card_PC_pos (N := N) b hbN
  have h2 := card_PC_pos (N := N) bH hbHN
  simp only [card_PS]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun σ hσ => Finset.sum_le_sum fun τ hτ => h σ hσ τ hτ

lemma E_affine (b bH k : ℕ) (hbN : b ≤ N) (hbHN : bH ≤ N)
    (Φ : (ℕ → Finset (Fin N)) → (ℕ → Finset (Fin N)) → ℝ) (a c : ℝ) :
    sampleExpectation N b bH k (fun S SH => a * Φ S SH + c) =
      a * sampleExpectation N b bH k Φ + c := by
  unfold sampleExpectation
  have h1 := card_PC_pos (N := N) b hbN
  have h2 := card_PC_pos (N := N) bH hbHN
  simp only [card_PS, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  push_cast
  field_simp


section SD
variable (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)

noncomputable def gs (w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) w‖ ^ 2

lemma avg_grad (hf : ∀ i, ContDiff ℝ 2 (f i)) (b : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N)
    (w : EuclideanSpace ℝ (Fin n)) :
    (1 / ((PC N b).card : ℝ)) • ∑ s ∈ PC N b, miniBatchGrad f s w =
      gradient (objective f) w := by
  rw [grad_obj f hf w, ← avg_vec b hb hbN (fun i => gradient (f i) w)]
  congr 1; apply Finset.sum_congr rfl; intro s hs
  unfold miniBatchGrad; rw [(Finset.mem_powersetCard.mp hs).2]

lemma grad_sq_le (hf : ∀ i, ContDiff ℝ 2 (f i)) (hN : 0 < N) (w : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (objective f) w‖ ^ 2 ≤ gs f w := by
  rw [grad_obj f hf]
  have := norm_avg_sq_le (Finset.univ : Finset (Fin N)) (by simp; omega)
    (fun i => gradient (f i) w)
  simpa [Finset.card_univ, gs] using this

lemma avg_mb_sq_le (b : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N) (w : EuclideanSpace ℝ (Fin n)) :
    (∑ s ∈ PC N b, ‖miniBatchGrad f s w‖ ^ 2) / ((PC N b).card : ℝ) ≤ gs f w := by
  rw [gs, ← avg_real b hb hbN]
  apply div_le_div_of_nonneg_right _ (card_PC_pos b hbN).le
  apply Finset.sum_le_sum
  intro s hs
  have hc := (Finset.mem_powersetCard.mp hs).2
  have := norm_avg_sq_le s (by omega) (fun i => gradient (f i) w)
  unfold miniBatchGrad
  rw [hc] at this ⊢
  exact this

lemma hessF (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (bH : ℕ) (hbH : 1 ≤ bH)
    (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (x d : EuclideanSpace ℝ (Fin n)) (hd : d ≠ 0) :
    lam * ‖d‖ ^ 2 < ⟪fderiv ℝ (gradient (objective f)) x d, d⟫ ∧
      ⟪fderiv ℝ (gradient (objective f)) x d, d⟫ < Lam * ‖d‖ ^ 2 := by
  rw [hess_obj f hf, ← avg_real bH hbH hbHN]
  have hP := card_PC_pos (N := N) bH hbHN
  have hne : (PC N bH).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hP
  have e : ∀ SH ∈ PC N bH, (1 / (bH : ℝ)) * ∑ i ∈ SH, ⟪fderiv ℝ (gradient (f i)) x d, d⟫ =
      ⟪subsampledHessian f SH x d, d⟫ := by
    intro SH hSH
    rw [hess_sub, (Finset.mem_powersetCard.mp hSH).2]
  rw [Finset.sum_congr rfl e]
  constructor
  · rw [lt_div_iff₀ hP]
    have := Finset.sum_lt_sum_of_nonempty hne (fun SH hSH =>
      (hHess SH (Finset.mem_powersetCard.mp hSH).2 x d hd).1)
    simpa [mul_comm] using this
  · rw [div_lt_iff₀ hP]
    have := Finset.sum_lt_sum_of_nonempty hne (fun SH hSH =>
      (hHess SH (Finset.mem_powersetCard.mp hSH).2 x d hd).2)
    simpa [mul_comm] using this

lemma step_bound (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hLam : 0 < Lam) (b bH : ℕ)
    (hb : 1 ≤ b) (hbN : b ≤ N) (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (μ₁ μ₂ : ℝ) (hμ₁ : 0 ≤ μ₁) (A : Matrix (Fin n) (Fin n) ℝ)
    (h1 : (A - μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (h2 : (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosDef) (α : ℝ) (hα : 0 ≤ α)
    (w : EuclideanSpace ℝ (Fin n)) :
    (∑ s ∈ PC N b, objective f (w - α • Matrix.toEuclideanLin A (miniBatchGrad f s w))) /
        ((PC N b).card : ℝ) ≤
      objective f w - α * μ₁ * ‖gradient (objective f) w‖ ^ 2 +
        Lam / 2 * α ^ 2 * μ₂ ^ 2 * gs f w := by
  set F := objective f
  set T := Matrix.toEuclideanLin A
  set u := gradient F w
  set K := Lam / 2 * α ^ 2 * μ₂ ^ 2
  have hF := obj_contDiff f hf
  have hH : ∀ x d, ⟪fderiv ℝ (gradient F) x d, d⟫ ≤ Lam * ‖d‖ ^ 2 := by
    intro x d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · exact (hessF f hf lam Lam bH hbH hbHN hHess x d hd).2.le
  have hterm : ∀ s ∈ PC N b, F (w - α • T (miniBatchGrad f s w)) ≤
      F w - α * ⟪u, T (miniBatchGrad f s w)⟫ + K * ‖miniBatchGrad f s w‖ ^ 2 := by
    intro s _
    have hd := descent F hF Lam hH w (-(α • T (miniBatchGrad f s w)))
    rw [← sub_eq_add_neg] at hd
    have hn : ‖T (miniBatchGrad f s w)‖ ≤ μ₂ * ‖miniBatchGrad f s w‖ :=
      norm_apply_le hμ₁ h1 h2 _
    have hn2 : ‖T (miniBatchGrad f s w)‖ ^ 2 ≤ μ₂ ^ 2 * ‖miniBatchGrad f s w‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [inner_neg_right, inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs] at hd
    have : Lam / 2 * (α ^ 2 * ‖T (miniBatchGrad f s w)‖ ^ 2) ≤
        K * ‖miniBatchGrad f s w‖ ^ 2 := by
      simp only [K]
      have := mul_le_mul_of_nonneg_left hn2 (by positivity : (0:ℝ) ≤ Lam / 2 * α ^ 2)
      nlinarith [this]
    linarith
  have hP := card_PC_pos (N := N) b hbN
  have hsum := Finset.sum_le_sum hterm
  have hg : ∑ s ∈ PC N b, miniBatchGrad f s w = ((PC N b).card : ℝ) • u := by
    have := avg_grad f hf b hb hbN w
    rw [show u = gradient (objective f) w from rfl, ← this, smul_smul, mul_one_div_cancel hP.ne', one_smul]
  have e : ∑ s ∈ PC N b, (F w - α * ⟪u, T (miniBatchGrad f s w)⟫ +
      K * ‖miniBatchGrad f s w‖ ^ 2) = ((PC N b).card : ℝ) * F w -
      α * (((PC N b).card : ℝ) * ⟪u, T u⟫) + K * ∑ s ∈ PC N b, ‖miniBatchGrad f s w‖ ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← inner_sum, ← map_sum, hg, map_smul, inner_smul_right, Finset.sum_const, nsmul_eq_mul]
  rw [e] at hsum
  have hq : μ₁ * ‖u‖ ^ 2 ≤ ⟪u, T u⟫ := by rw [real_inner_comm]; exact quad_lo h1 u
  have hgs := avg_mb_sq_le f b hb hbN w
  have hK : 0 ≤ K := by positivity
  rw [div_le_iff₀ hP]
  rw [div_le_iff₀ hP] at hgs
  nlinarith [mul_le_mul_of_nonneg_left hgs hK, mul_le_mul_of_nonneg_left hq hα,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hα) hP.le]

end SD

def fill {N k : ℕ} (σ : Fin k → Finset (Fin N)) (s0 : Finset (Fin N)) : ℕ → Finset (Fin N) :=
  fun j => if h : j < k then σ ⟨j, h⟩ else s0

lemma fill_card {N k b : ℕ} (σ : Fin k → Finset (Fin N)) (s0 : Finset (Fin N))
    (hσ : σ ∈ Fintype.piFinset (fun _ : Fin k => PC N b)) (hs0 : s0.card = b) (j : ℕ) :
    (fill σ s0 j).card = b := by
  unfold fill
  split_ifs with h
  · exact (Finset.mem_powersetCard.mp (Fintype.mem_piFinset.mp hσ _)).2
  · exact hs0

lemma fill_eq {N k : ℕ} (σ : Fin k → Finset (Fin N)) (s0 : Finset (Fin N)) (j : ℕ) (hj : j < k) :
    fill σ s0 j = extendSamples σ j := by
  unfold fill extendSamples; rw [dif_pos hj, dif_pos hj]

lemma real_step (k c Q D a : ℝ) (hk : 0 < k) (hkc : c ≤ k) (hQ0 : 0 ≤ Q)
    (hD : D ≤ (c - 1) * Q) (ih : a ≤ Q / k) :
    (1 - c / k) * a + D / k ^ 2 ≤ Q / (k + 1) := by
  have hk1 : 0 < k + 1 := by linarith
  have h1 : (1 - c / k) * a ≤ (1 - c / k) * (Q / k) :=
    mul_le_mul_of_nonneg_left ih (by rw [sub_nonneg, div_le_one hk]; exact hkc)
  have e : (1 - c / k) * (Q / k) + D / k ^ 2 = (k * Q - c * Q + D) / k ^ 2 := by
    field_simp
  have h2 : (k * Q - c * Q + D) / k ^ 2 ≤ Q / (k + 1) := by
    rw [div_le_div_iff₀ (by positivity) hk1]
    have h3 : (k * Q - c * Q + D) * (k + 1) ≤ (k * Q - Q) * (k + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hk1.le
    have h4 : (k * Q - Q) * (k + 1) = Q * k ^ 2 - Q := by ring
    linarith
  linarith

end BHAux

open BHAux in
theorem solution {n N : ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (M L b bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) (hb : 1 ≤ b) (hbN : b ≤ N) (hbH : 1 ≤ bH)
    (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn (objective f) Set.univ wstar) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      (∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
        (∀ t, 1 ≤ t → sqnPairS f M L α w1 S SH t ≠ 0) →
        ∀ k, 1 ≤ k →
          (sqnAppliedMatrix f M L α w1 S SH k -
              μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) -
              sqnAppliedMatrix f M L α w1 S SH k).PosDef) ∧
      (∀ (β γ : ℝ) (w1 : EuclideanSpace ℝ (Fin n)), 1 / (2 * μ₁ * lam) < β →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ t, 1 ≤ t → sqnPairS f M L (fun k => β / k) w1 S SH t ≠ 0) →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ k, 1 ≤ k →
            (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) (sqnIterate f M L (fun k => β / k) w1 S SH k)‖ ^ 2
              ≤ γ ^ 2) →
        ∀ k, 1 ≤ k →
          sampleExpectation N b bH k (fun S SH =>
              objective f (sqnIterate f M L (fun k => β / k) w1 S SH k) - objective f wstar) ≤
            max (Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / (2 * (2 * μ₁ * lam * β - 1)))
                (objective f w1 - objective f wstar) / k) := by
  obtain ⟨μ₁, μ₂, hμ₁, hμ₁h, hμ₂2, hI⟩ :=
    partI f M L hf lam Lam hlam hLam bH hM hL hbH hbHN hHess
  refine ⟨μ₁, μ₂, hμ₁, by linarith, fun α w1 S SH _ hSH hpair k hk =>
    hI α w1 S SH hSH hpair k hk, ?_⟩
  intro β γ w1 hβ hpair hγ
  set F := objective f with hFdef
  have hF := obj_contDiff f hf
  have hN : 0 < N := by omega
  have hPL : ∀ w, 2 * lam * (F w - F wstar) ≤ ‖gradient F w‖ ^ 2 :=
    (suboptimality_le_gradient_sq F hF lam hlam
      (fun w v hv => (hessF f hf lam Lam bH hbH hbHN hHess w v hv).1) wstar hwstar).2
  have hgap : 0 ≤ F w1 - F wstar := sub_nonneg.mpr (isMinOn_iff.mp hwstar w1 (Set.mem_univ _))
  have h2ml : 0 < 2 * μ₁ * lam := by positivity
  have hβpos : 0 < β := lt_trans (by positivity) hβ
  have hc : 1 < 2 * μ₁ * lam * β := by
    rw [div_lt_iff₀ h2ml] at hβ; linarith
  set c := 2 * μ₁ * lam * β with hcdef
  set αs : ℕ → ℝ := fun k => β / k with hαs
  set X := Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / (2 * (c - 1)) with hX
  set Q := max X (F w1 - F wstar) with hQ
  have hQ0 : 0 ≤ Q := le_trans hgap (le_max_right _ _)
  set a : ℕ → ℝ := fun k => sampleExpectation N b bH k
    (fun S SH => F (sqnIterate f M L αs w1 S SH k) - F wstar) with ha
  show ∀ k, 1 ≤ k → a k ≤ Q / k
  -- samples
  obtain ⟨s0, hs0⟩ := (Finset.powersetCard_nonempty (s := (Finset.univ : Finset (Fin N)))
    (n := b)).mpr (by simp; omega)
  obtain ⟨t0, ht0⟩ := (Finset.powersetCard_nonempty (s := (Finset.univ : Finset (Fin N)))
    (n := bH)).mpr (by simp; omega)
  have hs0c := (Finset.mem_powersetCard.mp hs0).2
  have ht0c := (Finset.mem_powersetCard.mp ht0).2
  -- facts along a history
  have hBnd : ∀ k, 1 ≤ k → ∀ σ ∈ Fintype.piFinset (fun _ : Fin k => PC N b),
      ∀ τ ∈ Fintype.piFinset (fun _ : Fin k => PC N bH),
      (sqnAppliedMatrix f M L αs w1 (extendSamples σ) (extendSamples τ) k -
        μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
      (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) -
        sqnAppliedMatrix f M L αs w1 (extendSamples σ) (extendSamples τ) k).PosDef := by
    intro k hk σ hσ τ hτ
    rw [← applied_congr f M L αs w1 (fill σ s0) (fill τ t0) _ _ k hk
      (fun j hj => fill_eq σ s0 j hj) (fun j hj => fill_eq τ t0 j hj)]
    exact hI αs w1 (fill σ s0) (fill τ t0) (fill_card τ t0 hτ ht0c)
      (hpair _ _ (fill_card σ s0 hσ hs0c) (fill_card τ t0 hτ ht0c)) k hk
  have hGs : ∀ k, 1 ≤ k → ∀ σ ∈ Fintype.piFinset (fun _ : Fin k => PC N b),
      ∀ τ ∈ Fintype.piFinset (fun _ : Fin k => PC N bH),
      gs f (sqnIterate f M L αs w1 (extendSamples σ) (extendSamples τ) k) ≤ γ ^ 2 := by
    intro k hk σ hσ τ hτ
    rw [← iter_congr f M L αs w1 (fill σ s0) (fill τ t0) _ _ k hk
      (fun j hj => fill_eq σ s0 j hj) (fun j hj => fill_eq τ t0 j hj)]
    exact hγ _ _ (fill_card σ s0 hσ hs0c) (fill_card τ t0 hτ ht0c) k hk
  -- crude bound
  have hcrude : ∀ k, 1 ≤ k → a k ≤ γ ^ 2 / (2 * lam) := by
    intro k hk
    have := E_le (N := N) b bH k hbN hbHN
      (fun S SH => F (sqnIterate f M L αs w1 S SH k) - F wstar) (fun _ _ => γ ^ 2 / (2 * lam))
      (by
        intro σ hσ τ hτ
        have h1 := hPL (sqnIterate f M L αs w1 (extendSamples σ) (extendSamples τ) k)
        have h2 := grad_sq_le f hf hN (sqnIterate f M L αs w1 (extendSamples σ) (extendSamples τ) k)
        have h3 := hGs k hk σ hσ τ hτ
        rw [le_div_iff₀ (by positivity)]
        linarith)
    rwa [E_const (N := N) b bH k hbN hbHN] at this
  -- one step
  have hstep : ∀ k, 1 ≤ k → a (k+1) ≤ (1 - c / k) * a k +
      Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / 2 / (k:ℝ) ^ 2 := by
    intro k hk
    have hkpos : (0:ℝ) < k := by exact_mod_cast hk
    simp only [ha]
    rw [E_succ, ← E_affine (N := N) b bH k hbN hbHN]
    apply E_le (N := N) b bH k hbN hbHN
    intro σ hσ τ hτ
    set S := extendSamples σ
    set SH := extendSamples τ
    set w := sqnIterate f M L αs w1 S SH k
    set A := sqnAppliedMatrix f M L αs w1 S SH k
    have hupd : ∀ s t, sqnIterate f M L αs w1 (Function.update S k s) (Function.update SH k t)
        (k+1) = w - αs k • Matrix.toEuclideanLin A (miniBatchGrad f s w) := by
      intro s t
      rw [iter_succ f M L αs w1 _ _ k hk, Function.update_self,
        iter_congr f M L αs w1 (Function.update S k s) (Function.update SH k t) S SH k hk
          (fun j hj => Function.update_of_ne (by omega) _ _)
          (fun j hj => Function.update_of_ne (by omega) _ _),
        applied_congr f M L αs w1 (Function.update S k s) (Function.update SH k t) S SH k hk
          (fun j hj => Function.update_of_ne (by omega) _ _)
          (fun j hj => Function.update_of_ne (by omega) _ _)]
    simp only [hupd, Finset.sum_const, nsmul_eq_mul]
    have hPb := card_PC_pos (N := N) b hbN
    have hPH := card_PC_pos (N := N) bH hbHN
    have e : (∑ s ∈ PC N b, ((PC N bH).card : ℝ) *
        (F (w - αs k • Matrix.toEuclideanLin A (miniBatchGrad f s w)) - F wstar)) /
        (((PC N b).card : ℝ) * (PC N bH).card) =
        (∑ s ∈ PC N b, F (w - αs k • Matrix.toEuclideanLin A (miniBatchGrad f s w))) /
          ((PC N b).card : ℝ) - F wstar := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [e]
    obtain ⟨hA1, hA2⟩ := hBnd k hk σ hσ τ hτ
    have hsb := step_bound f hf lam Lam hLam b bH hb hbN hbH hbHN hHess μ₁ μ₂ hμ₁.le A hA1 hA2
      (αs k) (by simp only [hαs]; positivity) w
    have hpl := hPL w
    have hg := hGs k hk σ hσ τ hτ
    have hαk : αs k = β / k := rfl
    rw [hαk] at hsb
    have e1 : β / k * μ₁ * ‖gradient F w‖ ^ 2 ≥ c / k * (F w - F wstar) := by
      have : c / k * (F w - F wstar) = β / k * μ₁ * (2 * lam * (F w - F wstar)) := by
        simp only [hcdef]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hpl (by positivity)
    have e2 : Lam / 2 * (β / k) ^ 2 * μ₂ ^ 2 * gs f w ≤
        Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / 2 / (k:ℝ) ^ 2 := by
      have : Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / 2 / (k:ℝ) ^ 2 =
          Lam / 2 * (β / k) ^ 2 * μ₂ ^ 2 * γ ^ 2 := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    nlinarith [hsb, e1, e2]
  -- n = 0 case
  by_cases hn : n = 0
  · subst hn
    intro k hk
    have : a k = 0 := by
      simp only [ha]
      have e : (fun S SH => F (sqnIterate f M L αs w1 S SH k) - F wstar) = fun _ _ => (0:ℝ) := by
        funext S SH
        rw [Subsingleton.elim (sqnIterate f M L αs w1 S SH k) wstar, sub_self]
      rw [e, E_const (N := N) b bH k hbN hbHN]
    rw [this]; positivity
  have hlL : lam ≤ Lam := by
    let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, by omega⟩ : Fin n) 1
    have hv : v ≠ 0 := by
      intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x (⟨0, by omega⟩ : Fin n)) h
      simp [v] at this
    have hh := hHess t0 ht0c w1 v hv
    have hv2 : 0 < ‖v‖ ^ 2 := by positivity
    have := hh.1.trans hh.2
    exact (le_of_mul_le_mul_right this.le hv2)
  have hXQ : X ≤ Q := le_max_left _ _
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have : a 1 = F w1 - F wstar := by
      simp only [ha]
      have e : (fun S SH => F (sqnIterate f M L αs w1 S SH 1) - F wstar) =
          fun _ _ => F w1 - F wstar := by
        funext S SH; rfl
      rw [e, E_const (N := N) b bH 1 hbN hbHN]
    rw [this, Nat.cast_one, div_one]; exact le_max_right _ _
  | succ k hk ih =>
    have hkpos : (0:ℝ) < k := by exact_mod_cast hk
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by linarith
    push_cast
    by_cases hkc : (k:ℝ) < c
    · -- crude
      refine (hcrude (k+1) (by omega)).trans ?_
      have hineq : ((k:ℝ) + 1) * (c - 1) ≤ lam * Lam * μ₂ ^ 2 * β ^ 2 := by
        have h1 : ((k:ℝ) + 1) * (c - 1) ≤ (c + 1) * (c - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have h2 : c ^ 2 ≤ lam * Lam * μ₂ ^ 2 * β ^ 2 := by
          have hm : (2 * μ₁) ^ 2 ≤ μ₂ ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
          have : c ^ 2 = lam * lam * (2 * μ₁) ^ 2 * β ^ 2 := by simp only [hcdef]; ring
          rw [this]
          have hl : lam * lam ≤ lam * Lam := mul_le_mul_of_nonneg_left hlL hlam.le
          have := mul_le_mul hl hm (by positivity) (by positivity)
          nlinarith [sq_nonneg β, this]
        nlinarith
      have : γ ^ 2 / (2 * lam) ≤ X / ((k:ℝ) + 1) := by
        rw [hX, div_div, div_le_div_iff₀ (by positivity) (by nlinarith)]
        have := mul_le_mul_of_nonneg_left hineq (sq_nonneg γ)
        nlinarith [this]
      exact this.trans (div_le_div_of_nonneg_right hXQ hk1.le)
    · push Not at hkc
      refine (hstep k hk).trans ?_
      have hD : Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / 2 ≤ (c - 1) * Q := by
        have : Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / 2 = (c - 1) * X := by
          have hc1 : c - 1 ≠ 0 := by linarith
          rw [hX]; field_simp
        rw [this]; exact mul_le_mul_of_nonneg_left hXQ (by linarith)
      exact real_step (k:ℝ) c Q _ (a k) hkpos hkc hQ0 hD ih

