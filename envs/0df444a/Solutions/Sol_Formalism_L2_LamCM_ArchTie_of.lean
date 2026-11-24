-- Prove2me | solution 1 for Formalism.L2.LamCM.ArchTie_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:13:14.798477+00:00
-- url     : https://prove2.me/submissions/1bc1d17a-218a-4337-84c7-faf104d8dea6

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
open scoped ComplexOrder
namespace Formalism.L2.LamCM
private theorem exists_conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.PosDef) :
    ∃ S : Matrix n n ℂ, H = Sᴴ * S := by
  have hA := hH.posSemidef
  let U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ)
  let d : n → ℂ := fun i => (RCLike.ofReal (Real.sqrt (hA.1.eigenvalues i)) : ℂ)
  have hd : ∀ i, star (d i) * d i = (RCLike.ofReal (hA.1.eigenvalues i) : ℂ) := by
    intro i
    simp only [d, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
  refine ⟨Matrix.diagonal d * star U, ?_⟩
  have h1 : (Matrix.diagonal d * star U)ᴴ * (Matrix.diagonal d * star U) =
      U * Matrix.diagonal (fun i => star (d i) * d i) * star U := by
    simp only [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (Matrix.diagonal d)), Matrix.star_eq_conjTranspose (Matrix.diagonal d),
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rfl
  have hdiag : (fun i => star (d i) * d i) = RCLike.ofReal ∘ hA.1.eigenvalues := funext fun i => hd i
  have hs := hA.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  rw [h1, hdiag]
  exact hs
private theorem eval_bind₁' {σ τ : Type} (f : σ → MvPolynomial τ ℂ) (x : τ → ℂ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.bind₁ f P) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) P := by
  induction P using MvPolynomial.induction_on <;> simp_all
private theorem hq_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.hq (Sᴴ * S) u = ∑ k, ‖(S *ᵥ u) k‖ ^ 2 := by
  unfold ReciprocityTheory.MultiplicativeHeights.hq
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
private theorem colNormSq_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ReciprocityTheory.MultiplicativeHeights.colNormSq M i = ‖colE M i‖ ^ 2 := by
  unfold ReciprocityTheory.MultiplicativeHeights.colNormSq colE
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
private theorem colE_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : colE (M + N) i = colE M i + colE N i := by
  first
  | (ext k; simp [colE])
  | (simp only [colE, ← WithLp.toLp_add]; rfl)
private theorem norm_colE_smul_one {n : ℕ} (t : ℂ) (i : Fin n) : ‖colE (t • (1 : Matrix (Fin n) (Fin n) ℂ)) i‖ = ‖t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (colE _ i)), ← colNormSq_eq]
  unfold ReciprocityTheory.MultiplicativeHeights.colNormSq
  rw [Finset.sum_eq_single i]
  · simp [Real.sqrt_sq (norm_nonneg t)]
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp
private theorem norm_toLp_mulVec {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    ‖(WithLp.toLp 2 (S *ᵥ u) : EuclideanSpace ℂ (Fin n))‖ = Real.sqrt (ReciprocityTheory.MultiplicativeHeights.hq (Sᴴ * S) u) := by
  rw [hq_eq, EuclideanSpace.norm_eq]
private theorem colE_mul {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (W : Fin n → Fin n → ℂ) (i : Fin n) :
    colE (S * Matrix.of fun k i' => ∑ j, U j k * W i' j) i =
      ∑ j, W i j • (WithLp.toLp 2 (S *ᵥ U j) : EuclideanSpace ℂ (Fin n)) := by
  ext k
  simp [colE, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem finite_det_add_smul_one_eq_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ({t : ℂ | (Y + t • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0}).Finite := by
  refine (Polynomial.finite_setOf_isRoot (Matrix.charpoly_monic (-Y)).ne_zero).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  have hm : Matrix.scalar (Fin n) t - -Y = Y + t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [sub_neg_eq_add, add_comm]
    congr 1
    simp [Matrix.smul_one_eq_diagonal]
  rw [hm]
  exact ht
end Formalism.L2.LamCM
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.LamCM
open Filter Topology
namespace Formalism.L2.LamCM
theorem _root_.solution (hH : ReciprocityTheory.MultiplicativeHeights.LemmaHStatement) : ArchTie := by
  intro B _ _ m a P Hm U nn C La r hpd heq hC hnn hLa hr hU z hz
  choose S hS using fun b => exists_conjTranspose_mul_self (Hm b) (hpd b)
  have hSdet : ∀ b, IsUnit (S b).det := by
    intro b
    have := (hpd b).det_pos
    rw [hS b, det_mul, det_conjTranspose] at this
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  let P' : (∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) → ℂ := fun Y => evalFr P (fun b => (S b)⁻¹ * Y b)
  let X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ := fun b => Matrix.of fun k i => ∑ j, U b j k * z ⟨b, (i, j)⟩
  have h0 : MvPolynomial.eval z (substFr U P) = evalFr P X := by
    unfold substFr evalFr
    rw [eval_bind₁']
    refine congrArg (fun f => MvPolynomial.eval f P) (funext fun v => ?_)
    simp [X, mul_comm]
  let Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ := fun b => S b * X b
  have hequiv : ∀ (x : ∀ s, Matrix (Fin (m s)) (Fin (m s)) ℂ) (s : B) (bb : Matrix (Fin (m s)) (Fin (m s)) ℂ),
      (∀ t, (x t).det ≠ 0) → bb.det ≠ 0 → bb.BlockTriangular id →
      P' (Function.update x s (x s * bb)) = ReciprocityTheory.MultiplicativeHeights.triChar (a s) bb * P' x := by
    intro x s bb hx hb htri
    have e : (fun t => (S t)⁻¹ * Function.update x s (x s * bb) t) =
        Function.update (fun t => (S t)⁻¹ * x t) s ((S s)⁻¹ * x s * bb) := by
      funext t
      rw [Function.apply_update (fun t (M : Matrix (Fin (m t)) (Fin (m t)) ℂ) => (S t)⁻¹ * M) x s (x s * bb) t,
        Matrix.mul_assoc]
    show evalFr P _ = _ * evalFr P _
    rw [e]
    refine heq (fun t => (S t)⁻¹ * x t) s bb (fun t => ?_) hb htri
    rw [det_mul]
    exact mul_ne_zero (isUnit_nonsing_inv_det _ (hSdet t)).ne_zero (hx t)
  have hunit : ∀ k : ∀ s, Matrix (Fin (m s)) (Fin (m s)) ℂ,
      (∀ s, k s ∈ Matrix.unitaryGroup (Fin (m s)) ℂ) → ‖P' k‖ ≤ C := by
    intro k hk
    refine hC _ fun b => ?_
    have e1 : S b * (S b)⁻¹ = 1 := mul_nonsing_inv _ (hSdet b)
    have e2 : ((S b)⁻¹)ᴴ * (S b)ᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
    have e3 : (k b)ᴴ * k b = 1 := by
      have := (mem_unitaryGroup_iff').mp (hk b)
      rwa [star_eq_conjTranspose] at this
    rw [hS b, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (S b) (S b)⁻¹ (k b), e1, Matrix.one_mul, ← Matrix.mul_assoc ((S b)⁻¹)ᴴ, e2,
      Matrix.one_mul, e3]
  have hcolY : ∀ b i, ‖colE (Y b) i‖ ≤ r * La := by
    intro b i
    have e : Y b = S b * Matrix.of fun k i' => ∑ j, U b j k * (fun i' j => z ⟨b, (i', j)⟩) i' j := rfl
    rw [e, colE_mul]
    calc _ ≤ ∑ j, ‖z ⟨b, (i, j)⟩ • (WithLp.toLp 2 (S b *ᵥ U b j) : EuclideanSpace ℂ (Fin (m b)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin (m b), La := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul, norm_toLp_mulVec, ← hS b]
          have h1 : Real.sqrt (ReciprocityTheory.MultiplicativeHeights.hq (Hm b) (U b j)) ≤ La * nn b j := by
            calc _ ≤ Real.sqrt ((La * nn b j) ^ 2) := Real.sqrt_le_sqrt (hU b j)
              _ = La * nn b j := Real.sqrt_sq (mul_nonneg hLa (hnn b j).le)
          calc _ ≤ ‖z ⟨b, (i, j)⟩‖ * (La * nn b j) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
            _ = La * (‖z ⟨b, (i, j)⟩‖ * nn b j) := by ring
            _ ≤ La * 1 := mul_le_mul_of_nonneg_left (hz ⟨b, (i, j)⟩) hLa
            _ = La := mul_one La
      _ = (m b : ℝ) * La := by simp
      _ ≤ r * La := mul_le_mul_of_nonneg_right (by exact_mod_cast hr b) hLa
  have hbound : ∀ t : ℂ, (∀ b, (Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)).det ≠ 0) →
      ‖P' (fun b => Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ))‖ ≤
        C * ((r : ℝ) * La + ‖t‖) ^ (∑ b, ∑ i, a b i) := by
    intro t ht
    refine hH B m a P' C ((r : ℝ) * La + ‖t‖) hequiv hunit
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hLa) (norm_nonneg _)) _ ht fun b j => ?_
    rw [colNormSq_eq, colE_add]
    have : ‖colE (Y b) j + colE (t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)) j‖ ≤ r * La + ‖t‖ :=
      (norm_add_le _ _).trans (add_le_add (hcolY b j) (norm_colE_smul_one t j).le)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℂ), ∀ b, (Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)).det ≠ 0 := by
    rw [Filter.eventually_all]
    intro b
    have hF := finite_det_add_smul_one_eq_zero (Y b)
    have hc : IsClosed ({t : ℂ | (Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)).det = 0} \ {0}) :=
      (hF.subset Set.sdiff_subset).isClosed
    have h1 : ({t : ℂ | (Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)).det = 0} \ {0})ᶜ ∈ 𝓝 (0:ℂ) :=
      hc.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht1 ht2
    intro hdet
    exact ht1 ⟨hdet, ht2⟩
  have hcont : Continuous fun t : ℂ => P' (fun b => Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)) := by
    show Continuous fun t : ℂ => MvPolynomial.eval
      (fun v : FrVar m => ((S v.1)⁻¹ * (Y v.1 + t • (1 : Matrix (Fin (m v.1)) (Fin (m v.1)) ℂ))) v.2.2 v.2.1) P
    refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun v => ?_)
    exact (continuous_const.matrix_mul (continuous_const.add (continuous_id.smul continuous_const))).matrix_elem _ _
  have hf : Tendsto (fun t : ℂ => ‖P' (fun b => Y b + t • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ))‖) (𝓝[≠] (0:ℂ))
      (𝓝 ‖P' (fun b => Y b + (0:ℂ) • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ))‖) :=
    ((continuous_norm.comp hcont).tendsto 0).mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun t : ℂ => C * ((r : ℝ) * La + ‖t‖) ^ (∑ b, ∑ i, a b i)) (𝓝[≠] (0:ℂ))
      (𝓝 (C * ((r : ℝ) * La + ‖(0:ℂ)‖) ^ (∑ b, ∑ i, a b i))) :=
    ((((continuous_const.add continuous_norm).pow _).const_mul C).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := le_of_tendsto_of_tendsto hf hg (hev.mono fun t ht => hbound t ht)
  have hP0 : P' (fun b => Y b + (0:ℂ) • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)) = evalFr P X := by
    show evalFr P _ = _
    congr 1
    funext b
    show (S b)⁻¹ * (S b * X b + (0:ℂ) • (1 : Matrix (Fin (m b)) (Fin (m b)) ℂ)) = X b
    rw [zero_smul, add_zero, ← Matrix.mul_assoc, nonsing_inv_mul _ (hSdet b), Matrix.one_mul]
  rw [hP0, norm_zero, add_zero] at hlim
  rw [h0]
  exact hlim
end Formalism.L2.LamCM
