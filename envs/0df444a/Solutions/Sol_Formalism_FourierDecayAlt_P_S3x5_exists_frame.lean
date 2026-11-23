-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:08.908524+00:00
-- url     : https://prove2.me/submissions/d5db6626-e364-44dc-9b6c-19f0d222ed60

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_polar
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_gram_submatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    {ν : Type} [Fintype ν] [DecidableEq ν] (J : Matrix ν ν K) (hJ : Jᴴ = J) (hd : IsUnit J.det)
    (m : ℕ) (hm : m ≤ Fintype.card ν) : ∃ X : Matrix ν (Fin m) K, Xᴴ * J * X = 1 := by
  induction m with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ m ih =>
    obtain ⟨X, hX⟩ := ih (by omega)
    let f : Matrix ν Unit K →ₗ[K] Matrix (Fin m) Unit K :=
      { toFun := fun Y => Xᴴ * J * Y
        map_add' := fun a b => Matrix.mul_add _ _ _
        map_smul' := fun c a => by simp }
    have hf : ∀ Y, f Y = Xᴴ * J * Y := fun _ => rfl
    have hker : LinearMap.ker f ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_matrix, Module.finrank_matrix]
      simp
      omega
    obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff _).1 hker
    have hex : ∃ v ∈ LinearMap.ker f, vᴴ * J * v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hp := polar htr J hJ _ hcon
      apply hy0
      have hyX : Xᴴ * J * y = 0 := by rw [← hf]; exact hyW
      have hyJ : ∀ z : Matrix ν Unit K, yᴴ * J * z = 0 := by
        intro z
        have hz' : z - X * (Xᴴ * J * z) ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, hf, Matrix.mul_sub, ← Matrix.mul_assoc (Xᴴ * J) X, hX, Matrix.one_mul,
            sub_self]
        have h1 := hp y hyW _ hz'
        have h2 : yᴴ * J * X = 0 := by
          have h3 : (Xᴴ * J * y)ᴴ = 0 := by rw [hyX]; simp
          rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
            ← Matrix.mul_assoc] at h3
        rw [Matrix.mul_sub, ← Matrix.mul_assoc (yᴴ * J) X, h2, Matrix.zero_mul, sub_zero] at h1
        exact h1
      have hyJ0 : yᴴ * J = 0 := by
        ext a i
        have h4 := congrFun (congrFun (hyJ (Matrix.single i () 1)) a) ()
        simpa using h4
      have hJy : J * y = 0 := by
        have h5 := congrArg conjTranspose hyJ0
        rwa [conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_zero] at h5
      calc y = J⁻¹ * (J * y) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
        _ = 0 := by rw [hJy, Matrix.mul_zero]
    obtain ⟨v, hvW, hv0⟩ := hex
    have hvX : Xᴴ * J * v = 0 := by rw [← hf]; exact hvW
    have ht0 : (vᴴ * J * v) () () ≠ 0 := by
      intro h
      apply hv0
      ext i j
      exact h
    have hherm : (vᴴ * J * v)ᴴ = vᴴ * J * v := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
    have hst : star ((vᴴ * J * v) () ()) = (vᴴ * J * v) () () := by
      have h6 := congrFun (congrFun hherm ()) ()
      rwa [conjTranspose_apply] at h6
    obtain ⟨l, hl⟩ := hnorm ((vᴴ * J * v) () ())⁻¹ (inv_ne_zero ht0) (by rw [star_inv₀, hst])
    have hw1 : (l • v)ᴴ * J * (l • v) = 1 := by
      ext i j
      simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm l, hl, inv_mul_cancel₀ ht0]
      simp
    have hw2 : Xᴴ * J * (l • v) = 0 := by rw [Matrix.mul_smul, hvX, smul_zero]
    have hw3 : (l • v)ᴴ * J * X = 0 := by
      have h3 : (Xᴴ * J * (l • v))ᴴ = 0 := by rw [hw2]; simp
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
        ← Matrix.mul_assoc] at h3
    let e : Fin m ⊕ Unit ≃ Fin (m + 1) := Fintype.equivOfCardEq (by simp)
    refine ⟨(Matrix.fromCols X (l • v)).submatrix id e.symm, ?_⟩
    rw [gram_submatrix, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      fromRows_mul_fromCols, hX, hw1, hw2, hw3, fromBlocks_one, submatrix_one_equiv]
end Formalism.FourierDecayAlt.P.S3x5
