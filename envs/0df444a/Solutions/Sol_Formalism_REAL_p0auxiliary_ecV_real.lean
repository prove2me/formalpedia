-- Prove2me | solution 1 for Formalism.REAL.p0auxiliary_ecV_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:16.041315+00:00
-- url     : https://prove2.me/submissions/8d624c43-7fe1-4ef3-a643-d00acd1748a1

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LieOperatorConjHolds
import Theorems.Thm_Formalism_REAL_p0auxiliary_cpart1_real
import Theorems.Thm_Formalism_REAL_p0auxiliary_cpart2_real
import Theorems.Thm_Formalism_REAL_p0auxiliary_cpart1_I
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma Jm_mul_selfRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private lemma conjTranspose_Jm {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp
private lemma inG_cpart1_real_place_taylor {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart1 ε Z) := by
  have hAH : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      conjTranspose_Jm, Matrix.mul_assoc]
  have h1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z := by
    rw [Matrix.mul_assoc, Jm_mul_selfRealPlaceTaylor, Matrix.mul_one]
  have h2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_selfRealPlaceTaylor, Matrix.one_mul]
  rw [inG, cpart1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hAH, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
  simp <;> module
private lemma inG_cpart2_real_place_taylor {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (cpart2 ε Z) := by
  have h := inG_cpart1_real_place_taylor ε (Complex.I • Z)
  rw [p0auxiliary_cpart1_I] at h
  rw [inG] at h ⊢
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add] at h
  exact neg_eq_zero.mp h
section EcV
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl
end EcV
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable (hl : RdLinV) {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
include hl
namespace Formalism.REAL
theorem _root_.solution (hf : SmoothOnGV ε f) (hg : inUJ ε g) (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε ((x : ℂ) • Z) f g = (x : ℂ) • EcV ε Z f g := by
  have H := hl
  unfold RdLinV at H
  simp only [EcV]
  rw [p0auxiliary_cpart1_real, p0auxiliary_cpart2_real,
    (H n ε E f f _ _ x 0 g hf hf (inG_cpart1_real_place_taylor ε Z) (inG_cpart1_real_place_taylor ε Z) hg).2.1,
    (H n ε E f f _ _ x 0 g hf hf (inG_cpart2_real_place_taylor ε Z) (inG_cpart2_real_place_taylor ε Z) hg).2.1, smul_add,
    smul_comm Complex.I (x : ℂ)]
end Formalism.REAL
