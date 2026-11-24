-- Prove2me | solution 1 for Formalism.REAL.vector_complexified_derivative_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:12.86436+00:00
-- url     : https://prove2.me/submissions/e6c23789-047e-4190-b804-a1bb8767b07e

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_vector_right_derivative_sub
import Theorems.Thm_Formalism_REAL_Jm_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section EabGl
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma Jm_mul_JmRealPlaceTaylor {m : ℕ} (e : Fin m → Bool) : Jm e * Jm e = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private lemma Jm_mul_Jm_mulRealPlaceTaylor {m : ℕ} (e : Fin m → Bool) (Y : Matrix (Fin m) (Fin m) ℂ) :
    Jm e * (Jm e * Y) = Y := by
  rw [← Matrix.mul_assoc, Jm_mul_JmRealPlaceTaylor, Matrix.one_mul]
private lemma cpart1_inG {m : ℕ} (e : Fin m → Bool) (Z : Matrix (Fin m) (Fin m) ℂ) :
    inG e (cpart1 e Z) := by
  have hc : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [star_div₀, star_one, star_ofNat]
  unfold inG cpart1
  rw [Matrix.conjTranspose_smul, hc, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Jm_mul_JmRealPlaceTaylor, Jm_mul_Jm_mulRealPlaceTaylor, Matrix.mul_one, smul_sub]
  abel
private lemma cpart2_inG {m : ℕ} (e : Fin m → Bool) (Z : Matrix (Fin m) (Fin m) ℂ) :
    inG e (cpart2 e Z) := by
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', star_ofNat, Complex.star_def, Complex.conj_I]
    ring
  unfold inG cpart2
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Jm_mul_JmRealPlaceTaylor, Jm_mul_Jm_mulRealPlaceTaylor, Matrix.mul_one, smul_add]
  rw [hc]
  simp only [neg_smul]
  abel
end EabGl
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.REAL
theorem _root_.solution (hl : RdLinV) {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnGV ε f) (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε (Z - W) f g = EcV ε Z f g - EcV ε W f g := by
  have h1 : cpart1 ε (Z - W) = cpart1 ε Z - cpart1 ε W := by
    simp only [cpart1, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_sub]
    abel
  have h2 : cpart2 ε (Z - W) = cpart2 ε Z - cpart2 ε W := by
    simp only [cpart2, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub]
    abel
  simp only [EcV]
  rw [h1, h2, vector_right_derivative_sub hl hf (cpart1_inG ε Z) (cpart1_inG ε W) hg,
    vector_right_derivative_sub hl hf (cpart2_inG ε Z) (cpart2_inG ε W) hg, smul_sub]
  abel
end Formalism.REAL
