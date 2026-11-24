-- Prove2me | solution 1 for Formalism.REAL.vector_complexified_derivative_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:12.097876+00:00
-- url     : https://prove2.me/submissions/ff559fd9-3c7a-4be6-b4e3-e2d71a0d2734

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_vector_right_derivative_add
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
private lemma inG_add_real_place_taylor {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
private lemma inG_commutator' {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X * Y - Y * X) := by
  unfold inG at *
  have key : (X * Y - Y * X)ᴴ * Jm e + Jm e * (X * Y - Y * X) =
      Yᴴ * (Xᴴ * Jm e + Jm e * X) - (Yᴴ * Jm e + Jm e * Y) * X - Xᴴ * (Yᴴ * Jm e + Jm e * Y) +
        (Xᴴ * Jm e + Jm e * X) * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [key, hX, hY]
  simp
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
private lemma inG_sub_real_place_taylor {m : ℕ} {e : Fin m → Bool} {X Y : Matrix (Fin m) (Fin m) ℂ}
    (hX : inG e X) (hY : inG e Y) : inG e (X - Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, hY, sub_zero]
private lemma Jm_mul_conjTranspose_mul_Jm_of_inG {m : ℕ} {e : Fin m → Bool} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : inG e A) : Jm e * Aᴴ * Jm e = -A := by
  unfold inG at hA
  have h : Jm e * Aᴴ * Jm e + A = Jm e * (Aᴴ * Jm e + Jm e * A) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_JmRealPlaceTaylor, Matrix.one_mul]
  rw [hA, Matrix.mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h
private lemma cpart1_cpart2_add_I_smul_of_inG {m : ℕ} (e : Fin m → Bool) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : inG e A) (hB : inG e B) :
    cpart1 e (A + Complex.I • B) = A ∧ cpart2 e (A + Complex.I • B) = B := by
  have hs : Jm e * (A + Complex.I • B)ᴴ * Jm e = -A + Complex.I • B := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Jm_mul_conjTranspose_mul_Jm_of_inG hA,
      Jm_mul_conjTranspose_mul_Jm_of_inG hB, neg_smul, smul_neg, neg_neg]
  have h2I : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  constructor
  · unfold cpart1
    rw [hs, show A + Complex.I • B - (-A + Complex.I • B) = (2 : ℂ) • A by rw [two_smul]; abel,
      smul_smul]
    norm_num
  · unfold cpart2
    rw [hs, show A + Complex.I • B + (-A + Complex.I • B) = (2 * Complex.I) • B by
        rw [mul_smul, two_smul]; abel,
      smul_smul, one_div, inv_mul_cancel₀ h2I, one_smul]
private lemma cpart1_add_I_smul_cpart2 {m : ℕ} (e : Fin m → Bool) (Z : Matrix (Fin m) (Fin m) ℂ) :
    cpart1 e Z + Complex.I • cpart2 e Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show Z - Jm e * Zᴴ * Jm e + (Z + Jm e * Zᴴ * Jm e) = (2 : ℂ) • Z by rw [two_smul]; abel,
    smul_smul]
  norm_num
private lemma commutator_add_I_smul_expand {m : ℕ} (A1 A2 B1 B2 : Matrix (Fin m) (Fin m) ℂ) :
    (A1 + Complex.I • A2) * (B1 + Complex.I • B2) - (B1 + Complex.I • B2) * (A1 + Complex.I • A2) =
      ((A1 * B1 - B1 * A1) - (A2 * B2 - B2 * A2)) +
        Complex.I • ((A1 * B2 - B2 * A1) + (A2 * B1 - B1 * A2)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.I_mul_I, neg_one_smul, smul_add, smul_sub]
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
theorem _root_.solution (hl : RdLinV) (hb : RdBracketV) (hs : RdSmoothV)
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnGV ε f) (hg : inUJ ε g) :
    EcV ε Z (EcV ε W f) g - EcV ε W (EcV ε Z f) g = EcV ε (Z * W - W * Z) f g := by
  have hZ1 := cpart1_inG ε Z
  have hZ2 := cpart2_inG ε Z
  have hW1 := cpart1_inG ε W
  have hW2 := cpart2_inG ε W
  have L1 : ∀ X Y, inG ε X →
      RdV X (EcV ε Y f) g =
        RdV X (RdV (cpart1 ε Y) f) g + Complex.I • RdV X (RdV (cpart2 ε Y) f) g :=
    fun X Y hX =>
      (hl n ε E (RdV (cpart1 ε Y) f) (RdV (cpart2 ε Y) f) X X 0 Complex.I g
        (hs n ε E f _ hf (cpart1_inG ε Y)) (hs n ε E f _ hf (cpart2_inG ε Y)) hX hX hg).2.2
  have Bk : ∀ X Y, inG ε X → inG ε Y →
      RdV X (RdV Y f) g = RdV Y (RdV X f) g + RdV (X * Y - Y * X) f g := by
    intro X Y hX hY
    rw [← hb n ε E f X Y g hf hX hY hg]
    abel
  have hC := commutator_add_I_smul_expand (cpart1 ε Z) (cpart2 ε Z) (cpart1 ε W) (cpart2 ε W)
  rw [cpart1_add_I_smul_cpart2, cpart1_add_I_smul_cpart2] at hC
  have hP1 := inG_sub_real_place_taylor (inG_commutator' hZ1 hW1) (inG_commutator' hZ2 hW2)
  have hP2 := inG_add_real_place_taylor (inG_commutator' hZ1 hW2) (inG_commutator' hZ2 hW1)
  obtain ⟨hc1, hc2⟩ := cpart1_cpart2_add_I_smul_of_inG ε _ _ hP1 hP2
  simp only [EcV]
  rw [L1 _ W hZ1, L1 _ W hZ2, L1 _ Z hW1, L1 _ Z hW2,
    Bk _ _ hZ1 hW1, Bk _ _ hZ1 hW2, Bk _ _ hZ2 hW1, Bk _ _ hZ2 hW2, hC, hc1, hc2,
    vector_right_derivative_sub hl hf (inG_commutator' hZ1 hW1) (inG_commutator' hZ2 hW2) hg,
    vector_right_derivative_add hl hf (inG_commutator' hZ1 hW2) (inG_commutator' hZ2 hW1) hg]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel
end Formalism.REAL
