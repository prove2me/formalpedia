-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.hsblock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:46:42.560691+00:00
-- url     : https://prove2.me/submissions/3ee8be6a-161a-41c8-924f-b7850ba62402

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_mul_H_conj
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
section Defs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Defs
section Alg
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Frame
end Frame
private theorem trace_mul_conjTranspose_of_signature_preserving {n : Type} [Fintype n] [DecidableEq n] (A D g : Matrix n n ℂ)
    (hAA : A * A = A) (hDD : D * D = D) (hAD : A * D = 0) (hDA : D * A = 0) (hsum : A + D = 1)
    (h1 : g * (A - D) * gᴴ = A - D) (h2 : gᴴ * (A - D) * g = A - D) :
    Matrix.trace (g * gᴴ) = Matrix.trace A + Matrix.trace D + 4 * Matrix.trace (A * (g * D * gᴴ)) := by
  have I1 : g * A * gᴴ - g * D * gᴴ = A - D := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact h1
  have I2 : gᴴ * A * g - gᴴ * D * g = A - D := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact h2
  have e0 : Matrix.trace (g * gᴴ) = Matrix.trace (g * A * gᴴ) + Matrix.trace (g * D * gᴴ) := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.mul_add, hsum, Matrix.mul_one]
  have e1 : Matrix.trace (g * A * gᴴ) - Matrix.trace (g * D * gᴴ) = Matrix.trace A - Matrix.trace D := by
    rw [← Matrix.trace_sub, ← Matrix.trace_sub, I1]
  have e2 : Matrix.trace (g * D * gᴴ) =
      Matrix.trace (A * (g * D * gᴴ)) + Matrix.trace (D * (g * D * gᴴ)) := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, hsum, Matrix.one_mul]
  have e3 : Matrix.trace (D * (g * A * gᴴ)) - Matrix.trace (D * (g * D * gᴴ)) = - Matrix.trace D := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, I1, Matrix.mul_sub, hDA, hDD, zero_sub, Matrix.trace_neg]
  have e4 : Matrix.trace (A * (g * A * gᴴ)) - Matrix.trace (A * (g * D * gᴴ)) = Matrix.trace A := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, I1, Matrix.mul_sub, hAA, hAD, sub_zero]
  have e5 : Matrix.trace (A * (gᴴ * A * g)) - Matrix.trace (A * (gᴴ * D * g)) = Matrix.trace A := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, I2, Matrix.mul_sub, hAA, hAD, sub_zero]
  have e6 : Matrix.trace (A * (gᴴ * A * g)) = Matrix.trace (A * (g * A * gᴴ)) := by
    rw [Matrix.trace_mul_comm A (gᴴ * A * g), show gᴴ * A * g * A = gᴴ * (A * g * A) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm gᴴ, show A * g * A * gᴴ = A * (g * A * gᴴ) by
      simp only [Matrix.mul_assoc]]
  have e7 : Matrix.trace (A * (gᴴ * D * g)) = Matrix.trace (D * (g * A * gᴴ)) := by
    rw [Matrix.trace_mul_comm A (gᴴ * D * g), show gᴴ * D * g * A = gᴴ * (D * g * A) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm gᴴ, show D * g * A * gᴴ = D * (g * A * gᴴ) by
      simp only [Matrix.mul_assoc]]
  linear_combination e0 + e1 + 2 * e2 - 2 * e3 + 2 * e4 - 2 * e5 + 2 * e6 - 2 * e7
namespace Frame
end Frame
end Alg
section Shear
section gramsec
variable {Q : Type} [Fintype Q] [DecidableEq Q]
end gramsec
section rankone
variable {Q : Type} [Fintype Q] [DecidableEq Q]
end rankone
section rankone2
variable {Q : Type} [Fintype Q] [DecidableEq Q]
end rankone2
section shearsec
variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]
end shearsec
end Shear
section Core
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
end Core
end Formalism.FourierDecayAlt.P.HermitianFormFactor
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : Formalism.FourierDecayAlt.B2.HSBlock := by
  intro k r g hg
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hH2 : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hAA : Ppos k r * Ppos k r = Ppos k r := by
    unfold Ppos
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hDD : Pneg k r * Pneg k r = Pneg k r := by
    unfold Pneg
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hAD : Ppos k r * Pneg k r = 0 := by
    unfold Ppos Pneg
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hDA : Pneg k r * Ppos k r = 0 := by
    unfold Ppos Pneg
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, hH2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.zero_apply, smul_eq_mul]
    ring
  have hsum : Ppos k r + Pneg k r = 1 := by
    unfold Ppos Pneg
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hdiff : Ppos k r - Pneg k r = Hpk k r := by
    unfold Ppos Pneg
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hAh : (Ppos k r)ᴴ = Ppos k r := by
    unfold Ppos
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hH]
    congr 1
    simp
  have hDh : (Pneg k r)ᴴ = Pneg k r := by
    unfold Pneg
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
    congr 1
    simp
  have h1 : g * (Ppos k r - Pneg k r) * gᴴ = Ppos k r - Pneg k r := by
    rw [hdiff]; exact mul_H_conj hH2 hg
  have h2 : gᴴ * (Ppos k r - Pneg k r) * g = Ppos k r - Pneg k r := by
    rw [hdiff]; exact hg
  have key := trace_mul_conjTranspose_of_signature_preserving (Ppos k r) (Pneg k r) g hAA hDD hAD hDA hsum h1 h2
  have htr : Matrix.trace (Ppos k r) + Matrix.trace (Pneg k r) = ((2 * r + k + 1 : ℕ) : ℂ) := by
    rw [← Matrix.trace_add, hsum, Matrix.trace_one, Fintype.card_fin]
  set A := Ppos k r with hA
  set D := Pneg k r with hD
  have hb : Matrix.trace (A * g * D * (A * g * D)ᴴ) = Matrix.trace (A * (g * D * gᴴ)) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAh, hDh]
    rw [show A * g * D * (D * (gᴴ * A)) = A * (g * (D * D) * gᴴ * A) by simp only [Matrix.mul_assoc], hDD]
    rw [Matrix.trace_mul_comm, show g * D * gᴴ * A * A = g * D * gᴴ * (A * A) by simp only [Matrix.mul_assoc],
      hAA, Matrix.trace_mul_comm]
  have key2 : Matrix.trace (g * gᴴ) =
      ((2 * r + k + 1 : ℕ) : ℂ) + 4 * Matrix.trace (A * g * D * (A * g * D)ᴴ) := by
    rw [key, hb, htr]
  rw [gN_sq, gN_sq]
  have h3 := congrArg Complex.re key2
  simpa using h3
end Formalism.FourierDecayAlt.P.HermitianFormFactor
