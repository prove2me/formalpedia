-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_big_cell_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:58:56.848729+00:00
-- url     : https://prove2.me/submissions/b7fbb390-42b9-422e-b399-91663f90c972

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_aDil_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace B2
end B2
private lemma star_ofReal_eq (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.DilBigCell := by
  unfold Formalism.FourierDecayAlt.B.DilBigCell
  intro k r c μ t₁ t₂ h1 h2
  rw [B2.aDil_inv k r t₁ h1]
  unfold aDil
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold bigCell esI
  beta_reduce
  split_ifs
  all_goals try first
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | rfl
    | (rw [one_mul, mul_one])
    | exact (congrArg (· * (1 : ℂ)) (one_mul _)).trans (mul_one _)
    | (simp; done)
    | (have e : (i : ℕ) - (r + k) = r - (j : ℕ) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       rw [e]
       try simp only [Fin.val_mk]
       push_cast
       simp only [inv_pow, inv_inv]
       ring)
    | (have e1 : r - (i : ℕ) = (j : ℕ) - (r + k) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       have e2 : r - (2 * r + k - (j : ℕ)) = (j : ℕ) - (r + k) := by omega
       simp only [Fin.val_mk, e1, e2, star_mul', star_ofReal_eq]
       push_cast
       ring)
end Formalism.FourierDecayAlt.P
