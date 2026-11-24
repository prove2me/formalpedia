-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.cd_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:58.456288+00:00
-- url     : https://prove2.me/submissions/bbce3830-3e0d-4a96-9969-162e1b894833

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (q : MvPolynomial (Vr (2 * r + k + 1)) ℂ) : ContDiff ℝ ∞ (fun g : Mat k r => eval (vars g) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mat k r => a)
  next p q hp hq =>
    simpa using hp.add hq
  next p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases n with ⟨i, j⟩ | ⟨i, j⟩
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl]
      fun_prop
    · simp only [PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr]
      have h : ContDiff ℝ ∞ fun g : Mat k r => g i j := by fun_prop
      exact Complex.conjCLE.contDiff.comp h
end Formalism.FourierDecayAlt.P.MinorPolynomials
