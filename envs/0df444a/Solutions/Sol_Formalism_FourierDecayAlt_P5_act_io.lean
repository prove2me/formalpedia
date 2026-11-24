-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.act_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:17:38.106433+00:00
-- url     : https://prove2.me/submissions/3bcb5467-2a85-48d8-9738-b73f7cfbc94e

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_fst_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (f : Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (io f) x a = f.1 (x a) := by
  simp only [act, io, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), pr_fst_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ a) h
end Formalism.FourierDecayAlt.P5
