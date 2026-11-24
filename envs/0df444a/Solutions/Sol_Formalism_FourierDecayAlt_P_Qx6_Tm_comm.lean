-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.Tm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:55.476006+00:00
-- url     : https://prove2.me/submissions/e8d92195-38bd-40a1-a83d-e681bcac80c2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ)
    {a c d : Fin n} (h1 : a ≠ c) (h2 : d ≠ a) : Tm E u a a * E c d = E c d * Tm E u a a := by
  have h := hE a a c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
  simp only [Tm, eq_self_iff_true, if_true]
  rw [add_mul, mul_add, h, Algebra.commutes]
end Formalism.FourierDecayAlt.P.Qx6
