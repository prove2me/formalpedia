-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.loc_rd_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:28.418435+00:00
-- url     : https://prove2.me/submissions/cfbf1a03-6c07-4297-8941-fc6bbdbc0596

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Flow G X)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U) :
    LocExt G (RdV X f) (fun k => fderiv ℝ F k (k * X)) U :=
  ⟨hL.1, loc_smooth hL.1 hL.2.1 X, fun _ hh hhG => loc_ext hX hL hh hhG⟩
end Formalism.FourierDecayAlt.Q.EabGlW
