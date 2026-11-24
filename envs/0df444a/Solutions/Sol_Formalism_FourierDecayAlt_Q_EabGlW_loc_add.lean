-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.loc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:19:15.924829+00:00
-- url     : https://prove2.me/submissions/5cf75c31-b601-469b-bb44-7eaeefe1f35a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_ext

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
theorem _root_.solution {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : Flow G X) (hY : Flow G Y) (hXY : Flow G (X + Y))
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) :
    RdV (X + Y) f g = RdV X f g + RdV Y f g := by
  rw [loc_ext hXY hL hg hgG, loc_ext hX hL hg hgG, loc_ext hY hL hg hgG, Matrix.mul_add, map_add]
end Formalism.FourierDecayAlt.Q.EabGlW
