-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.isOpen_big_cell_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:32:15.235736+00:00
-- url     : https://prove2.me/submissions/e231e68e-31f3-4f0d-aa2f-496a3832a029

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dmin_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Gf_cont


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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : IsOpen (V0 D L) := by
  unfold V0
  refine (isOpen_lt continuous_const (Gf_cont D.z D.z')).inter ?_
  refine isOpen_biInter_finset (fun l _ => ?_)
  exact isOpen_ne_fun (Dmin_cont D.z D.z' l) continuous_const
end Formalism.FourierDecayAlt.P.MinorPolynomials
