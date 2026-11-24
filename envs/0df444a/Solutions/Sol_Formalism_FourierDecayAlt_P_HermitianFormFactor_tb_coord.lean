-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.tb_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:41:01.768587+00:00
-- url     : https://prove2.me/submissions/032cc1d2-5959-4b85-b005-4aed495f2ec2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Tm_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (F : Frame H Ep Em) (Y : Q → m → ℂ) : tb H Ep Y = swapBlockPair (coordE F Y) := by
  refine Prod.ext ?_ rfl
  show Tm H (cm Y) = gram (fun j => Emᴴ *ᵥ Y j) - (cm (fun j => Epᴴ *ᵥ Y j))ᴴ * cm (fun j => Epᴴ *ᵥ Y j)
  unfold gram
  rw [cm_mulVec, cm_mulVec, Tm_coord F]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
