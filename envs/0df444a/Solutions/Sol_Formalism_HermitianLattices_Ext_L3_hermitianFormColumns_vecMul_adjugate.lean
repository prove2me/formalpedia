-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.vecMul_adjugate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:57.617958+00:00
-- url     : https://prove2.me/submissions/008328ef-8ffa-49c0-aa54-2f22eb5cae95

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {A : Type*} [CommRing A] [StarRing A]
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution (H : Matrix m m A) (x : m → A) :
    (x ᵥ* H) ᵥ* H.adjugate = H.det • x := by
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
