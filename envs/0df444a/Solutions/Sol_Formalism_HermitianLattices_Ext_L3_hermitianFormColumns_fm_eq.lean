-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.fm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:21.977271+00:00
-- url     : https://prove2.me/submissions/adde415b-a4fa-4091-9c35-a3addceb83ad

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
theorem _root_.solution (H : Matrix m m A) (x y : m → A) : fm H x y = (star x ᵥ* H) ⬝ᵥ y := Matrix.dotProduct_mulVec (star x) H y
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
