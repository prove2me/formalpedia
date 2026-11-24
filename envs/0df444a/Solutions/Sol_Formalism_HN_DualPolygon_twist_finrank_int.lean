-- Prove2me | solution 1 for Formalism.HN.DualPolygon.twist_finrank_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:19.190944+00:00
-- url     : https://prove2.me/submissions/c23bfa7a-8086-4a98-a3b9-71561560d239

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
open scoped Pointwise
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
namespace Formalism.HN.DualPolygon
theorem _root_.solution [StarRing K] (X : Submodule (𝓞 K) W) (hX : X.FG) :
    finrank ℤ X = finrank ℚ K * finrank K (Submodule.span K (X : Set W)) := by
  let b := Module.finBasis K W
  let Xf : InfinitePlace K → Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := fun _ => 1
  have hXf : ∀ v, IsUnit (Xf v).det := fun v => by simp [Xf]
  obtain ⟨-, hrk, -⟩ := place_lattice_structure K W (Fin (finrank K W)) b Xf hXf X hX
  have hinj := Formalism.HN.PlaceLattice.realize_injective b Xf hXf
  let e : X.toAddSubgroup ≃+ (X.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b Xf)) :=
    AddSubgroup.equivMapOfInjective _ _ hinj
  have h1 : finrank ℤ X = finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b Xf) X) :=
    e.toIntLinearEquiv.finrank_eq
  rw [h1]
  exact hrk
end Formalism.HN.DualPolygon
