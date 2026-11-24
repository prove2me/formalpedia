-- Prove2me | solution 1 for Formalism.ExtensionFiltration.muDef_eq_covol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:20.192814+00:00
-- url     : https://prove2.me/submissions/9b9a587b-d654-49d7-956b-0dddfad95679

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
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
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    muDef b X M = 2 * (-Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M)) /
      ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ))) - Real.log 2 +
        logDisc K / (Module.finrank ℚ K : ℝ) := by
  obtain ⟨-, hrkM, -⟩ := place_lattice_structure K V ι b X hX M hM
  have h1 : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) M) = Module.finrank ℚ K * rkK M := hrkM
  unfold muDef Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [h1]
  push_cast
  rfl
end Formalism.ExtensionFiltration
