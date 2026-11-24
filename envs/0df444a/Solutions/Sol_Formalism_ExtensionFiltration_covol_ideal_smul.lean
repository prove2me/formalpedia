-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covol_ideal_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:20.775973+00:00
-- url     : https://prove2.me/submissions/53e2a96a-5e74-4978-be3c-5848ce4a3631

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Theorems.Thm_Formalism_ExtensionFiltration_covol_of_le
import Theorems.Thm_Formalism_HN_DualPolygon_twist_index
import Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul


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
    (hX : ∀ v, IsUnit (X v).det) (M : Submodule (𝓞 K) V) (hM : M.FG) (𝔟 : Ideal (𝓞 K))
    (h𝔟 : 𝔟 ≠ ⊥) :
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) (𝔟 • M)) =
      (Ideal.absNorm 𝔟 : ℝ) ^ rkK M * Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hfg : (𝔟 • M).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hM
  have hrk : rkK (𝔟 • M) = rkK M := by
    unfold rkK
    rw [Formalism.HN.DualPolygon.twist_span_smul M 𝔟 h𝔟]
  rw [covol_of_le b X hX (𝔟 • M) M hfg hM Submodule.smul_le_right hrk,
    Formalism.HN.DualPolygon.twist_index M hM 𝔟 h𝔟, Nat.cast_pow]
  rfl
end Formalism.ExtensionFiltration
