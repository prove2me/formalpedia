-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.86465+00:00
-- url     : https://prove2.me/submissions/30a299fc-3a83-4f71-b3c5-e14d8a2ecc2a

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_finLen
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (p : Ideal (𝓞 K)) [p.IsPrime] (X Y : Submodule (𝓞 K) Z) (hX : X.FG)
    (hY : Submodule.span K (Y : Set Z) = ⊤) : qlen (localization₂ p X) (localization₂ p Y) ≠ ⊤ := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) X Y hX
    (by rw [indexBasic_locS_top (K := K) Y hY]; exact le_top)
  exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
