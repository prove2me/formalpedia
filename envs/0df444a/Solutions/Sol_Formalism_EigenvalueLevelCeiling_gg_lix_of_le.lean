-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.gg_lix_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:04.810327+00:00
-- url     : https://prove2.me/submissions/8808c3b1-a5c4-4bed-ab25-f5791a3a5bd7

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locLen_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) (h : B ≤ A) :
    lix w A B = (Formalism.HermitianLatticesTheory.locLen w.asIdeal A B : ℤ) := by
  unfold lix Formalism.HermitianLatticesTheory.lidx
  rw [inf_eq_right.mpr h, Formalism.HermitianLatticesTheory.indexBasic_locLen_self]
  simp
end Formalism.EigenvalueLevelCeiling
