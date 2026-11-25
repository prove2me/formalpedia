-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.vw_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:01.391955+00:00
-- url     : https://prove2.me/submissions/920c5e39-39da-4a96-b396-79fcbeb8ee11

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Theorems.Thm_unipVal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain CategoryTheory
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {g1 g2 : ℕ} (h1 : g1.Prime) (h2 : g2.Prime) (h12 : g1 ≠ g2) (a : ℕ) :
    (vw w (((g1 ^ a * g2 ^ a : ℕ)) : K) : ℝ) =
      (ramw w : ℝ) * (if plc w = g1 ∨ plc w = g2 then (a : ℝ) else 0) :=
  (unipVal K w).2 g1 g2 a h1 h2 h12
end Formalism.L2.Indef.Tree
