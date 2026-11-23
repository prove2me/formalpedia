-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.plc_conjPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:25.549856+00:00
-- url     : https://prove2.me/submissions/3f77c864-59d2-4177-92ee-861cb5f48046

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : plc (conjPl w) = plc w := by
  unfold plc
  let e := Ideal.quotientEquiv w.asIdeal (conjPl w).asIdeal (cO K) rfl
  haveI := ringChar.charP (𝓞 K ⧸ w.asIdeal)
  haveI : CharP (𝓞 K ⧸ (conjPl w).asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) :=
    charP_of_injective_ringHom (f := (e : 𝓞 K ⧸ w.asIdeal →+* 𝓞 K ⧸ (conjPl w).asIdeal))
      e.injective _
  exact ringChar.eq _ _
end Formalism.EigenvalueLevelCeiling
