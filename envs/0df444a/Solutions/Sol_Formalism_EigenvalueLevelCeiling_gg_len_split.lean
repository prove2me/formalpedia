-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.gg_len_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:04.601802+00:00
-- url     : https://prove2.me/submissions/2dfec340-96a0-47b1-817e-b6d3c0d9ca73

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG

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
variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (f : Y →ₗ[R] Y) :
    Module.length R Y =
      Module.length R (LinearMap.range f) + Module.length R (Y ⧸ LinearMap.range f) :=
  Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
end Formalism.EigenvalueLevelCeiling
