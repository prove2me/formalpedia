-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_locLen_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:22.313594+00:00
-- url     : https://prove2.me/submissions/2f7b8295-aea8-4bb3-a23c-ddf2019910cb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (p : Ideal R) [p.IsPrime] {X X' Y Y' : Submodule R (Fin d → K)}
    (hX : localization₂ p X = localization₂ p X') (hY : localization₂ p Y = localization₂ p Y') : locLen p X Y = locLen p X' Y' := by
  unfold locLen
  rw [hX, hY]
end Formalism.DivisionValues
