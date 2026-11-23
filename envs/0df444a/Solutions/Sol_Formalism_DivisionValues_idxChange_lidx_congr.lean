-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_lidx_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:13.94956+00:00
-- url     : https://prove2.me/submissions/af99d5b7-1346-4933-b664-5eb800474e6d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_locLen_congr
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


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
theorem _root_.solution (p : Ideal R) [p.IsPrime] {A A' B B' : Submodule R (Fin d → K)}
    (hA : localization₂ p A = localization₂ p A') (hB : localization₂ p B = localization₂ p B') : lidx p A B = lidx p A' B' := by
  have hinf : localization₂ p (A ⊓ B) = localization₂ p (A' ⊓ B') := by
    unfold localization₂ at hA hB ⊢
    rw [locBasic_locS_inf, locBasic_locS_inf, hA, hB]
  unfold lidx
  rw [idxChange_locLen_congr p hA hinf, idxChange_locLen_congr p hB hinf]
end Formalism.DivisionValues
