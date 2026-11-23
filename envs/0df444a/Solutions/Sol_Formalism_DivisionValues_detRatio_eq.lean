-- Prove2me | solution 1 for Formalism.DivisionValues.detRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:27.748797+00:00
-- url     : https://prove2.me/submissions/accd0dc5-3033-48ca-abbc-26da6bf8d62a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Theorems.Thm_Formalism_DivisionValues_star_mulVec_dot
import Theorems.Thm_Formalism_DivisionValues_majAt_eq
import Theorems.Thm_Formalism_DivisionValues_cv_mulVec
import Theorems.Thm_Formalism_DivisionValues_cv_single
import Theorems.Thm_Formalism_DivisionValues_single_dot_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution {d : ℕ} (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (φ : Matrix (Fin d) (Fin d) K) (v : InfinitePlace K) :
    detRatio XS XT φ v =
      ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding).det.re / (metMat XS v).det.re := by
  have h1 : gram XT v (fun i => φ.mulVec (Pi.single i 1)) =
      (φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_mulVec, cv_mulVec, cv_single, cv_single, star_mulVec_dot, single_dot_single]
  have h2 : gram XS v (fun i => (Pi.single i 1 : Fin d → K)) = metMat XS v := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_single, cv_single, single_dot_single]
  rw [detRatio, h1, h2]
end Formalism.DivisionValues
