-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:48.4618+00:00
-- url     : https://prove2.me/submissions/cce97736-3160-4c0c-b912-3f94415920c6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv K := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have hd : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have h := Real.one_le_rpow hd (by positivity : (0 : ℝ) ≤ 1 / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)))
  have e : 2 * (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ))) / 2) =
      |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by ring
  rw [e]; exact h
end Formalism.MainNotions.MassRatioZetaBound
