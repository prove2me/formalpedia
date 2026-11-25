-- Prove2me | solution 1 for Formalism.L2.NX.glOf_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:34.121935+00:00
-- url     : https://prove2.me/submissions/c3349fcb-6bdf-4acc-b6db-db199738d455

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L
namespace Formalism.L2.NX
theorem _root_.solution {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) (h : IsUnit M.det) :
    ((glOf M : GL ι R) : Matrix ι ι R) = M := by
  unfold glOf
  rw [dif_pos h]
  rfl
end Formalism.L2.NX
