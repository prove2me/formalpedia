-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_tr_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:26.032978+00:00
-- url     : https://prove2.me/submissions/ed0109bf-e05d-43cf-b178-42ba7ee18ae6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h z (x + y)) = Algebra.trace ℚ K (h z x) + Algebra.trace ℚ K (h z y) := by
  simp only [map_add]
end Formalism.HermitianLatticesTheory
