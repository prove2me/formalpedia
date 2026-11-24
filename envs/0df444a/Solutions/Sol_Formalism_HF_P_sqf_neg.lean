-- Prove2me | solution 1 for Formalism.HF.P.sqf_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:11.305954+00:00
-- url     : https://prove2.me/submissions/af7678fd-baec-4b77-8cc8-3adabdad0603

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (p : ℕ) (hp : p.Prime) : Squarefree (-(p : ℤ)) :=
  (Nat.prime_iff_prime_int.mp hp).neg.squarefree
end Formalism.HF.P
