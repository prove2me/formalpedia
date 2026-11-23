-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.eval_pow_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:21.067285+00:00
-- url     : https://prove2.me/submissions/39cf5c7f-e8f4-4f73-b1d7-62875b72b500

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_frob_comp_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (p : (ZMod g)[X]) (x : Fbar g) :
    (p.map (algebraMap (ZMod g) (Fbar g))).eval (x ^ g) =
      ((p.map (algebraMap (ZMod g) (Fbar g))).eval x) ^ g := by
  rw [eval_map, eval_map, ← frobenius_def, ← frobenius_def, hom_eval₂, frob_comp_alg]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
