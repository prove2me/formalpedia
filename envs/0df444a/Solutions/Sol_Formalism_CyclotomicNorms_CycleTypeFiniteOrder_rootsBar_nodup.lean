-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.rootsBar_nodup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:38.107087+00:00
-- url     : https://prove2.me/submissions/64ba294a-382e-4b35-be12-77128f20487d

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction

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
variable {N : ℕ} {f : (ZMod g)[X]}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hf : GoodPoly N f) : (rootsBar f).Nodup :=
  nodup_roots ((PerfectField.separable_iff_squarefree.mpr hf.sqf).map)
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
