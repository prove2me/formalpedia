-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.weyl_int_module_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:46.874334+00:00
-- url     : https://prove2.me/submissions/5a75ce02-5e29-4ec5-87c9-24b6a4d57db1

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_dualWeyl_fg
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    Module.Free ℤ (weyl ℤ r n hn ν) := by
  have h1 : Module.Finite ℤ (dualWeyl ℤ r n ν) := Module.Finite.iff_fg.2 (la_dualWeyl_fg r n ν)
  have h2 : Module.Finite ℤ (weyl ℤ r n hn ν) :=
    Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ r n hn ν hν))
      (Submodule.inclusion_injective _)
  infer_instance
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
