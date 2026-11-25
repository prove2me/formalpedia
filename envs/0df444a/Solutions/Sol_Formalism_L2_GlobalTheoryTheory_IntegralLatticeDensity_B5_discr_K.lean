-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:46.184377+00:00
-- url     : https://prove2.me/submissions/5d8a39ec-8d68-488f-ad3f-5db37be02532

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_covA_discr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Polynomial Matrix Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    NumberField.discr K = -(d : ℤ) := covA_discr K d hd4 x hx hK
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
