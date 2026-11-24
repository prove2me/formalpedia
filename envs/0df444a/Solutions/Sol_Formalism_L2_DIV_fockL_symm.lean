-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:14.898872+00:00
-- url     : https://prove2.me/submissions/cba8c320-74cb-4516-848d-3e2719c60abe

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_fockSHerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution {σ : Type} (f g : MvPolynomial σ K) : fockL f g = star (fockL g f) :=
  fockSHerm K σ g f
end Formalism.L2.DIV
