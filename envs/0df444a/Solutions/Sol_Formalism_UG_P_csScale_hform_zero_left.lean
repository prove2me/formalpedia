-- Prove2me | solution 1 for Formalism.UG.P.csScale_hform_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:11.449206+00:00
-- url     : https://prove2.me/submissions/5cb849d6-746d-4205-90f3-37ad466ec9cc

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n]
namespace Formalism.UG.P
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (y : n → A) :
    hform σ J 0 y = 0 := by
  simp [hform]
end Formalism.UG.P
