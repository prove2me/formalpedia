-- Prove2me | solution 1 for Formalism.UG.P.afsplit_prV_IE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:19.482314+00:00
-- url     : https://prove2.me/submissions/f7711c9a-4895-44ea-9b63-cd1b0bc2e0e7

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Theorems.Thm_Formalism_UG_P_afsplitIE_tmul
import Theorems.Thm_Formalism_UG_P_afsplit_prV_tmul
import Theorems.Thm_Formalism_UG_P_afsplitI_self


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
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    prV (E := E) v (afsplitIE v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end Formalism.UG.P
