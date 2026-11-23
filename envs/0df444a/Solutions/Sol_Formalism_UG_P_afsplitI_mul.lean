-- Prove2me | solution 1 for Formalism.UG.P.afsplitI_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:47.845127+00:00
-- url     : https://prove2.me/submissions/34ffee6e-08b2-4b10-b1f0-c889efc6f155

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_afsplitI_ne

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
variable {F : Type} [Field F] [NumberField F]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    afsplitI v (x * y) = afsplitI v x * afsplitI v y := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, mul_zero]
end Formalism.UG.P
