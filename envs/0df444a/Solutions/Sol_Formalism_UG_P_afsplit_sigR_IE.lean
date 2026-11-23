-- Prove2me | solution 1 for Formalism.UG.P.afsplit_sigR_IE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:19.266341+00:00
-- url     : https://prove2.me/submissions/06f362de-60d5-4481-81a1-703fa526377c

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Theorems.Thm_Formalism_UG_P_afsplitIE_tmul

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
theorem _root_.solution (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    sigR σ 𝔸 (afsplitIE v x) = afsplitIE v (sigR σ (v.adicCompletion F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [sigR, afsplitIE_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end Formalism.UG.P
