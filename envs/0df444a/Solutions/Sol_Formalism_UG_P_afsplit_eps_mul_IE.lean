-- Prove2me | solution 1 for Formalism.UG.P.afsplit_eps_mul_IE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:19.162455+00:00
-- url     : https://prove2.me/submissions/23f98b72-1a4a-4e76-890b-2be0ddc96679

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Theorems.Thm_Formalism_UG_P_afsplitIE_tmul
import Theorems.Thm_Formalism_UG_P_afsplitI_mul


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
    afsplitEps E v * afsplitIE v x = afsplitIE v x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [he, afsplitIE_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← afsplitI_mul, one_mul]
  | add x y hx hy => rw [map_add, mul_add, hx, hy]
end Formalism.UG.P
