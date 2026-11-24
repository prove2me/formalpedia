-- Prove2me | solution 1 for Formalism.UG.P.afsplit_coord_prV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:12.24475+00:00
-- url     : https://prove2.me/submissions/63660c0a-f736-48f8-af81-1bd491fba058

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Theorems.Thm_Formalism_UG_P_afsplit_prV_tmul

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
theorem _root_.solution (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (i : Module.Free.ChooseBasisIndex F E) (w : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] 𝔸) :
    TensorProduct.lid F (w.adicCompletion F) ((b.coord i).rTensor _ (prV (E := E) w y)) =
      (TensorProduct.lid F 𝔸 ((b.coord i).rTensor _ y)) w := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    rw [afsplit_prV_tmul]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, afsplit_smul_apply]
  | add x y hx hy => simp only [map_add, hx, hy, afsplit_add_apply]
end Formalism.UG.P
