-- Prove2me | solution 1 for Formalism.UG.P.afsplitC_prV_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:09.977631+00:00
-- url     : https://prove2.me/submissions/bcd8f434-aec2-4896-9e9f-f8f696ffe6b5

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Theorems.Thm_Formalism_UG_P_afsplit_prV_IE_ne
import Theorems.Thm_Formalism_UG_P_afsplit_prV_eps_ne


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
  {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "R" => E ⊗[F] 𝔸
namespace Formalism.UG.P
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (M : Matrix n n Rv)
    (N : Matrix n n R) : (afsplitC v M N).map (prV (E := E) w) = N.map (prV (E := E) w) := by
  unfold afsplitC
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
    map_one, afsplit_prV_IE_ne v w h, afsplit_prV_eps_ne v w h, sub_zero, one_mul, zero_add]
end Formalism.UG.P
