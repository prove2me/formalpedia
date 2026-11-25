-- Prove2me | solution 1 for Formalism.UG.P.afsplitC_prV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:26.170958+00:00
-- url     : https://prove2.me/submissions/43aea1d1-d3a7-4443-b4cf-7098a3ee7d36

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Theorems.Thm_Formalism_UG_P_afsplit_prV_IE
import Theorems.Thm_Formalism_UG_P_afsplit_prV_eps


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
theorem _root_.solution (M : Matrix n n Rv) (N : Matrix n n R) :
    (afsplitC v M N).map (prV (E := E) v) = M := by
  unfold afsplitC
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [afsplit_prV_IE, map_sub, map_one, afsplit_prV_eps, sub_self, zero_mul, add_zero]
end Formalism.UG.P
