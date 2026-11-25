-- Prove2me | solution 1 for Formalism.UG.P.afsplitC_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:21.3482+00:00
-- url     : https://prove2.me/submissions/3924f851-fccc-418f-a538-7997e54d27ba

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC

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
theorem _root_.solution (M M' : Matrix n n Rv) (N : Matrix n n R) :
    afsplitC v M (afsplitC v M' N) = afsplitC v M N := by
  unfold afsplitC
  rw [smul_add, afsplit_smul_map, zero_add, smul_smul, afsplit_om_idem]
end Formalism.UG.P
