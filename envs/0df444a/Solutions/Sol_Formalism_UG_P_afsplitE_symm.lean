-- Prove2me | solution 1 for Formalism.UG.P.afsplitE_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:37:08.189879+00:00
-- url     : https://prove2.me/submissions/fede7b9c-9c76-4161-a428-06a6ef3358dc

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit

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
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (p : UPts σ J (v.adicCompletion F) × afsplitKer σ J v) :
    (((afsplitE σ J v).symm p : UPts σ J 𝔸) : GL n (E ⊗[F] 𝔸)) =
      afsplitU v (p.1 : GL n (E ⊗[F] v.adicCompletion F)) (p.2 : GL n (E ⊗[F] 𝔸)) := rfl
end Formalism.UG.P
