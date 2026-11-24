-- Prove2me | solution 1 for Formalism.UG.P.afsplitC_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:38:10.106579+00:00
-- url     : https://prove2.me/submissions/397e0052-2429-4d37-829a-f3273ff9999d

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Theorems.Thm_Formalism_UG_P_afsplit_sigR_IE
import Theorems.Thm_Formalism_UG_P_afsplit_sigR_eps


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
theorem _root_.solution (σ : E →ₐ[F] E) (M : Matrix n n Rv) (N : Matrix n n R) :
    cT (sigR σ 𝔸) (afsplitC v M N) =
      afsplitC v (cT (sigR σ (v.adicCompletion F)) M) (cT (sigR σ 𝔸) N) := by
  unfold cT afsplitC
  ext i j
  simp [Matrix.transpose_apply, Matrix.map_apply, afsplit_sigR_IE, afsplit_sigR_eps]
end Formalism.UG.P
