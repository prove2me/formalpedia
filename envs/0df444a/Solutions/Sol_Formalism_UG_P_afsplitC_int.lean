-- Prove2me | solution 1 for Formalism.UG.P.afsplitC_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:09.652738+00:00
-- url     : https://prove2.me/submissions/7860b62e-6614-416a-8ab0-d4e9f1703903

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Theorems.Thm_Formalism_UG_P_afsplit_IE_int
import Theorems.Thm_Formalism_UG_P_afsplit_eps_int

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
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸))
    (hM : ∀ i j, M i j ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring)
    (hN : ∀ i j, N i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) (i j : n) :
    afsplitC v M N i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  simp only [afsplitC, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact add_mem (afsplit_IE_int v _ (hM i j))
    (mul_mem (sub_mem (one_mem _) (afsplit_eps_int (E := E) v)) (hN i j))
end Formalism.UG.P
