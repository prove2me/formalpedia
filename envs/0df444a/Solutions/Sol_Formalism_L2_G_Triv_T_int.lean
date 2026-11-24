-- Prove2me | solution 1 for Formalism.L2.G.Triv.T_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:42:51.565625+00:00
-- url     : https://prove2.me/submissions/c93d8dd4-42f1-4243-a0c8-3d1a8609028e

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Theorems.Thm_Formalism_L2_G_Triv_T_mul
import Theorems.Thm_Formalism_UG_P_adelstabT_mem
import Theorems.Thm_Formalism_UG_P_afsplitIE_tmul
import Theorems.Thm_Formalism_UG_P_afsplitI_self
import Theorems.Thm_Formalism_UG_P_afsplit_IE_int
import Theorems.Thm_Formalism_UG_P_afsplit_decomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.G.Triv
theorem _root_.solution (z : 𝒜) (hz : ∀ v, prV (E := E) v z ∈ SV E v) : adelstabT F E z ∈ intAd F := by
  intro v
  have h1 := adelstabT_mem (afsplit_IE_int v _ (hz v))
  rw [afsplit_decomp, afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul, T_mul] at h1
  have h2 := h1 v
  rw [afsplit_mul_apply, afsplitI_self, one_mul] at h2
  exact h2
end Formalism.L2.G.Triv
