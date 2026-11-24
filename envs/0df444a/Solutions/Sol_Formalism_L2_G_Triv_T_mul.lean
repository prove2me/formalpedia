-- Prove2me | solution 1 for Formalism.L2.G.Triv.T_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:23:45.191428+00:00
-- url     : https://prove2.me/submissions/9e25f6c9-ab10-4663-863f-05bfa3b8591b

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal

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
theorem _root_.solution (c : 𝔸) (z : 𝒜) : adelstabT F E (((1 : E) ⊗ₜ[F] c) * z) = c * adelstabT F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [adelstabT, Algebra.TensorProduct.tmul_mul_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
end Formalism.L2.G.Triv
