-- Prove2me | solution 1 for Formalism.L2.Geo.Def.PC.levelafC_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:52.288546+00:00
-- url     : https://prove2.me/submissions/143b7cb5-c83e-494a-82ef-cbc7a8eaed5c

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE

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
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.Geo.Def.PC
theorem _root_.solution (N : ℕ) : levelafC E ((N : ℕ) : 𝓞 F) = (N : 𝒜) := by
  unfold levelafC
  rw [map_natCast]
  first
    | (rw [← Algebra.TensorProduct.includeRight_apply, map_natCast])
    | simp
    | norm_cast
end Formalism.L2.Geo.Def.PC
