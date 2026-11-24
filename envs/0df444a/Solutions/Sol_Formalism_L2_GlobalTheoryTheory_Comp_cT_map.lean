-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.cT_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:02:22.934802+00:00
-- url     : https://prove2.me/submissions/57e3d526-2e9b-498d-a3bb-1e05ffacdbfe

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ExistsUnitaryOneDetEq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (σ : E →ₐ[F] E) {p q : Type} (Q : Matrix p q E) :
    cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) = (cT (σ : E →+* E) Q).map ιA := by
  unfold Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  first
  | rfl
  | simp [Formalism.UG.sigR, Formalism.UG.inclE]
  | simp [Formalism.UG.P.sigR, Formalism.UG.P.inclE]
  | simp [Formalism.UG.CS.sigR, Formalism.UG.CS.inclE]
  | (unfold Formalism.UG.sigR; done)
end Formalism.L2.GlobalTheoryTheory.Comp
