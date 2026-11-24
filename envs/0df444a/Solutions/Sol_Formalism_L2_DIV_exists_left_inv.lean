-- Prove2me | solution 1 for Formalism.L2.DIV.exists_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.501509+00:00
-- url     : https://prove2.me/submissions/0f9e68b4-2fbb-476a-ba6e-6a3f2e4cbac8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
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
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {F : Type} [Field F] {n d : ℕ} (E : Matrix (Fin n) (Fin d) F)
    (h : Function.Injective E.mulVec) : ∃ L : Matrix (Fin d) (Fin n) F, L * E = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' E) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' E) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' E) = 1 := by
    rw [hg]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1
end Formalism.L2.DIV
