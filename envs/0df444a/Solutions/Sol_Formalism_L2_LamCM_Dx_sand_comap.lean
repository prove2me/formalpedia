-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.sand_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:19.502194+00:00
-- url     : https://prove2.me/submissions/b2701848-23d4-47bb-89dd-f4fd17940236

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_castSucc
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_last
attribute [local simp] Formalism.L2.LamCM.Dx.lastL_apply

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : Sand (M.comap (snocL K n)) := by
  obtain ⟨⟨a, ha, hs⟩, ⟨b, hb, hint⟩⟩ := hM
  refine ⟨⟨a, ha, fun i => ?_⟩, ⟨b, hb, fun x hx i => ?_⟩⟩
  · show snocL K n _ ∈ M
    have : snocL K n (Pi.single i (algebraMap (𝓞 K) K a)) = Pi.single (Fin.castSucc i) (algebraMap (𝓞 K) K a) := by
      ext k; refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [(Fin.castSucc_lt_last i).ne']
      · simp [Pi.single_apply, Fin.castSucc_inj]
    rw [this]; exact hs _
  · have := hint _ hx (Fin.castSucc i)
    simpa using this
end Formalism.L2.LamCM.Dx
