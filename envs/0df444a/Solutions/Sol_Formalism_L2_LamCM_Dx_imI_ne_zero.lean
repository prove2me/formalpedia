-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.imI_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:18.210378+00:00
-- url     : https://prove2.me/submissions/32963361-3e4d-47e8-aa3d-63740d1d18e4

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
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : imI M hM ≠ 0 := by
  obtain ⟨a, ha, hs⟩ := hM.1
  intro h0
  have hmem : algebraMap (𝓞 K) K a ∈ (imI M hM : Submodule (𝓞 K) K) :=
    ⟨_, hs (Fin.last n), by simp⟩
  rw [h0] at hmem
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha ((FractionalIdeal.mem_zero_iff _).1 hmem)
end Formalism.L2.LamCM.Dx
