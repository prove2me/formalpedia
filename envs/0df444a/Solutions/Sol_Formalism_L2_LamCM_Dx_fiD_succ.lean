-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.fiD_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:17.643459+00:00
-- url     : https://prove2.me/submissions/52dc367b-f722-4051-9017-ec5193786627

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_dS_mul_le
import Theorems.Thm_Formalism_L2_LamCM_Dx_dS_le_mul
import Theorems.Thm_Formalism_L2_LamCM_Dx_coe_fiD
import Theorems.Thm_Formalism_L2_LamCM_Dx_sand_comap
import Theorems.Thm_Formalism_L2_LamCM_Dx_exists_unit_one_add_generator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    fiD M = fiD (M.comap (snocL K n)) * imI M hM := by
  apply FractionalIdeal.coeToSubmodule_injective
  show (fiD M : Submodule (𝓞 K) K) = ((fiD (M.comap (snocL K n)) * imI M hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  rw [FractionalIdeal.coe_mul, coe_fiD M hM, coe_fiD _ (sand_comap M hM)]
  show dS M = dS (M.comap (snocL K n)) * M.map (lastL K n)
  obtain ⟨z, hz1, hz⟩ := exists_unit_one_add_generator M hM
  exact le_antisymm (dS_le_mul M z hz1 hz) (dS_mul_le M)
end Formalism.L2.LamCM.Dx
