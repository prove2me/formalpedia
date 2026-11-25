-- Prove2me | solution 1 for Formalism.L2.LamCM.local_generator_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:17.729265+00:00
-- url     : https://prove2.me/submissions/15d67e94-a8cc-476f-8c0c-60880d232ac9

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
import Theorems.Thm_Formalism_L2_LamCM_count_coeIdeal_eq_zero
import Theorems.Thm_Formalism_L2_LamCM_exists_split_of_isLocGen
import Theorems.Thm_Formalism_L2_LamCM_eq_bcI
import Theorems.Thm_Formalism_L2_LamCM_bcI_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_bcI_mul
import Theorems.Thm_Formalism_L2_LamCM_bcI_spanSingleton
import Theorems.Thm_Formalism_L2_LamCM_bcI_coeIdeal
import Theorems.Thm_P2M_Formalism_L2_LamCM_spanSingleton_ne_zero__ef0616425764


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
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : LocGenBaseChange := by
  intro K K1 _ _ _ _ _ L L1 p p1 c hI hB hp hc
  obtain ⟨A, B, hA, hB', hAB⟩ := exists_split_of_isLocGen p hI hc
  have hc1 : algebraMap K K1 c ≠ 0 := (map_ne_zero _).mpr hc.1
  have hmap : ∀ X : Ideal (𝓞 K), ¬ X ≤ p.asIdeal → ¬ X.map (algebraMap (𝓞 K) (𝓞 K1)) ≤ p1.asIdeal := by
    intro X hX hle
    obtain ⟨x, hxX, hxp⟩ := SetLike.not_le_iff_exists.mp hX
    exact hxp ((hp x).mpr (hle (Ideal.mem_map_of_mem _ hxX)))
  have hne : ∀ X : Ideal (𝓞 K), ¬ X ≤ p.asIdeal →
      ((X.map (algebraMap (𝓞 K) (𝓞 K1)) : Ideal (𝓞 K1)) : FractionalIdeal (𝓞 K1)⁰ K1) ≠ 0 := by
    intro X hX h0
    rw [FractionalIdeal.coeIdeal_eq_zero] at h0
    exact hmap X hX (h0 ▸ bot_le)
  have h1 := congrArg (bcI (K1 := K1)) hAB
  rw [bcI_mul, bcI_mul, bcI_spanSingleton, bcI_coeIdeal, bcI_coeIdeal, ← eq_bcI hB] at h1
  have h2 := congrArg (FractionalIdeal.count K1 p1) h1
  rw [FractionalIdeal.count_mul K1 p1 (by rw [eq_bcI hB]; exact bcI_ne_zero hI) (hne B hB'),
    FractionalIdeal.count_mul K1 p1 (spanSingleton_ne_zero' hc1) (hne A hA),
    count_coeIdeal_eq_zero p1 (hmap A hA), count_coeIdeal_eq_zero p1 (hmap B hB')] at h2
  exact ⟨hc1, by omega⟩
end Formalism.L2.LamCM
