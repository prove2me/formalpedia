-- Prove2me | solution 1 for Formalism.L2.LamCM.key_degree_essential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:39.069386+00:00
-- url     : https://prove2.me/submissions/10ccde02-9744-4bbf-8dca-fd2e11dc123f

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
import Theorems.Thm_Formalism_L2_LamCM_keyDegCore_core
import Theorems.Thm_Formalism_L2_LamCM_count_eq_of_valuation_le
import Theorems.Thm_Formalism_L2_LamCM_eq_of_count_eq
import Theorems.Thm_Formalism_L2_LamCM_sum_log_norm_embeddings


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
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution : KeyDegCore := by
  intro hKC K _ _ x T abelian₂ hT hL hloc harch
  refine keyDegCore_core hKC K x T abelian₂ hT hL hloc harch (fun k hk => sum_log_norm_embeddings hk)
    (fun I k hI hk hlocI => ?_)
  have hsk : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hk
  refine eq_of_count_eq hsk hI (fun p => ?_)
  obtain ⟨c, h1, h2, h3⟩ := hlocI p
  rw [count_eq_of_valuation_le p hk h1.1 h2 h3, h1.2]
end Formalism.L2.LamCM
