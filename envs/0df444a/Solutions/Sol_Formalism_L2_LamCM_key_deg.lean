-- Prove2me | solution 1 for Formalism.L2.LamCM.key_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:30.097692+00:00
-- url     : https://prove2.me/submissions/d13512c3-39c1-4dc3-a9c9-9b3908b6c25a

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Theorems.Thm_Formalism_L2_LamCM_count_eq_of_valuation_le
import Theorems.Thm_Formalism_L2_LamCM_eq_of_count_eq
import Theorems.Thm_Formalism_L2_LamCM_sum_log_norm_embeddings
import Theorems.Thm_Formalism_L2_LamCM_keyDeg_core

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
theorem _root_.solution : KeyDeg := by
  unfold KeyDeg
  intro hKF K _ _ x T abelian₂ hT hL hloc harch
  exact keyDeg_core hKF K x T abelian₂ hT hL hloc harch (fun k hk => sum_log_norm_embeddings hk)
    (fun I k hI hk h => eq_of_count_eq (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hk) hI
      (fun p => by
        obtain ⟨c, hc, h1, h2⟩ := h p
        exact (count_eq_of_valuation_le p hk hc.1 h1 h2).trans hc.2))
end Formalism.L2.LamCM
