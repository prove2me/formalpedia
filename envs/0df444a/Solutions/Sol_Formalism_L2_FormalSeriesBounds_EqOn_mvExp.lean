-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.EqOn.mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:57.012729+00:00
-- url     : https://prove2.me/submissions/bb0017a6-cfa4-40ac-a958-b76c4f4db30a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace EqOn
theorem _root_.solution {A : Set σ} {F G : MvPowerSeries σ K} (h : EqOn A F G) : EqOn A (mvExp F) (mvExp G) := by
  intro μ hμ
  show ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : K) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (G ^ k) / (k.factorial : K)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]
end EqOn
end Formalism.L2.FormalSeriesBounds
