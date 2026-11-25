-- Prove2me | solution 1 for Formalism.HC.EAtH.explicit_formula_error_of_host_conditions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:52:44.664955+00:00
-- url     : https://prove2.me/submissions/c1edfea1-b2fc-483b-b24c-9b113c35936b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
namespace Formalism.HC
namespace EAtH
theorem _root_.solution {T : HType} {κ : HConst} {X x : ℝ} {φ : Frame} {H : HostRaw φ} (hr : T.InRange X x φ.e) (hC : 0 ≤ κ.C)
    (h : HostConditions T κ X x H) {TT : Finset φ.A} (hs : φ.Shares TT (x ^ (-1 + T.eps))) :
    EAtH (T.level φ.o) H TT x T.eps (κ.C * T.J) := by
  refine ⟨rfl, h.kept, h.e, hs, h.c1, fun θ hθ N _ χ hχ => (h.b.2 θ hθ N χ hχ).trans ?_⟩
  obtain ⟨h1, h2, -⟩ := hr
  have hJ : (0 : ℝ) < T.J := by exact_mod_cast T.one_le_J
  have h3 := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) h2
  rw [Real.log_rpow (by linarith), div_mul_eq_mul_div, one_mul, div_le_iff₀ hJ] at h3
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hC
end EAtH
end Formalism.HC
