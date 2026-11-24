-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.q_etaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:05.393491+00:00
-- url     : https://prove2.me/submissions/8e2475e9-64fe-4f5c-9990-5d3b1d249866

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_weight_ind
import Theorems.Thm_Formalism_GM_GammaExpansion_q_isWH
import Theorems.Thm_Formalism_GM_GammaExpansion_degH_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last N))
    (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hh : h ∈ M.Pol p r (lowerLast LL e)) :
    ∀ s ∈ (aeval (M.freezeSub p LL ρ) h).support, s (Fin.last (N + 1), ρ) ≤ LL.total - e := by
  intro s hs
  have hw : Finsupp.weight (fun x : Fin (N + 1 + 1) × Fin r => (if x.1 = Fin.last (N + 1) then 1 else 0)) s =
      LL.total - e := by
    rw [← degH_eq LL e he]
    exact q_isWH p LL ρ e h hh (fun b' => if b' = Fin.last (N + 1) then 1 else 0) (mem_support_iff.1 hs)
  rw [weight_ind] at hw
  rw [← hw]
  exact Finset.single_le_sum (f := fun c => s (Fin.last (N + 1), c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ ρ)
end Formalism.GM.GammaExpansion
