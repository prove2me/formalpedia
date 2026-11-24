-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.Yh_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:12.280803+00:00
-- url     : https://prove2.me/submissions/f23229e5-0502-4975-a747-67c32032b4c9

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_m_W_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_o_le_S

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)
variable (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m)
  (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) (hn : LL.total ≤ n)
include hm hme hn
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution : Yh (K := K) LL ρ e m n ≠ 0 → 1 ≤ LL.deg (Fin.last N) - e ∧ 1 ≤ n - e := by
  intro h
  unfold Yh at h
  by_cases h' : m (Fin.last N, ρ) = e
  · rw [if_pos h'] at h; exact absurd rfl h
  · have hS := m_W_le LL ρ m hm
    have hoS := o_le_S LL
    omega
end Formalism.GM.leadingTermLemmas
