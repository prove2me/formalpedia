-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_Yh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:22.718629+00:00
-- url     : https://prove2.me/submissions/31ea4673-b372-40ee-829b-00fa603c5c18

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_zero
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_E_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_wW_inj
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_e__inj_b83b9739b71a
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_wW_ne_e__a87a32810661
import Theorems.Thm_Formalism_GM_leadingTermLemmas_m_W_le
import Theorems.Thm_Formalism_GM_leadingTermLemmas_o_le_S
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_Xsq

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
theorem _root_.solution : BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - e - 1) (n - e - 1) (Yh (K := K) LL ρ e m n) := by
  unfold Yh
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h]; exact biHom_zero _ _
  · rw [if_neg h]
    have := biHom_E_pow wW_inj eη_inj wW_ne_eη (biHom_Xsq (K := K) LL ρ m hm n hn) (m (Fin.last N, ρ) - e - 1)
    have hS := m_W_le LL ρ m hm
    have hoS := o_le_S LL
    rwa [show LL.deg (Fin.last N) - m (Fin.last N, ρ) + (m (Fin.last N, ρ) - e - 1) = LL.deg (Fin.last N) - e - 1 by omega,
      show n - m (Fin.last N, ρ) + (m (Fin.last N, ρ) - e - 1) = n - e - 1 by omega] at this
end Formalism.GM.leadingTermLemmas
