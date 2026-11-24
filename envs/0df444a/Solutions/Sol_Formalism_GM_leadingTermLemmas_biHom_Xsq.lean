-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_Xsq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:07.610803+00:00
-- url     : https://prove2.me/submissions/17e73594-e632-4323-87c3-1ad84b2e0289

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_mul
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_Xeta
import Theorems.Thm_P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
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
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (n : ℕ) (hn : LL.total ≤ n) :
    BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - m (Fin.last N, ρ)) (n - m (Fin.last N, ρ))
      (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq (K := K) LL ρ m) := by
  have h1 := biHom_pow (biHom_Xeta (K := K) (N := N) ρ) (n - LL.total)
  have h2 := biHom_mul h1 (biHom_sq' (K := K) LL ρ m hm)
  have hS := m_W_le LL ρ m hm
  have hoS := o_le_S LL
  rwa [mul_zero, zero_add, mul_one, show n - LL.total + (LL.total - m (Fin.last N, ρ)) = n - m (Fin.last N, ρ) by omega]
    at h2
end Formalism.GM.leadingTermLemmas
