-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.bihomogeneous_leading_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:23.190082+00:00
-- url     : https://prove2.me/submissions/edebdaf8-985e-47ac-a927-7caac4f04485

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_zero
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
theorem _root_.solution : BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - e) (n - e) (V0 (K := K) LL ρ e m n) := by
  unfold V0
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h]; have := biHom_Xsq (K := K) LL ρ m hm n hn; rwa [h] at this
  · rw [if_neg h]; exact biHom_zero _ _
end Formalism.GM.leadingTermLemmas
