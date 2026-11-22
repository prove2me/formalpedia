-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.m_W_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:45.587593+00:00
-- url     : https://prove2.me/submissions/f301e97d-0208-4bca-a0de-88df89b216f8

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

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
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    m (Fin.last N, ρ) ≤ LL.deg (Fin.last N) := by
  rw [← hm (Fin.last N)]
  exact Finset.single_le_sum (f := fun c => m (Fin.last N, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
end Formalism.GM.leadingTermLemmas
