-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.frz_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:12.868853+00:00
-- url     : https://prove2.me/submissions/8e38c238-3fc1-4ec9-ae3e-9aefb7083152

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_aeval_fSub_monomial
import Theorems.Thm_Formalism_GM_leadingTermLemmas_prod_split
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fSub_alt
import Theorems.Thm_Formalism_GM_leadingTermLemmas_tieE_pow_eq

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (hv : LL.vec (Fin.last N) = true) (n : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    frz K LL ρ n (monomial m 1) =
      (tieE (wW (N := N)) eη ^ (m (Fin.last N, ρ))) (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq LL ρ m) := by
  rw [frz, aeval_fSub_monomial, prod_split _ m (Fin.last N, ρ), fSub_alt LL ρ hv, tieE_pow_eq, sq]
  ring
end Formalism.GM.leadingTermLemmas
