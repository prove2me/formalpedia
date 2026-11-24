-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:02.792728+00:00
-- url     : https://prove2.me/submissions/92498662-2eb0-453f-907c-c80b6a34b1d6

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_prod_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_fSub

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
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) :
    BiHom (wW (N := N)) eη (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * (if x.1 = Fin.last N then 1 else 0))
      (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * 1) (sq (K := K) LL ρ m) :=
  biHom_prod_pow _ _ _ _ _ (fun x _ => biHom_fSub LL ρ x)
end Formalism.GM.leadingTermLemmas
