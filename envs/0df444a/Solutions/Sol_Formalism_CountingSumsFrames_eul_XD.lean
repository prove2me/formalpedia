-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eul_XD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:41.370773+00:00
-- url     : https://prove2.me/submissions/04f79ba6-c732-4eb0-ad1d-1b0fb64414fa

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_eulX
import Theorems.Thm_Formalism_GM_ProjS_eulL_mul
import Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ : Type} {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c d : Fin s)
    (g : MvPolynomial σ ℚ_[p]) :
    ProjS.eulL t (X (t c) * pderiv (t d) g) = X (t c) * pderiv (t d) (ProjS.eulL t g) := by
  rw [ProjS.eulL_mul, eulX t ht, ProjS.eulL_pderiv_mem t ht d g]; ring
end Formalism.CountingSumsFrames
