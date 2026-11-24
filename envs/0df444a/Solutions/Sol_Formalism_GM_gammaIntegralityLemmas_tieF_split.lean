-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.tieF_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:32.305459+00:00
-- url     : https://prove2.me/submissions/e25316f5-2687-4eef-b348-4473509e5958

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieF_eq_FT
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (ρ : Fin r) :
    Formalism.GM.tieF w e = Dop (p := p) (w ρ) (e ρ) + FT w e (univ.erase ρ) := by
  rw [tieF_eq_FT, ← FT_insert w e ρ _ (notMem_erase ρ univ), insert_erase (mem_univ ρ)]
end Formalism.GM.gammaIntegralityLemmas
