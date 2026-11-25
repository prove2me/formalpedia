-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.tieF_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:33.901522+00:00
-- url     : https://prove2.me/submissions/a6c0761c-7fdf-46df-b41a-2066ea935b88

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieF_split
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ) (ρ : Fin r)
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (j : ℕ) (Z : MvPolynomial σ ℚ_[p]) :
    (Formalism.GM.tieF w e ^ j) Z = ∑ a ∈ range (j + 1),
      ((j.choose a : ℕ) : ℚ_[p]) • (Dop (w ρ) (e ρ) ^ a) ((FT w e (univ.erase ρ) ^ (j - a)) Z) := by
  rw [tieF_split w e ρ, (FT_commute w e (w ρ) (e ρ) (univ.erase ρ)).add_pow j, LinearMap.sum_apply]
  apply sum_congr rfl
  intro a _
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    Nat.cast_smul_eq_nsmul]
end Formalism.GM.gammaIntegralityLemmas
