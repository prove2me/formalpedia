-- Prove2me | solution 1 for Formalism.FG.SolveVAux.low_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:55.301407+00:00
-- url     : https://prove2.me/submissions/b0bcd5b1-7676-4686-81f2-17e2481269bc

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {M N : ℕ} {p q : MvPowerSeries τ R} (hp : Low M p) (hq : Low N q) :
    Low (M + N) (p * q) := by
  classical
  intro d hd
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := map_add _ _ _
  rw [hx] at hdeg
  rcases lt_or_ge x.1.degree M with h1 | h1
  · rw [hp _ h1, zero_mul]
  · rw [hq _ (by omega), mul_zero]
end Formalism.FG.SolveVAux
