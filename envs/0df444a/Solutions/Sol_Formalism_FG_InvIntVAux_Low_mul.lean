-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.Low.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:42.569819+00:00
-- url     : https://prove2.me/submissions/e58c1e75-4c64-4d90-bf94-2775cb905ee4

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV

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
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
variable {σ : Type*}
namespace Formalism.FG.InvIntVAux
namespace Low
theorem _root_.solution {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = d := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | exact (_root_.Finset.mem_antidiagonal).mp hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← hp']
    first
      | exact (Finsupp.degree_add p.1 p.2).symm
      | exact (map_add Finsupp.degree p.1 p.2).symm
      | simp
  by_cases h1 : p.1.degree < m
  · rw [hx _ h1, zero_mul]
  · rw [hy _ (by omega), mul_zero]
end Low
end Formalism.FG.InvIntVAux
