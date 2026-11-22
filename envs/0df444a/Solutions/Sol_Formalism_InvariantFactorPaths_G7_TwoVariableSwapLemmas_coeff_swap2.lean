-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:06.068086+00:00
-- url     : https://prove2.me/submissions/67e1270e-9a7c-4584-83c1-93954df91dc0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_eq_rename_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
theorem _root_.solution (G : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) :
    coeff n (swap2 G) = coeff (sw n) G := by
  have h : n = Finsupp.embDomain (Equiv.swap (0 : Fin 2) 1).toEmbedding (sw n) := by
    rw [Finsupp.embDomain_eq_mapDomain, sw, Finsupp.equivMapDomain_eq_mapDomain,
      ← Finsupp.mapDomain_comp]
    have hid : (⇑(Equiv.swap (0 : Fin 2) 1).toEmbedding ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
      funext i
      simp
    rw [hid, Finsupp.mapDomain_id]
  rw [swap_two_eq_rename_equiv]
  conv_lhs => rw [h]
  exact coeff_embDomain_rename _ _ _
end Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
