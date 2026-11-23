-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.edgeW_swap_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:46.186094+00:00
-- url     : https://prove2.me/submissions/108c5f63-cff6-4fc2-9ad6-3e179096cd8e

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_of_ne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_swap_mul_apply_right

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}
variable {R : Type u} [CommRing R]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (w : Fin n → Fin n → R) {a b : Fin n} (hab : a < b) {τ : Equiv.Perm (Fin n)}
    (hτa : τ a = a) (hτb : τ b = b) : edgeW w (Equiv.swap a b * τ) = w a b * edgeW w τ := by
  unfold edgeW
  have hset : Finset.univ.filter (fun i => i < (Equiv.swap a b * τ) i) =
      insert a (Finset.univ.filter (fun i => i < τ i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hia : i = a
    · subst hia
      simp [swap_mul_apply_left hτa, hab]
    · by_cases hib : i = b
      · subst hib
        simp [swap_mul_apply_right hτb, hτb, hia, hab.le]
      · simp [swap_mul_apply_of_ne hτa hτb hia hib, hia]
  have hna : a ∉ Finset.univ.filter (fun i => i < τ i) := by
    simp [hτa]
  rw [hset, Finset.prod_insert hna, swap_mul_apply_left hτa]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < τ i := (Finset.mem_filter.mp hi).2
  have hia : i ≠ a := fun h => by rw [h, hτa] at hi'; exact lt_irrefl _ hi'
  have hib : i ≠ b := fun h => by rw [h, hτb] at hi'; exact lt_irrefl _ hi'
  rw [swap_mul_apply_of_ne hτa hτb hia hib]
end Formalism.DworkPowerSeriesWeights
