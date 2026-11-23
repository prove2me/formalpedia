-- Prove2me | solution 1 for Formalism.D5.thick_average_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:37.420637+00:00
-- url     : https://prove2.me/submissions/78b1a68f-7c99-4c88-8801-95d457323cae

import Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Theorems.Thm_Formalism_D5_balTop_split
import Theorems.Thm_Formalism_D5_sum_thick_term_eq_gaussSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
namespace Formalism.D5
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] :
    ThickAverage (H := H) := by
  unfold ThickAverage
  intro m Hs Nd
  have hj : ∀ (t : H) (j : Fin m), ∑ u0 : H, (thickZ Hs Nd u0 t j).re =
      (Nd.T2.card : ℝ) / 2 * (Nd.bj j * (GC Hs 0 (Nd.a t / Nd.bj j)
        + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j)
        - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)).re) := by
    intro t j
    rw [← Complex.re_sum, sum_thick_term_eq_gaussSums,
      show ((Nd.T2.card : ℂ) / 2 * ((Nd.bj j : ℝ) : ℂ))
        = (((Nd.T2.card : ℝ) / 2 * Nd.bj j : ℝ) : ℂ) by push_cast; try ring,
      Complex.re_ofReal_mul]
    ring
  have hswap : ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re
      = ∑ t ∈ Nd.T, ∑ j : Fin m, ∑ u0 : H, (thickZ Hs Nd u0 t j).re := by
    calc ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re
        = ∑ t ∈ Nd.T, ∑ u0 : H, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re := Finset.sum_comm
      _ = ∑ t ∈ Nd.T, ∑ j : Fin m, ∑ u0 : H, (thickZ Hs Nd u0 t j).re :=
          Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
  simp_rw [balTop_split Hs Nd, Finset.sum_add_distrib, mul_add]
  congr 1
  · rw [hswap, signal]
    simp_rw [hj, ← Finset.mul_sum]
    ring
end Formalism.D5
