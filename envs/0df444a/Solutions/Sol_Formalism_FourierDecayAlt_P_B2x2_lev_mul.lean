-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:33:37.205965+00:00
-- url     : https://prove2.me/submissions/b5bc8b03-fb46-4de9-9c33-2e5d65a74113

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_levPos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_n

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution (k r' : ℕ) (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hp : mid k r' p
  · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
    rw [← Fintype.sum_of_injective (levPos k 1 r') (levPos_inj k r')
      (fun u => g s u * ιLev k 1 r' h (levPos k 1 r' u) q)
      (fun l => ιLev k 1 r' g (levPos k 1 r' s) l * ιLev k 1 r' h l q)
      (fun l hl => by
        simp only [lev_mn k r' g _ l (mid_levPos k r' s) (fun hm => hl ((mid_iff k r' l).1 hm)),
          zero_mul])
      (fun u => by simp only [lev_mm])]
    by_cases hq : mid k r' q
    · obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
      simp only [lev_mm, Matrix.mul_apply]
    · have hz : ∀ (g' : Mat k r') (u : Fin (2 * r' + k + 1)), ιLev k 1 r' g' (levPos k 1 r' u) q = 0 :=
        fun g' u => lev_mn k r' g' _ q (mid_levPos k r' u) hq
      simp only [hz, mul_zero, Finset.sum_const_zero]
  · rw [lev_n k r' _ p q hp]
    simp only [lev_n k r' g p _ hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, lev_n k r' h p q hp]
end Formalism.FourierDecayAlt.P.B2x2
