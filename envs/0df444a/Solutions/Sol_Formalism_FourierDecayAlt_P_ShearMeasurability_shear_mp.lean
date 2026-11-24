-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:46:31.53664+00:00
-- url     : https://prove2.me/submissions/eeac304a-d081-4d18-a3ab-99a809e96733

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_upto_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_lvl_mp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.ShearMeasurability
theorem _root_.solution (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) (hFm : Measurable F) (hF : ShearCond ρ F) :
    MeasurePreserving F volume volume := by
  classical
  have hN : ∀ q, ρ q < Finset.univ.sup ρ + 1 := fun q =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ q))
  have hall : ∀ n, MeasurePreserving (upto ρ F n) volume volume := by
    intro n
    induction n with
    | zero =>
      have h0 : upto ρ F 0 = id := by
        funext x q
        simp [upto]
      rw [h0]
      exact MeasurePreserving.id _
    | succ n ih =>
      rw [upto_succ hF n]
      exact ih.comp (lvl_mp hFm hF n)
  have hF' : upto ρ F (Finset.univ.sup ρ + 1) = F := by
    funext x q
    simp [upto, hN q]
  rw [← hF']
  exact hall _
end Formalism.FourierDecayAlt.P.ShearMeasurability
