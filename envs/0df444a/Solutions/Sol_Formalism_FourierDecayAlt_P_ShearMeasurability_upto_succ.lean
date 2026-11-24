-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.upto_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:30.320816+00:00
-- url     : https://prove2.me/submissions/9a6a8bd8-322d-4669-a960-0ace3f570d33

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability

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
theorem _root_.solution {ρ : ι → ℕ} {F : (ι → ℂ) → ι → ℂ} (hF : ShearCond ρ F) (n : ℕ) :
    upto ρ F (n + 1) = upto ρ F n ∘ lvl ρ F n := by
  funext x q
  show (if ρ q < n + 1 then F x q else x q) =
    (if ρ q < n then F (lvl ρ F n x) q else lvl ρ F n x q)
  have hlv : ∀ p, ρ p ≠ n → lvl ρ F n x p = x p := fun p hp => by
    simp only [lvl]
    rw [if_neg hp]
  by_cases h1 : ρ q < n
  · rw [if_pos (by omega), if_pos h1]
    have h2 := hF q x (lvl ρ F n x) (fun p hp => (hlv p (by omega)).symm)
    rw [hlv q (by omega)] at h2
    linear_combination h2
  · by_cases h2 : ρ q = n
    · rw [if_pos (by omega), if_neg h1]
      simp only [lvl]
      rw [if_pos h2]
    · rw [if_neg (by omega), if_neg h1, hlv q h2]
end Formalism.FourierDecayAlt.P.ShearMeasurability
