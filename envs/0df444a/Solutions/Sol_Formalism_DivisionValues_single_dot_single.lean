-- Prove2me | solution 1 for Formalism.DivisionValues.single_dot_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:07.750843+00:00
-- url     : https://prove2.me/submissions/34ddff38-8b7f-439b-a88e-582039c00258

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    star (Pi.single a (1 : ℂ)) ⬝ᵥ (N *ᵥ Pi.single b (1 : ℂ)) = N a b := by
  have hs : star (Pi.single a (1 : ℂ) : Fin d → ℂ) = Pi.single a 1 := by
    ext i
    rcases eq_or_ne i a with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  rw [hs]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.DivisionValues
