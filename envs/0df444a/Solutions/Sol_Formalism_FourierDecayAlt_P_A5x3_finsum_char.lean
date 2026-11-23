-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.finsum_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:27.40669+00:00
-- url     : https://prove2.me/submissions/df43e9de-a6ec-4b36-8e37-bfc41c523429

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution {G : Type} [AddCommGroup G] [Finite G] (χ : AddChar G ℂ) :
    ((∀ g, χ g = 1) → ∑ᶠ g, χ g = (Nat.card G : ℂ)) ∧ ((∃ g, χ g ≠ 1) → ∑ᶠ g, χ g = 0) := by
  classical
  have := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, AddChar.sum_eq_ite, Nat.card_eq_fintype_card]
  constructor
  · intro hg
    rw [if_pos (AddChar.eq_zero_iff.2 hg)]
  · intro hg
    rw [if_neg (AddChar.ne_zero_iff.2 hg)]
end Formalism.FourierDecayAlt.P.A5x3
