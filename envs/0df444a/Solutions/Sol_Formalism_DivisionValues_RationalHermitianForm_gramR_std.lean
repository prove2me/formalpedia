-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.gramR_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:24.065089+00:00
-- url     : https://prove2.me/submissions/48c172ef-9ec8-4f72-bfef-483af67cc9bd

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm

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
open Formalism.DivisionValues.RationalHermitianForm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.RationalHermitianForm
theorem _root_.solution {D : ℕ} (Γ : Matrix (Fin D) (Fin D) K) :
    gramR Γ (fun i => (Pi.single i 1 : Fin D → K)) = Γ.det := by
  unfold gramR
  congr 1
  ext a b
  have hst : ∀ x : Fin D, star ((Pi.single a (1 : K) : Fin D → K) x) = (Pi.single a (1 : K) : Fin D → K) x := by
    intro x; rcases eq_or_ne x a with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  simp only [Matrix.of_apply, dotProduct, Pi.star_apply, hst]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.DivisionValues.RationalHermitianForm
