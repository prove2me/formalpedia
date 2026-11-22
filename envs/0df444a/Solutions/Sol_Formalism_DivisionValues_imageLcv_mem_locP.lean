-- Prove2me | solution 1 for Formalism.DivisionValues.imageLcv_mem_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:00.293474+00:00
-- url     : https://prove2.me/submissions/f356232f-49ba-4418-8be8-5f0500de830e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv

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
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.DivisionValues
theorem _root_.solution (p : Ideal R) [p.IsPrime] (A : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl
end Formalism.DivisionValues
