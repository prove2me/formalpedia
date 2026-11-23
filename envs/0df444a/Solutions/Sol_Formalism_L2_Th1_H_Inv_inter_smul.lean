-- Prove2me | solution 1 for Formalism.L2.Th1.H.Inv.inter_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:20.263+00:00
-- url     : https://prove2.me/submissions/498874d0-7fa4-4b64-9aa9-0ea0ea0cab96

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
namespace Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
private theorem finsum_const_mul' {ι : Type*} (c : ℂ) (f : ι → ℂ) : ∑ᶠ i, c * f i = c * ∑ᶠ i, f i := by
  have h := smul_finsum c f
  simpa only [smul_eq_mul] using h.symm
end Inv
open Inv
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.Inv
theorem _root_.solution (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (c : ℂ) (F : V → ℂ) :
    inter H α Λ₁ Λ₂ (c • F) = c • inter H α Λ₁ Λ₂ F := by
  funext z
  simp only [Formalism.L2.Th1.H.inter, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm c]
  congr 1
  rw [← finsum_const_mul']
  refine finsum_congr fun q => ?_
  simp only [Formalism.L2.Th1.H.opU, Pi.smul_apply, smul_eq_mul]
  ring
end Formalism.L2.Th1.H.Inv
