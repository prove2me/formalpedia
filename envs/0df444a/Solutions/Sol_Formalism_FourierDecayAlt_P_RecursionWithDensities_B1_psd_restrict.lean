-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.psd_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:44.835189+00:00
-- url     : https://prove2.me/submissions/cfc49fbc-a27d-4820-ae1c-031da58a36d5

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
section gen
variable {α : Type}
variable {E : Type} [AddCommGroup E]
end gen
section ta
variable {E : Type} [Field E] [DecidableEq E]
end ta
section main
variable {E : Type} [Field E] [DecidableEq E]
end main
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
private theorem sum_attach_ite_eq {α : Type} (X : Finset α) (a : α) (F : α → ℂ) :
    (∑ j ∈ X.attach, if (j : α) = a then F j else 0) = if a ∈ X then F a else 0 := by
  rw [Finset.sum_attach (s := X) (f := fun j => if j = a then F j else 0)]
  first
  | exact Finset.sum_ite_eq' X a F
  | simp
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.P.OneLevelCoefficients Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B2
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
namespace Formalism.FourierDecayAlt.P
open RecursionWithDensities
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution {α : Type} {X : Finset α} (Y : Finset α) {k : α → α → ℂ} (hk : PSDOn X k) :
    PSDOn Y (fun x y => if x ∈ X ∧ y ∈ X then k x y else 0) := by
  unfold TB.PSDOn at hk ⊢
  have hB := hk.conjTranspose_mul_mul_same
    (Matrix.of fun (x : X) (y : Y) => if (x : α) = (y : α) then (1 : ℂ) else 0)
  convert hB using 1
  ext y y'
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite (star : ℂ → ℂ)]
  rw [sum_attach_ite_eq X (y' : α) (fun a => ∑ j ∈ X.attach, if (j : α) = (y : α) then k j a else 0),
    sum_attach_ite_eq X (y : α) (fun a => k a y')]
  by_cases hy : (y : α) ∈ X <;> by_cases hy' : (y' : α) ∈ X <;> simp [hy, hy']
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
