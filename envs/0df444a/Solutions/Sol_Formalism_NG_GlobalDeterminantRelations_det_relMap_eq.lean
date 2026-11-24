-- Prove2me | solution 1 for Formalism.NG.GlobalDeterminantRelations.det_relMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:23.980354+00:00
-- url     : https://prove2.me/submissions/040c67d2-0638-4754-b57f-4e6cd57da55a

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Theorems.Thm_Formalism_NG_GlobalDeterminantRelations_evalSp_smul

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
open Formalism Formalism.NG
open Formalism.NG.GlobalDeterminantRelations
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')
namespace Formalism.NG.GlobalDeterminantRelations
theorem _root_.solution (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R') :
    LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') Θ) =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det := by
  have hconj := LinearMap.det_conj (relMap (FractionRing O) (EvalSp O d R' x') Θ) (curryE R' x' g).symm
  rw [← hconj, ← LinearMap.det_toLin']
  congr 1
  apply LinearMap.ext
  intro v
  funext p
  obtain ⟨i, a⟩ := p
  let ev : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => (w : d → FractionRing O) a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  show ev (∑ j, Θ i j • (curryE R' x' g v) j) =
    Matrix.mulVec (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ) v (i, a)
  rw [map_sum]
  have hev : ∀ j, ev (Θ i j • (curryE R' x' g v) j) =
      ∑ b, (Θ i j : X' → Matrix d d (FractionRing O)) x' a b * v (j, b) := fun j =>
    evalSp_smul R' x' (Θ i j) ((curryE R' x' g v) j) a
  rw [Finset.sum_congr rfl (fun j _ => hev j), Matrix.mulVec]
  first
    | (rw [dotProduct, Fintype.sum_prod_type]; rfl)
    | (rw [Matrix.dotProduct, Fintype.sum_prod_type]; rfl)
    | (simp only [dotProduct, Fintype.sum_prod_type]; rfl)
end Formalism.NG.GlobalDeterminantRelations
