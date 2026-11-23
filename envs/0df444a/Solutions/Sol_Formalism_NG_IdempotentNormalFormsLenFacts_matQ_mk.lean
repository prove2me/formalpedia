-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.matQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:50.990139+00:00
-- url     : https://prove2.me/submissions/9c7ba96b-b6f1-4fad-a1e9-1680d4f2e3d1

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsLenFacts
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.IdempotentNormalFormsLenFacts
theorem _root_.solution {ι : Type*} [Fintype ι] (A : Matrix ι ι O) (y : ι → FractionRing O) :
    matQ O A (fun i => (Submodule.Quotient.mk (y i) : KO O)) =
      fun i => (Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i) : KO O) := by
  ext i
  show ∑ j, A i j • (Submodule.mkQ (1 : Submodule O (FractionRing O)) (y j)) =
    Submodule.mkQ (1 : Submodule O (FractionRing O))
      ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i)
  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.map_apply, Algebra.smul_def]
end Formalism.NG.IdempotentNormalFormsLenFacts
