-- Prove2me | solution 1 for Formalism.UG.P.cartan_mem_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:53.030056+00:00
-- url     : https://prove2.me/submissions/20214eaf-2126-4542-acd2-d16723a9af26

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (U : GL n L) (h1 : ∀ i j, (U : Matrix n n L) i j ∈ O)
    (h2 : ∀ i j, ((U⁻¹ : GL n L) : Matrix n n L) i j ∈ O) : U ∈ GLint n O := by
  have key : ∀ (A : Matrix n n L) (hA : ∀ i j, A i j ∈ O),
      (Matrix.of fun i j => (⟨A i j, hA i j⟩ : O)).map O.subtype = A := fun A hA => by
    ext
    rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨(U : Matrix n n L) i j, h1 i j⟩,
    Matrix.of fun i j => ⟨((U⁻¹ : GL n L) : Matrix n n L) i j, h2 i j⟩, ?_, ?_⟩, ?_⟩
  · apply hinj
    dsimp only
    rw [Matrix.map_mul, key, key, Matrix.map_one _ (map_zero _) (map_one _)]
    exact U.mul_inv
  · apply hinj
    dsimp only
    rw [Matrix.map_mul, key, key, Matrix.map_one _ (map_zero _) (map_one _)]
    exact U.inv_mul
  · exact Units.ext (key _ h1)
end Formalism.UG.P
