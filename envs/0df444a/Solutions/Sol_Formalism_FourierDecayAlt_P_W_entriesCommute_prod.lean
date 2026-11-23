-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.entriesCommute_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:40.805335+00:00
-- url     : https://prove2.me/submissions/d4d54ee9-aeaa-44d6-b4c0-4768d758bde0

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]
namespace Formalism.FourierDecayAlt.P.W
theorem _root_.solution (M : R → Matrix (Fin 2) (Fin 2) B)
    (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ y ∈ L, EntriesCommute M y.1) :
    EntriesCommute M (fun Y => (L.map (fun x => x.1 Y)).prod) := by
  unfold Formalism.FourierDecayAlt.W.EntriesCommute at *
  intro Y Y' i j k l
  induction L generalizing k l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs <;> simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * y.1 Y' k l = y.1 Y' k l * M Y i j :=
      fun y hy => h y (by simp [hy])
    exact (Commute.sum_right _ _ _ (fun m _ => Commute.mul_right (hx Y Y' i j k m) (ih ht m l))).eq
end Formalism.FourierDecayAlt.P.W
