-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.wordFusion_list
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:28.245523+00:00
-- url     : https://prove2.me/submissions/f57ea4aa-4ce9-493e-9766-4dfdddee3dcb

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_embedding_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_entries_mem_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_isDet_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_isRTT_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_isDet_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_entriesCommute_prod

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
set_option maxHeartbeats 800000
namespace Formalism.FourierDecayAlt.P.W
theorem _root_.solution (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ x ∈ L, IsRTT x.1 ∧ IsDet x.1 x.2)
    (hp : L.Pairwise (fun x y => EntriesCommute x.1 y.1)) :
    IsRTT (fun Y => (L.map (fun x => x.1 Y)).prod) ∧
      IsDet (fun Y => (L.map (fun x => x.1 Y)).prod) (fun Y => (L.map (fun x => x.2 Y)).prod) := by
  induction L with
  | nil =>
    refine ⟨?_, ?_⟩
    · unfold Formalism.FourierDecayAlt.W.IsRTT
      intro Y Y'
      simp [first_embedding_one, entries_mem_one]
    · rw [isDet_iff]
      intro Y
      simp
  | cons x t ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, IsRTT y.1 ∧ IsDet y.1 y.2 := fun y hy => h y (by simp [hy])
    rw [List.pairwise_cons] at hp
    obtain ⟨ih1, ih2⟩ := ih ht hp.2
    have hc := entriesCommute_prod x.1 t hp.1
    have e1 := isRTT_mul x.1 _ hx.1 ih1 hc
    have e2 := isDet_mul x.1 _ x.2 _ hx.2 ih2 hc
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · first
      | exact e1
      | simpa using e1
    · first
      | exact e2
      | simpa using e2
end Formalism.FourierDecayAlt.P.W
