-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.isRTT_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:00.21855+00:00
-- url     : https://prove2.me/submissions/80e733ac-19cc-447d-911d-903a633bb2d9

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_entries_mem_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_first_second_embedding_commute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
section Words
variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]
private theorem rtt_relation_mul_of_rtt_of_commute {A : Type*} [Ring A] (P a b c d : A) (hM : P * a * c = c * a * P)
    (hN : P * b * d = d * b * P) (c1 : b * c = c * b) (c2 : a * d = d * a) :
    P * (a * b) * (c * d) = c * d * (a * b) * P := by
  calc P * (a * b) * (c * d) = P * a * (b * c) * d := by simp only [mul_assoc]
    _ = P * a * (c * b) * d := by rw [c1]
    _ = (P * a * c) * b * d := by simp only [mul_assoc]
    _ = (c * a * P) * b * d := by rw [hM]
    _ = c * a * (P * b * d) := by simp only [mul_assoc]
    _ = c * a * (d * b * P) := by rw [hN]
    _ = c * (a * d) * b * P := by simp only [mul_assoc]
    _ = c * (d * a) * b * P := by rw [c2]
    _ = c * d * (a * b) * P := by simp only [mul_assoc]
end Words
section Norm
end Norm
end Formalism.FourierDecayAlt.P.W
namespace Formalism.FourierDecayAlt.P
open NumberField
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]
namespace Formalism.FourierDecayAlt.P.W
theorem _root_.solution (M N : R → Matrix (Fin 2) (Fin 2) B) (hM : IsRTT M) (hN : IsRTT N)
    (hc : EntriesCommute M N) : IsRTT (fun Y => M Y * N Y) := by
  unfold Formalism.FourierDecayAlt.W.IsRTT at *
  intro Y Y'
  simp only [first_embedding_mul, entries_mem_mul]
  exact rtt_relation_mul_of_rtt_of_commute _ _ _ _ _ (hM Y Y') (hN Y Y')
    (first_second_embedding_commute _ _ (fun i j k l => (hc Y Y' k l i j).symm)) (first_second_embedding_commute _ _ (fun i j k l => hc Y' Y i j k l))
end Formalism.FourierDecayAlt.P.W
