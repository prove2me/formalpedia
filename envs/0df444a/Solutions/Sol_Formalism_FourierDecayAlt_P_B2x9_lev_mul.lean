-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.lev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:52.384448+00:00
-- url     : https://prove2.me/submissions/d206e037-10d8-4192-b224-0f80dafd9391

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mid_or
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levPos_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levPos_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
private lemma iotaLev_levPos_apply_of_col_outside (g : Mat k r') (i : Fin (2 * r' + k + 1)) (m : Fin (2 * (1 + r') + k + 1))
    (hm : ¬ (1 ≤ m.val ∧ m.val < 2 * r' + k + 1 + 1)) : ιLev k 1 r' g (levPos k 1 r' i) m = 0 := by
  unfold ιLev
  rw [dif_pos (levPos_mid i), dif_neg hm]
private lemma iotaLev_apply_of_first_index_outside (g : Mat k r') (p : Fin (2 * (1 + r') + k + 1))
    (hp : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) (m : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g p m = if p = m then 1 else 0 := by
  unfold ιLev
  rw [dif_neg hp]
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9
namespace Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x9.S1
namespace Formalism.FourierDecayAlt.P.B2x9.S2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x9.S2
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  ext p q
  rw [Matrix.mul_apply]
  rcases mid_or p with ⟨i, rfl⟩ | hp
  · rcases mid_or q with ⟨j, rfl⟩ | hq
    · rw [lev_mid, Matrix.mul_apply]
      have hsub : ∑ m, ιLev k 1 r' g (levPos k 1 r' i) m * ιLev k 1 r' h m (levPos k 1 r' j) =
          ∑ m ∈ Finset.univ.map ⟨levPos k 1 r', levPos_inj⟩,
            ιLev k 1 r' g (levPos k 1 r' i) m * ιLev k 1 r' h m (levPos k 1 r' j) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro m _ hm
        rcases mid_or m with ⟨l, rfl⟩ | hm'
        · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ l)) hm
        · rw [iotaLev_levPos_apply_of_col_outside g i m hm', zero_mul]
      rw [hsub, Finset.sum_map]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Function.Embedding.coeFn_mk]
      rw [lev_mid, lev_mid]
    · rw [iotaLev_levPos_apply_of_col_outside _ i q hq]
      symm
      apply Finset.sum_eq_zero
      intro m _
      rcases mid_or m with ⟨l, rfl⟩ | hm
      · rw [iotaLev_levPos_apply_of_col_outside h l q hq, mul_zero]
      · rw [iotaLev_levPos_apply_of_col_outside g i m hm, zero_mul]
  · rw [iotaLev_apply_of_first_index_outside (g * h) p hp q]
    simp only [iotaLev_apply_of_first_index_outside g p hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [iotaLev_apply_of_first_index_outside h p hp q]
end Formalism.FourierDecayAlt.P.B2x9
