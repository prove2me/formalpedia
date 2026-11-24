-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.submatrix_mul_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:57.713835+00:00
-- url     : https://prove2.me/submissions/a4453f08-e284-4ed4-93eb-785c0c300946

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p k : ℕ} (h : k ≤ p) (L X : Matrix (Fin p) (Fin p) ℂ)
    (hL : ∀ a b, a < b → L a b = 0) {l : Type*} (f : l → Fin p) :
    (L * X).submatrix (Fin.castLE h) f =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * X.submatrix (Fin.castLE h) f := by
  ext a b
  simp only [submatrix_apply, mul_apply]
  symm
  have e1 : ∑ t : Fin k, L (Fin.castLE h a) (Fin.castLE h t) * X (Fin.castLE h t) (f b) =
      ∑ t ∈ Finset.univ.map (Fin.castLEEmb h), L (Fin.castLE h a) t * X t (f b) := by
    rw [Finset.sum_map]
    rfl
  rw [e1]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro t _ ht
  have hk : k ≤ t.val := by
    by_contra hlt
    have hlt : t.val < k := not_le.mp hlt
    exact ht (Finset.mem_map.mpr ⟨⟨t.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hL _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega), zero_mul]
end Formalism.FourierDecayAlt.P.Ux5
