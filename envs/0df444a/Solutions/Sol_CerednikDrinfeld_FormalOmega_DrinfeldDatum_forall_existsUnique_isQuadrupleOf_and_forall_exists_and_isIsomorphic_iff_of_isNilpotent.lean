-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/65f6fe82-c9ef-5f4d-9724-297eefc2eada

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) :
    (∀ Q : DrinfeldDatum (K := K) π B, ∃! d : DeligneDatum (K := K) π B, Q.IsQuadrupleOf d) ∧
    (∀ d : DeligneDatum (K := K) π B, ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d) ∧
    (∀ (Q Q' : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B),
      Q.IsQuadrupleOf d → (Q'.IsQuadrupleOf d ↔ Q'.IsIsomorphic Q)) := by
  refine ⟨fun Q => ?_, fun d => CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf hπ hfin hB d, fun Q Q' d h =>
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.isQuadrupleOf_iff_isIsomorphic hπ hB h Q'⟩
  obtain ⟨d, hd⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf hπ hB Q
  exact ⟨d, hd, fun d' hd' => CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique hπ hd hd'⟩

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_forall_existsUnique_isQuadrupleOf_and_forall_exists_and_isIsomorphic_iff_of_isNilpotent (solution)
