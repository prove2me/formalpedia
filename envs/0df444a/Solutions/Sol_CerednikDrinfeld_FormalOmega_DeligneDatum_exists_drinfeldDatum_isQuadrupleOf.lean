-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a64c7d35-6f81-5b77-9544-647618789c70

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) : ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d := by
  classical
  obtain ⟨k, f, hf, M', M, hcov⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent hπ hfin hB d
  have hBi : ∀ i : Fin k, IsNilpotent (algebraMap 𝒪 (Localization.Away (f i)) π) := by
    intro i
    rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i))]
    exact hB.map _
  have hQ : ∀ i : Fin k, ∃ Q : DrinfeldDatum (K := K) π (Localization.Away (f i)),
      Q.IsQuadrupleOf (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))) := fun i =>
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart hπ (hBi i) (hcov i).1 (hcov i).2.1
      (hcov i).2.2.1 _ (hcov i).2.2.2
  exact CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away hπ hB d f hf
    (fun i => (hQ i).choose) (fun i => (hQ i).choose_spec)

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf (solution)
