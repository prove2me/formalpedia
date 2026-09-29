-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1cd1682b-1a73-594c-88ef-f40540ee173c

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_of_edgeNondegAt_maximalIdeal
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_of_vertexNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K) (d' : DeligneDatum (K := K) π B),
      DeligneDatum.IsPullback (K := K) (π := π) B h d d' ∧
      d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
  classical
  have h𝔪 : (IsLocalRing.maximalIdeal B).IsPrime := (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have hcoe : ((unitOfNeZero (K := K) hπ.ne_zero : Kˣ) : K) = algebraMap 𝒪 K π := unitOfNeZero_coe hπ.ne_zero

  obtain ⟨P', P, hP₁, hP₂, hE⟩ : ∃ P' P : FullLattice 𝒪 K,
      latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) P.1 < P'.1 ∧ P'.1 < P.1 ∧
        d.EdgeNondegAt π (IsLocalRing.maximalIdeal B) P' P := by
    obtain ⟨M', M, hMM⟩ := d.exists_edgeNondegAt π (IsLocalRing.maximalIdeal B) h𝔪
    have hπle : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.1 hv
      rw [hcoe]
      exact hMM.2.1 ⟨w, hw⟩
    by_cases hdeg : M'.1 = M.1 ∨ M'.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1
    ·
      have hV : d.VertexNondegAt π (IsLocalRing.maximalIdeal B) M := by
        rcases hdeg with heq | heq
        · have hMM' : M' = M := Subtype.ext heq
          subst hMM'
          exact hMM.2.2.2
        · intro v hv
          refine hMM.2.2.1 v ?_
          rw [heq]
          intro hvmem
          obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.1 hvmem
          exact hv ⟨⟨w, hw⟩, by rw [← hwv, hcoe]⟩
      obtain ⟨M'', hlt₁, hlt₂⟩ := CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt π hπ M
      refine ⟨M'', M, hlt₁, hlt₂, ?_⟩
      refine CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_of_vertexNondegAt π d _ M'' M hlt₂.le ?_ hV
      intro v
      apply hlt₁.le
      rw [← hcoe]
      exact mem_latticeMap_scalarGL.2 ⟨v, v.2, rfl⟩
    · push Not at hdeg
      exact ⟨M', M, lt_of_le_of_ne hπle (Ne.symm hdeg.2), lt_of_le_of_ne hMM.1 hdeg.1, hMM⟩

  have hIn : d.InEdgeChart π P' P :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.inEdgeChart_of_edgeNondegAt_maximalIdeal π d P' P hE

  obtain ⟨h, hP, hP'⟩ :=
    CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt π hπ g hg P' P hP₁ hP₂
  refine ⟨h, DeligneDatum.pullback π B h d, DeligneDatum.isPullback_pullback π B h d, ?_⟩
  intro 𝔭 h𝔭
  have hT := CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv π d h 𝔭 P' P (hIn 𝔭 h𝔭)
  have e1 : FullLattice.act h⁻¹ P = stdFullLattice K := by
    rw [← hP]; exact Subtype.ext (latticeMap_inv_latticeMap h _)
  have e2 : FullLattice.act h⁻¹ P' = FullLattice.act g (stdFullLattice K) := by
    rw [← hP']; exact Subtype.ext (latticeMap_inv_latticeMap h _)
  rw [e1, e2] at hT
  exact hT

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing (solution)
