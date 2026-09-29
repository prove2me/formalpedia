-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/05978209-59b5-59d2-9404-6445ae555eec

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finset_span_eq_top_forall_inEdgeChart_map_away
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_fullLattice_lt_and_lt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_of_vertexNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B25CC

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

theorem exists_genuine (π : 𝒪) (hπ : Irreducible π) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (hd : d.InEdgeChart π M' M) :
    ∃ M'' : FullLattice 𝒪 K, latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M''.1 ∧ M''.1 < M.1 ∧
      d.InEdgeChart π M'' M := by

  by_cases hgen : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 ∧ M'.1 < M.1
  · exact ⟨M', hgen.1, hgen.2, hd⟩

  have hπle : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [unitOfNeZero_coe]; exact hπM w hw
  have hV : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → d.VertexNondegAt π 𝔭 M := by
    intro 𝔭 h𝔭 v hv
    obtain ⟨h1, h2, h3, h4⟩ := hd 𝔭 h𝔭
    rcases not_and_or.mp hgen with hng | hng
    ·
      have heq : M'.1 = latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 :=
        (eq_of_le_of_not_lt hπle hng).symm
      apply h3 v
      intro hvM'
      rw [heq, mem_latticeMap_scalarGL] at hvM'
      obtain ⟨w, hw, hwv⟩ := hvM'
      exact hv ⟨⟨w, hw⟩, by rw [← hwv, unitOfNeZero_coe]⟩
    ·
      have heq : M'.1 = M.1 := eq_of_le_of_not_lt hle hng
      have heq' : M' = M := Subtype.ext heq
      subst heq'
      exact h4 v hv
  obtain ⟨M'', h1, h2⟩ := CerednikDrinfeld.FormalOmega.exists_fullLattice_lt_and_lt π hπ M
  refine ⟨M'', h1, h2, fun 𝔭 h𝔭 => ?_⟩
  apply CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_of_vertexNondegAt π d 𝔭 M'' M h2.le
  · intro v
    apply h1.le
    exact mem_latticeMap_scalarGL.mpr ⟨v, v.2, by rw [unitOfNeZero_coe]⟩
  · exact hV 𝔭 h𝔭

end B25CC

open B25CC in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (d : DeligneDatum (K := K) π B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧ ∀ r ∈ s,
      ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K) (x : chartERing 𝒪 π q →ₐ[𝒪] Localization.Away r),
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).InEdgeChart π
          (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) ∧
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).line (stdFullLattice K) =
          Submodule.span (Localization.Away r)
            {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : Localization.Away r) ⊗ₜ[𝒪] stdBasisVec K 1} ∧
        (DeligneDatum.pullback π (Localization.Away r) h
            (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)))).line (FullLattice.act g (stdFullLattice K)) =
          (Submodule.span (Localization.Away r)
            {(1 : Localization.Away r) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
            (actBaseChange (Localization.Away r) g (stdFullLattice K)).toLinearMap := by
  obtain ⟨s, hs, hcov⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finset_span_eq_top_forall_inEdgeChart_map_away
    (K := K) (inferInstance : Finite (𝒪 ⧸ Ideal.span {π})) hB d
  refine ⟨s, hs, fun r hr => ?_⟩
  obtain ⟨M', M, hle, hπM, -, hd⟩ := hcov r hr
  set dr := d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)) with hdr
  obtain ⟨M'', h1, h2, hd''⟩ := exists_genuine π hπ dr M' M hle hπM hd
  obtain ⟨h, hM, hM''⟩ := CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt π hπ g hg M'' M h1 h2

  have hstd : (DeligneDatum.pullback π (Localization.Away r) h dr).InEdgeChart π
      (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
    intro 𝔭 h𝔭
    have key := CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv π dr h 𝔭 M'' M (hd'' 𝔭 h𝔭)
    have e1 : FullLattice.act h⁻¹ M'' = FullLattice.act g (stdFullLattice K) := by
      rw [← hM'']; exact Subtype.ext (latticeMap_inv_latticeMap h _)
    have e2 : FullLattice.act h⁻¹ M = stdFullLattice K := by
      rw [← hM]; exact Subtype.ext (latticeMap_inv_latticeMap h _)
    rw [e1, e2] at key
    exact key
  have hBr : IsNilpotent (algebraMap 𝒪 (Localization.Away r) π) := by
    rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away r)]; exact hB.map _
  obtain ⟨x, hx0, hx1⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_algHom_chartERing_line_eq_of_inEdgeChart_of_finite
    π hπ q hq g hg (Localization.Away r) hBr _ hstd
  exact ⟨h, x, hstd, hx0, hx1⟩

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_cover_pullback_map_inEdgeChart_stdEdge_line_eq (solution)
