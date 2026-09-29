-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1325bd39-9ec8-5069-b171-52cf1446efd6

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_normal_finiteIndex_forall_isOfFinOrder_imp_eq_one
import Theorems.Thm_CerednikDrinfeld_natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct Quaternion MatrixGroups
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld ValuationSubring

theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [Algebra R₀ ↥(ratClosure A)] [IsFractionRing R₀ ↥(ratClosure A)]
    (hR₀ : ∀ x : ↥(ratClosure A), x ∈ Set.range (algebraMap R₀ ↥(ratClosure A)) ↔
      Valued.v (algebraMap ↥(ratClosure A) A.valuation.Completion x) ≤ 1)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) (hι : Function.Injective ι)
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ratClosure A)))
    (hρ : ∀ x : (ℍ[ℚ, a, b])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a, b] →* Matrix (Fin 2) (Fin 2) ↥(ratClosure A)) x))
    [MulAction (ℍ[ℚ, a, b])ˣ (LT.LatticeTree.Vertex R₀ ↥(ratClosure A))] :
    ∃ Γ'' : Subgroup (ℍ[ℚ, a, b])ˣ,
      Γ'' ≤ CosetGraph.awayUnits R v ⊓ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
          (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A)) ∧
      Γ''.relIndex (CosetGraph.awayUnits R v ⊓ Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A))
          (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A))) ≠ 0 ∧
      ∀ g ∈ Γ''.map ρ, IsOfFinOrder g → g = 1 := by
  classical

  obtain ⟨n, hn⟩ : ∃ n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, n ∈ primeHeckeSet R r := by
    have hcard := CerednikDrinfeld.natCard_setOf_exists_mem_primeHeckeSet_quotientMk_eq_eq_succ_of_prime
      R r hR hrN hrq'.symm hdef
    have hpos : 0 < Nat.card {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R //
        ∃ g ∈ primeHeckeSet R r,
          (QuotientGroup.mk g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c} := by
      rw [hcard]; exact Nat.succ_pos r
    obtain ⟨⟨c, g, hg, -⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨g, hg⟩

  obtain ⟨-, ψ, -, hψ, -, -⟩ :=
    CerednikDrinfeld.CosetGraph.exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq
      hdef hR hrq' hrN v hv hn A hA R₀ hR₀ ι hι ρ hρ

  obtain ⟨Γ', -, hfi, htf⟩ :=
    CerednikDrinfeld.CosetGraph.exists_normal_finiteIndex_forall_isOfFinOrder_imp_eq_one hdef hR hrq' hrN v hv

  set Aw : Subgroup (ℍ[ℚ, a, b])ˣ := CosetGraph.awayUnits R v with hAw
  set tp : Subgroup (ℍ[ℚ, a, b])ˣ :=
    Mumford.typePreserving (ℍ[ℚ, a, b])ˣ (BruhatTits.tree R₀ ↥(ratClosure A)) (LT.LatticeTree.stdVertex R₀ ↥(ratClosure A))
    with htp
  let π : ↥Aw →* CosetGraph.ProjAwayUnits R v := QuotientGroup.mk' (CosetGraph.actionKer R v)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Γ₁ : Subgroup ↥Aw := Γ'.comap π
  let T : Subgroup ↥Aw := tp.subgroupOf Aw
  have hsub : Function.Injective Aw.subtype := Aw.subtype_injective
  refine ⟨(Γ₁ ⊓ T).map Aw.subtype, ?_, ?_, ?_⟩
  ·
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y.2, hy.2⟩
  ·
    have hT : Aw ⊓ tp = T.map Aw.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [hT, Subgroup.relIndex_map_map_of_injective _ _ hsub, Subgroup.inf_relIndex_right]
    have h1 : Γ₁.relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      show (Γ'.comap π).index ≠ 0
      rw [Subgroup.index_comap_of_surjective Γ' hπ]
      exact hfi.index_ne_zero
    exact fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right le_top h0)
  ·
    rintro g ⟨x, ⟨y, hy, rfl⟩, rfl⟩ hfin
    have hy1 : π y ∈ Γ' := hy.1
    have hψy : ((ψ (π y) : ↥((CosetGraph.awayUnits R v).map ρ)) : PGL(2, ↥(ratClosure A))) = ρ (Aw.subtype y) := hψ y
    obtain ⟨m, hm, hgm⟩ := (isOfFinOrder_iff_pow_eq_one).mp hfin
    have hs : (ψ (π y)) ^ m = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hψy, Subgroup.coe_one]
      exact hgm
    have hπy : (π y) ^ m = 1 := by
      apply ψ.injective
      rw [map_pow, map_one, hs]
    have : π y = 1 := htf _ hy1 ((isOfFinOrder_iff_pow_eq_one).mpr ⟨m, hm, hπy⟩)
    rw [← hψy, this, map_one, Subgroup.coe_one]

end S_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_le_awayUnits_inf_typePreserving_relIndex_ne_zero_forall_isOfFinOrder_eq_one (solution)
