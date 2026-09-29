-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_algHom_chartERing_comp_eq_of_isBaseChange_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1b2f3da4-c922-5d02-a85a-9c1f2f00a77f

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_comp_eq_of_isBaseChange_of_surjective
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B25CPL

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']

theorem rTensor_smul' (φ : B' →ₐ[𝒪] B) (N : FullLattice 𝒪 K) (r : B') (n : latticeBaseChange 𝒪 K B' N) :
    LinearMap.rTensor (↥N.1) (φ : B' →ₐ[𝒪] B).toLinearMap (r • n) =
      φ r • LinearMap.rTensor (↥N.1) (φ : B' →ₐ[𝒪] B).toLinearMap n := by
  induction n using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add c e hc he => rw [smul_add, map_add, map_add, smul_add, hc, he]
  | tmul c w =>
    rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul',
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem edgeNondegAt_of_isBaseChange (φ : B' →ₐ[𝒪] B) (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B')
    (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) φ d' d) (M' M : FullLattice 𝒪 K)
    (𝔭' : Ideal B') (𝔭 : Ideal B) (hle : Ideal.map (φ : B' →+* B) 𝔭' ≤ 𝔭)
    (h : d.EdgeNondegAt π 𝔭 M' M) : d'.EdgeNondegAt π 𝔭' M' M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ (N : FullLattice 𝒪 K) (v : ↥N.1),
      (1 : B') ⊗ₜ[𝒪] v ∈ d'.line N ⊔ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' N)) →
      (1 : B) ⊗ₜ[𝒪] v ∈ d.line N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B N)) := by
    intro N v hv
    set F := LinearMap.rTensor (↥N.1) (φ : B' →ₐ[𝒪] B).toLinearMap with hF
    have hI : ∀ b ∈ (𝔭' • ⊤ : Submodule B' (latticeBaseChange 𝒪 K B' N)),
        F b ∈ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B N)) := by
      intro b hb
      induction hb using Submodule.smul_induction_on' with
      | smul r hr n _ =>
        rw [hF, rTensor_smul']
        exact Submodule.smul_mem_smul (hle (Ideal.mem_map_of_mem _ hr)) Submodule.mem_top
      | add c e _ _ hc he => rw [map_add]; exact Submodule.add_mem _ hc he
    have himg : F ((1 : B') ⊗ₜ[𝒪] v) = (1 : B) ⊗ₜ[𝒪] v := by
      rw [hF, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
    rw [← himg]
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    rw [← hab, map_add]
    refine Submodule.add_mem_sup ?_ (hI b hb)
    rw [hd' N]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  exact ⟨h1, h2, fun v hv hmem => h3 v hv (key M v hmem), fun v' hv' hmem => h4 v' hv' (key M' v' hmem)⟩

end B25CPL

open B25CPL in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    (φ : B' →ₐ[𝒪] B) (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker (φ : B' →+* B)))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K))
    (x : chartERing 𝒪 π q →ₐ[𝒪] B)
    (hx0 : d.line (stdFullLattice K) =
      Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hx1 : d.line (FullLattice.act g (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g (stdFullLattice K)).toLinearMap)
    (d' : DeligneDatum (K := K) π B') (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) φ d' d) :
    ∃ x' : chartERing 𝒪 π q →ₐ[𝒪] B', φ.comp x' = x ∧
      d'.line (stdFullLattice K) =
        Submodule.span B' {(x' (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec K 1} ∧
      d'.line (FullLattice.act g (stdFullLattice K)) =
        (Submodule.span B' {(1 : B') ⊗ₜ[𝒪] stdBasisVec K 0 + (x' (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
          (actBaseChange B' g (stdFullLattice K)).toLinearMap := by
  classical
  have hB : IsNilpotent (algebraMap 𝒪 B π) := by
    obtain ⟨n, hn⟩ := hB'
    exact ⟨n, by rw [← φ.commutes, ← map_pow, hn, map_zero]⟩

  have hd'c : d'.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) := by
    intro 𝔭' h𝔭'
    have hker : RingHom.ker (φ : B' →+* B) ≤ 𝔭' := by
      intro r hr
      obtain ⟨n, hn⟩ := hφn
      have : r ^ n ∈ (RingHom.ker (φ : B' →+* B)) ^ n := Ideal.pow_mem_pow hr n
      rw [hn] at this
      exact h𝔭'.mem_of_pow_mem n (by rw [Submodule.zero_eq_bot, Ideal.mem_bot] at this; rw [this]; exact 𝔭'.zero_mem)
    haveI : 𝔭'.IsPrime := h𝔭'
    have hP : (Ideal.map (φ : B' →+* B) 𝔭').IsPrime := Ideal.map_isPrime_of_surjective hφs hker
    exact edgeNondegAt_of_isBaseChange φ d d' hd' _ _ 𝔭' _ le_rfl (hd _ hP)
  have H' := CerednikDrinfeld.FormalOmega.DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
    π hπ q hq g hg B' hB'
  have H := CerednikDrinfeld.FormalOmega.DeligneDatum.existsUnique_algHom_chartERing_line_eq_and_natural_of_inEdgeChart
    π hπ q hq g hg B hB
  obtain ⟨x', ⟨hx'0, hx'1⟩, -⟩ := H'.1 d' hd'c
  obtain ⟨hn0, hn1⟩ := H'.2.2 B φ d' x' ⟨hx'0, hx'1⟩
  have hdd : (Omega K π).map φ d' = d := by
    apply DeligneDatum.ext'
    funext M
    exact (hd' M).symm
  rw [hdd] at hn0 hn1
  obtain ⟨x₀, -, huniq⟩ := H.1 d hd
  exact ⟨x', (huniq (φ.comp x') ⟨hn0, hn1⟩).trans (huniq x ⟨hx0, hx1⟩).symm, hx'0, hx'1⟩

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_comp_eq_of_isBaseChange_of_surjective
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_algHom_chartERing_comp_eq_of_isBaseChange_of_surjective (solution)
