-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.deligneDatum_unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e3ba92e1-a1d9-5a05-8d2c-d550fb264ef5

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleU1

section Contract

variable {B : Type} [CommRing B]

theorem comap_le_of_isPrime (x : PrimeSpectrum B) (𝔮 : Ideal (Localization.AtPrime x.asIdeal)) (h𝔮 : 𝔮.IsPrime) :
    Ideal.comap (algebraMap B (Localization.AtPrime x.asIdeal)) 𝔮 ≤ x.asIdeal := by
  intro s hs
  by_contra hsx
  apply h𝔮.ne_top
  apply Ideal.eq_top_of_isUnit_mem 𝔮 (Ideal.mem_comap.mp hs)
  exact IsLocalization.map_units (Localization.AtPrime x.asIdeal) (⟨s, hsx⟩ : x.asIdeal.primeCompl)

end Contract

section Chart

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem edgeNondegAt_mono (d : DeligneDatum (K := K) π B) {𝔭 𝔮 : Ideal B} (h : 𝔮 ≤ 𝔭) (M' M : FullLattice 𝒪 K)
    (hd : d.EdgeNondegAt π 𝔭 M' M) : d.EdgeNondegAt π 𝔮 M' M := by
  obtain ⟨hle, hπ, h1, h2⟩ := hd
  refine ⟨hle, hπ, fun v hv hmem => h1 v hv ?_, fun v' hv' hmem => h2 v' hv' ?_⟩
  · obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    exact Submodule.mem_sup.mpr ⟨y, hy, z, Submodule.smul_mono_left h hz, hyz⟩
  · obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    exact Submodule.mem_sup.mpr ⟨y, hy, z, Submodule.smul_mono_left h hz, hyz⟩

theorem edgeNondegAt_map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K) π B)
    {𝔭 : Ideal B} (M' M : FullLattice 𝒪 K) (hd : d.EdgeNondegAt π 𝔭 M' M) (𝔮 : Ideal B') (h𝔮 : 𝔮.IsPrime)
    (hle : Ideal.comap f 𝔮 ≤ 𝔭) : (d.map π f).EdgeNondegAt π 𝔮 M' M := by
  haveI := h𝔮
  obtain ⟨hMM, hπ, h1, h2⟩ := edgeNondegAt_mono π d hle M' M hd
  refine ⟨hMM, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔮 _ (h1 v hv)
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') 𝔮 _ (h2 v' hv')

theorem inEdgeChart_map_toLocRing (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B) (M' M : FullLattice 𝒪 K)
    (hd : d.EdgeNondegAt π x.asIdeal M' M) : (d.map π (toLocRing B x)).InEdgeChart π M' M := by
  intro 𝔮 h𝔮
  refine edgeNondegAt_map π (toLocRing B x) d M' M hd 𝔮 h𝔮 ?_
  intro s hs
  exact comap_le_of_isPrime x 𝔮 h𝔮 (by simpa [Ideal.mem_comap] using hs)

end Chart

section LocalGlobal

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev locMap (𝔭 : Ideal B) [𝔭.IsPrime] (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K (Localization.AtPrime 𝔭) M :=
  AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B (Localization.AtPrime 𝔭))

scoped instance locMap_isLocalizedModule (𝔭 : Ideal B) [𝔭.IsPrime] (M : FullLattice 𝒪 K) :
    IsLocalizedModule 𝔭.primeCompl (locMap (𝒪 := 𝒪) (K := K) 𝔭 M) := by
  infer_instance

theorem locMap_apply (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    locMap x.asIdeal M y = LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v => rfl

theorem lineBaseChange_toLocRing_eq_localized' (x : PrimeSpectrum B) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange (toLocRing B x) M N =
      N.localized' (Localization.AtPrime x.asIdeal) x.asIdeal.primeCompl (locMap x.asIdeal M) := by
  have hfun : (⇑(LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap) :
      latticeBaseChange 𝒪 K B M → latticeBaseChange 𝒪 K (locRing B x) M) = ⇑(locMap x.asIdeal M) :=
    funext fun z => (locMap_apply x M z).symm
  rw [Submodule.localized'_eq_span, lineBaseChange, hfun]

theorem eq_of_forall_map_toLocRing_eq (d d' : DeligneDatum (K := K) π B)
    (h : ∀ x : PrimeSpectrum B, d'.map π (toLocRing B x) = d.map π (toLocRing B x)) : d' = d := by
  apply DeligneDatum.ext'
  funext M
  refine Submodule.eq_of_localization_maximal
    (fun (P : Ideal B) (_ : P.IsMaximal) => Localization.AtPrime P)
    (fun (P : Ideal B) (_ : P.IsMaximal) => latticeBaseChange 𝒪 K (Localization.AtPrime P) M)
    (fun (P : Ideal B) (_ : P.IsMaximal) => locMap P M) ?_
  intro P hP
  have hx := congrArg (fun e : DeligneDatum (K := K) π (Localization.AtPrime P) => e.line M) (h ⟨P, hP.isPrime⟩)
  change lineBaseChange (toLocRing B ⟨P, hP.isPrime⟩) M (d'.line M) =
    lineBaseChange (toLocRing B ⟨P, hP.isPrime⟩) M (d.line M) at hx
  rw [lineBaseChange_toLocRing_eq_localized', lineBaseChange_toLocRing_eq_localized'] at hx
  exact hx

end LocalGlobal

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem deligneDatum_unique (hπ : Irreducible π) {Q : DrinfeldDatum (K := K) π B} {d d' : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (h' : Q.IsQuadrupleOf d') : d' = d := by
  apply eq_of_forall_map_toLocRing_eq π d d'
  intro x
  obtain ⟨hedge, hk₀, hk₁⟩ := h x
  obtain ⟨-, hk₀', hk₁'⟩ := h' x
  exact CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ
    (d.map π (toLocRing B x)) (d'.map π (toLocRing B x)) (Q.L₀ x) (Q.L₁ x)
    (inEdgeChart_map_toLocRing π d x (Q.L₀ x) (Q.L₁ x) hedge)
    (by rw [← hk₁', hk₁]) (by rw [← hk₀', hk₀])

end Main

end P2mKcQuadrupleU1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique.P2mKcQuadrupleU1"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique.P2mKcQuadrupleU1"

open P2mKcQuadrupleU1 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {Q : DrinfeldDatum (K := K) π B} {d d' : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (h' : Q.IsQuadrupleOf d') : d' = d :=
  deligneDatum_unique hπ h h'

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_deligneDatum_unique (solution)
