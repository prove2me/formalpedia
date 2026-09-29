-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isQuadrupleOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5433c05c-ebdb-5dc3-a4d6-2cc590c7aa0e

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq
import Theorems.Thm_Submodule_exists_invertible_quotient_and_forall_localized_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleB

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev locMap (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K (locRing B x) M :=
  AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B (locRing B x))

scoped instance locMap_isLocalizedModule (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) :
    IsLocalizedModule x.asIdeal.primeCompl (locMap (𝒪 := 𝒪) (K := K) x M) := by
  infer_instance

theorem locMap_apply (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    locMap x M y = LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v => rfl

theorem locMap_one_tmul (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (v : ↥M.1) :
    locMap x M ((1 : B) ⊗ₜ[𝒪] v) = (1 : locRing B x) ⊗ₜ[𝒪] v := by
  rw [locMap_apply, rTensor_one_tmul]

abbrev locSub (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    Submodule (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) M) :=
  N.localized' (locRing B x) x.asIdeal.primeCompl (locMap x M)

theorem lineBaseChange_toLocRing_eq_locSub (x : PrimeSpectrum B) (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) :
    lineBaseChange (toLocRing B x) M N = locSub x M N := by
  have hfun : (⇑(LinearMap.rTensor (↥M.1) (toLocRing B x).toLinearMap) :
      latticeBaseChange 𝒪 K B M → latticeBaseChange 𝒪 K (locRing B x) M) = ⇑(locMap x M) :=
    funext fun z => (locMap_apply x M z).symm
  change lineBaseChange (toLocRing B x) M N = N.localized' (locRing B x) x.asIdeal.primeCompl (locMap x M)
  rw [Submodule.localized'_eq_span, lineBaseChange, hfun]

theorem mem_locSub_of_mem (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) {N : Submodule B (latticeBaseChange 𝒪 K B M)}
    {z : latticeBaseChange 𝒪 K B M} (hz : z ∈ N) : locMap x M z ∈ locSub x M N :=
  ⟨z, hz, 1, IsLocalizedModule.mk'_one _ _ z⟩

theorem mem_of_forall_locMap_mem (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (z : latticeBaseChange 𝒪 K B M) (h : ∀ x : PrimeSpectrum B, locMap x M z ∈ locSub x M N) : z ∈ N := by
  refine Submodule.mem_of_localization_maximal
    (fun (P : Ideal B) (_ : P.IsMaximal) => latticeBaseChange 𝒪 K (Localization.AtPrime P) M)
    (fun (P : Ideal B) (_ : P.IsMaximal) => locMap ⟨P, inferInstance⟩ M) z N ?_
  intro P hP
  exact h ⟨P, hP.isPrime⟩

theorem locMap_mem_maximalIdeal_smul_top (x : PrimeSpectrum B) (M : FullLattice 𝒪 K)
    {z : latticeBaseChange 𝒪 K B M} (hz : z ∈ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    locMap x M z ∈ (IsLocalRing.maximalIdeal (locRing B x) • ⊤ :
      Submodule (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) M)) := by
  induction hz using Submodule.smul_induction_on' with
  | smul b hb w _ =>
    rw [LinearMap.map_smul, ← algebraMap_smul (locRing B x) b (locMap x M w)]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (locRing B x) x.asIdeal b).mpr hb
  | add u w _ _ hu hw =>
    rw [map_add]
    exact Submodule.add_mem _ hu hw

theorem one_tmul_not_mem_sup (x : PrimeSpectrum B) (M : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B M))
    (Nx : Submodule (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) M)) (hN : locSub x M N ≤ Nx) (v : ↥M.1)
    (h : (1 : locRing B x) ⊗ₜ[𝒪] v ∉ Nx ⊔ (IsLocalRing.maximalIdeal (locRing B x) • ⊤ :
      Submodule (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) M))) :
    (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  intro hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  apply h
  rw [← locMap_one_tmul x M v, ← hyz, map_add]
  exact Submodule.mem_sup.mpr ⟨_, hN (mem_locSub_of_mem x M hy), _, locMap_mem_maximalIdeal_smul_top x M hz, rfl⟩

end Loc

section FP

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

scoped instance finite_lattice (M : FullLattice 𝒪 K) : Module.Finite 𝒪 ↥M.1 :=
  Module.Finite.iff_fg.mpr M.2.1

scoped instance finitePresentation_lattice (M : FullLattice 𝒪 K) : Module.FinitePresentation 𝒪 ↥M.1 :=
  Module.finitePresentation_of_finite 𝒪 ↥M.1

scoped instance finitePresentation_latticeBaseChange (M : FullLattice 𝒪 K) :
    Module.FinitePresentation B (latticeBaseChange 𝒪 K B M) :=
  inferInstanceAs (Module.FinitePresentation B (B ⊗[𝒪] ↥M.1))

end FP

section Glue

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

def dloc (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    DeligneDatum (K := K) π (locRing B x) :=
  Classical.choose (CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_localDeligneDatum hπ Q x)

theorem dloc_spec (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    LinearMap.ker (Q.u₀ x) = (dloc hπ Q x).line (Q.L₀ x) ∧ LinearMap.ker (Q.u₁ x) = (dloc hπ Q x).line (Q.L₁ x) ∧
      (dloc hπ Q x).InEdgeChart π (Q.L₀ x) (Q.L₁ x) :=
  Classical.choose_spec (CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_localDeligneDatum hπ Q x)

theorem exists_glued_line (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) :
    ∃ N : Submodule B (latticeBaseChange 𝒪 K B L), Module.Invertible B (latticeBaseChange 𝒪 K B L ⧸ N) ∧
      ∀ x : PrimeSpectrum B, locSub x L N = (dloc hπ Q x).line L := by
  refine Submodule.exists_invertible_quotient_and_forall_localized_eq
    (fun x : PrimeSpectrum B => latticeBaseChange 𝒪 K (locRing B x) L) (fun x => locMap x L)
    (fun x => (dloc hπ Q x).line L) (fun x => (dloc hπ Q x).invertible L) fun x => ?_
  obtain ⟨r, hr, N, hNfg, hN⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq hπ hB Q x L
  refine ⟨r, hr, N, hNfg, fun y hy => ?_⟩
  obtain ⟨h₀, h₁, hch⟩ := dloc_spec hπ Q y
  have := hN y hy (dloc hπ Q y) h₀ h₁ hch
  rwa [lineBaseChange_toLocRing_eq_locSub] at this

def gline (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) : Submodule B (latticeBaseChange 𝒪 K B L) :=
  Classical.choose (exists_glued_line hπ hB Q L)

theorem gline_invertible (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) : Module.Invertible B (latticeBaseChange 𝒪 K B L ⧸ gline hπ hB Q L) :=
  (Classical.choose_spec (exists_glued_line hπ hB Q L)).1

theorem locSub_gline (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) (x : PrimeSpectrum B) : locSub x L (gline hπ hB Q L) = (dloc hπ Q x).line L :=
  (Classical.choose_spec (exists_glued_line hπ hB Q L)).2 x

theorem lineBaseChange_gline (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    lineBaseChange (toLocRing B x) L (gline hπ hB Q L) = (dloc hπ Q x).line L := by
  rw [lineBaseChange_toLocRing_eq_locSub, locSub_gline]

theorem mem_gline_iff (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) (z : latticeBaseChange 𝒪 K B L) :
    z ∈ gline hπ hB Q L ↔ ∀ x : PrimeSpectrum B, locMap x L z ∈ (dloc hπ Q x).line L := by
  constructor
  · intro hz x
    rw [← locSub_gline hπ hB Q L x]
    exact mem_locSub_of_mem x L hz
  · intro h
    refine mem_of_forall_locMap_mem L _ z fun x => ?_
    rw [locSub_gline]
    exact h x

end Glue

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem locMap_inclBaseChange (x : PrimeSpectrum B) {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1)
    (z : latticeBaseChange 𝒪 K B M') :
    locMap x M (inclBaseChange B h z) = inclBaseChange (locRing B x) h (locMap x M' z) := by
  rw [locMap_apply, locMap_apply]
  exact rTensor_inclBaseChange (toLocRing B x) h z

theorem locMap_actBaseChange (x : PrimeSpectrum B) (g : GL (Fin 2) K) (M : FullLattice 𝒪 K)
    (z : latticeBaseChange 𝒪 K B M) :
    locMap x (FullLattice.act g M) (actBaseChange B g M z) = actBaseChange (locRing B x) g M (locMap x M z) := by
  rw [locMap_apply, locMap_apply]
  exact rTensor_actBaseChange (toLocRing B x) g M z

def dglob (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B) :
    DeligneDatum (K := K) π B where
  line L := gline hπ hB Q L
  invertible L := gline_invertible hπ hB Q L
  mono {M' M} h := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    rw [mem_gline_iff] at hz ⊢
    intro x
    rw [locMap_inclBaseChange]
    exact (dloc hπ Q x).mono h (Submodule.mem_map_of_mem (hz x))
  homothety c M := by
    apply le_antisymm
    · intro z hz
      rw [mem_gline_iff] at hz

      refine Submodule.mem_map.mpr ⟨(actBaseChange B (scalarGL c) M).symm z, ?_, LinearEquiv.apply_symm_apply _ z⟩
      rw [mem_gline_iff]
      intro x
      have hx := hz x
      rw [(dloc hπ Q x).homothety c M] at hx
      obtain ⟨w, hw, hwz⟩ := hx
      have hz' : locMap x (FullLattice.act (scalarGL c) M) z =
          actBaseChange (locRing B x) (scalarGL c) M (locMap x M ((actBaseChange B (scalarGL c) M).symm z)) := by
        conv_lhs => rw [← LinearEquiv.apply_symm_apply (actBaseChange B (scalarGL c) M) z]
        exact locMap_actBaseChange x (scalarGL c) M _
      have hinj := (actBaseChange (locRing B x) (scalarGL c) M).injective
      have : locMap x M ((actBaseChange B (scalarGL c) M).symm z) = w := by
        apply hinj
        rw [← hz']
        exact hwz.symm
      rw [this]
      exact hw
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
      rw [mem_gline_iff] at hz ⊢
      intro x
      rw [(dloc hπ Q x).homothety c M]
      change locMap x (FullLattice.act (scalarGL c) M) (actBaseChange B (scalarGL c) M z) ∈ _
      rw [locMap_actBaseChange]
      exact Submodule.mem_map_of_mem (hz x)
  nondeg 𝔭 h𝔭 := by
    let x : PrimeSpectrum B := ⟨𝔭, h𝔭⟩
    obtain ⟨hle, hπM, h1, h2⟩ := (dloc_spec hπ Q x).2.2 (IsLocalRing.maximalIdeal (locRing B x)) inferInstance
    refine ⟨Q.L₀ x, Q.L₁ x, hle, hπM, fun v hv => ?_, fun v' hv' => ?_⟩
    · exact one_tmul_not_mem_sup x (Q.L₁ x) _ _ (le_of_eq (locSub_gline hπ hB Q (Q.L₁ x) x)) v (h1 v hv)
    · exact one_tmul_not_mem_sup x (Q.L₀ x) _ _ (le_of_eq (locSub_gline hπ hB Q (Q.L₀ x) x)) v' (h2 v' hv')

theorem dglob_line (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B)
    (L : FullLattice 𝒪 K) : (dglob hπ hB Q).line L = gline hπ hB Q L := rfl

theorem isQuadrupleOf_dglob (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B) :
    Q.IsQuadrupleOf (dglob hπ hB Q) := by
  intro x
  obtain ⟨hk₀, hk₁, hch⟩ := dloc_spec hπ Q x
  obtain ⟨hle, hπM, h1, h2⟩ := hch (IsLocalRing.maximalIdeal (locRing B x)) inferInstance
  refine ⟨⟨hle, hπM, fun v hv => ?_, fun v' hv' => ?_⟩, ?_, ?_⟩
  · exact one_tmul_not_mem_sup x (Q.L₁ x) _ _ (le_of_eq (locSub_gline hπ hB Q (Q.L₁ x) x)) v (h1 v hv)
  · exact one_tmul_not_mem_sup x (Q.L₀ x) _ _ (le_of_eq (locSub_gline hπ hB Q (Q.L₀ x) x)) v' (h2 v' hv')
  · rw [hk₀]
    change _ = lineBaseChange (toLocRing B x) (Q.L₀ x) (gline hπ hB Q (Q.L₀ x))
    rw [lineBaseChange_gline]
  · rw [hk₁]
    change _ = lineBaseChange (toLocRing B x) (Q.L₁ x) (gline hπ hB Q (Q.L₁ x))
    rw [lineBaseChange_gline]

theorem main (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π)) (Q : DrinfeldDatum (K := K) π B) :
    ∃ d : DeligneDatum (K := K) π B, Q.IsQuadrupleOf d :=
  ⟨dglob hπ hB Q, isQuadrupleOf_dglob hπ hB Q⟩

end Main

end P2mKcQuadrupleB
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf.P2mKcQuadrupleB"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf.P2mKcQuadrupleB"

open P2mKcQuadrupleB in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) : ∃ d : DeligneDatum (K := K) π B, Q.IsQuadrupleOf d :=
  main hπ hB Q

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isQuadrupleOf (solution)
