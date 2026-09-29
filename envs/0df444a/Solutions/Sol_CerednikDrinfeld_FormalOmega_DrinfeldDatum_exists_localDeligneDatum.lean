-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_localDeligneDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ad9d9062-0302-55db-a125-e342ce3ab30b

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleStalk

section Local

variable {B : Type} [CommRing B] (x : PrimeSpectrum B)
variable {T : Type} [AddCommGroup T] [Module B T]

theorem mem_ideal_smul_top_of_mem_maximalIdeal_smul_top (y : stalk B x T)
    (hy : y ∈ (IsLocalRing.maximalIdeal (locRing B x) • ⊤ : Submodule (locRing B x) (stalk B x T))) :
    y ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T)) := by
  refine Submodule.smul_induction_on (p := fun y => y ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T))) hy ?_ ?_
  · intro r hr t _
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.asIdeal.primeCompl r
    have hb : b ∈ x.asIdeal := (IsLocalization.AtPrime.mk'_mem_maximal_iff (locRing B x) x.asIdeal b s).mp hr
    have e : IsLocalization.mk' (locRing B x) b s • t =
        b • (IsLocalization.mk' (locRing B x) (1 : B) s • t) := by
      rw [← smul_assoc, Algebra.smul_def b (IsLocalization.mk' (locRing B x) (1 : B) s), ← IsLocalization.mk'_eq_mul_mk'_one]
    show IsLocalization.mk' (locRing B x) b s • t ∈ _
    rw [e]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

theorem mem_ideal_smul_top_of_mem_prime_smul_top (𝔮 : Ideal (locRing B x)) [𝔮.IsPrime] (y : stalk B x T)
    (hy : y ∈ (𝔮 • ⊤ : Submodule (locRing B x) (stalk B x T))) : y ∈ (x.asIdeal • ⊤ : Submodule B (stalk B x T)) :=
  mem_ideal_smul_top_of_mem_maximalIdeal_smul_top x y
    (Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hy)

theorem map_mem_smul_top_of_mem_sup {V W : Type} [AddCommGroup V] [Module (locRing B x) V] [AddCommGroup W]
    [Module (locRing B x) W] (f : V →ₗ[locRing B x] W) (𝔮 : Ideal (locRing B x)) (w : V)
    (hw : w ∈ LinearMap.ker f ⊔ (𝔮 • ⊤ : Submodule (locRing B x) V)) : f w ∈ (𝔮 • ⊤ : Submodule (locRing B x) W) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add, LinearMap.mem_ker.mp ha, zero_add]
  have : f b ∈ (𝔮 • ⊤ : Submodule (locRing B x) V).map f := Submodule.mem_map_of_mem hb
  rw [Submodule.map_smul'', Submodule.map_top] at this
  exact Submodule.smul_mono le_rfl le_top this

end Local

section Quadruple

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem invertible_quot_ker_u₀ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    Module.Invertible (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) (Q.L₀ x) ⧸ LinearMap.ker (Q.u₀ x)) :=
  Module.Invertible.congr (LinearMap.quotKerEquivOfSurjective (Q.u₀ x) (Q.u₀_surjective x)).symm

theorem invertible_quot_ker_u₁ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    Module.Invertible (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) (Q.L₁ x) ⧸ LinearMap.ker (Q.u₁ x)) :=
  Module.Invertible.congr (LinearMap.quotKerEquivOfSurjective (Q.u₁ x) (Q.u₁_surjective x)).symm

theorem map_incl_ker_u₀_le (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    (LinearMap.ker (Q.u₀ x)).map (inclBaseChange (locRing B x) (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x)) ≤
      LinearMap.ker (Q.u₁ x) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hs
  rw [LinearMap.mem_ker, Q.u₁_incl x s, hs, map_zero]

theorem map_smul_ker_u₁_le (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    (LinearMap.ker (Q.u₁ x)).map ((smulInto π (Q.smul_le x)).baseChange (locRing B x) :
      latticeBaseChange 𝒪 K (locRing B x) (Q.L₁ x) →ₗ[locRing B x] latticeBaseChange 𝒪 K (locRing B x) (Q.L₀ x)) ≤
      LinearMap.ker (Q.u₀ x) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hs
  rw [LinearMap.mem_ker, Q.u₀_smul x s, hs, map_zero]

theorem clause₁ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (𝔮 : Ideal (locRing B x)) (h𝔮 : 𝔮.IsPrime)
    (v : ↥(Q.L₁ x).1) (hv : (v : Fin 2 → K) ∉ (Q.L₀ x).1) :
    (1 : locRing B x) ⊗ₜ[𝒪] v ∉ LinearMap.ker (Q.u₁ x) ⊔
      (𝔮 • ⊤ : Submodule (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) (Q.L₁ x))) := by
  intro hmem
  apply hv
  apply Q.injective₁ x v
  have h1 := map_mem_smul_top_of_mem_sup x (Q.u₁ x) 𝔮 _ hmem
  exact Submodule.mem_sup_right (mem_ideal_smul_top_of_mem_prime_smul_top x 𝔮 _ h1)

theorem clause₂ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (𝔮 : Ideal (locRing B x)) (h𝔮 : 𝔮.IsPrime)
    (v' : ↥(Q.L₀ x).1) (hv' : ¬ ∃ w : ↥(Q.L₁ x).1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) :
    (1 : locRing B x) ⊗ₜ[𝒪] v' ∉ LinearMap.ker (Q.u₀ x) ⊔
      (𝔮 • ⊤ : Submodule (locRing B x) (latticeBaseChange 𝒪 K (locRing B x) (Q.L₀ x))) := by
  intro hmem
  apply hv'
  have h1 := map_mem_smul_top_of_mem_sup x (Q.u₀ x) 𝔮 _ hmem
  obtain ⟨w, hw, hw'⟩ := Q.injective₀ x v' (Submodule.mem_sup_right (mem_ideal_smul_top_of_mem_prime_smul_top x 𝔮 _ h1))
  exact ⟨⟨w, hw⟩, hw'⟩

theorem exists_local (hπ : Irreducible π) (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ dₓ : DeligneDatum (K := K) π (locRing B x),
      LinearMap.ker (Q.u₀ x) = dₓ.line (Q.L₀ x) ∧ LinearMap.ker (Q.u₁ x) = dₓ.line (Q.L₁ x) ∧
      dₓ.InEdgeChart π (Q.L₀ x) (Q.L₁ x) := by
  haveI := invertible_quot_ker_u₀ Q x
  haveI := invertible_quot_ker_u₁ Q x
  obtain ⟨d, hM, hM', hchart⟩ :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq (K := K) hπ (B := locRing B x)
      (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x) (Q.smul_le x) (LinearMap.ker (Q.u₁ x)) (LinearMap.ker (Q.u₀ x))
      (map_incl_ker_u₀_le Q x) (map_smul_ker_u₁_le Q x) (fun 𝔮 h𝔮 v hv => clause₁ Q x 𝔮 h𝔮 v hv)
      (fun 𝔮 h𝔮 v' hv' => clause₂ Q x 𝔮 h𝔮 v' hv')
  exact ⟨d, hM'.symm, hM.symm, hchart⟩

end Quadruple

end P2mKcQuadrupleStalk

end

open P2mKcQuadrupleStalk in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) :
    ∃ dₓ : DeligneDatum (K := K) π (locRing B x),
      LinearMap.ker (Q.u₀ x) = dₓ.line (Q.L₀ x) ∧ LinearMap.ker (Q.u₁ x) = dₓ.line (Q.L₁ x) ∧
      dₓ.InEdgeChart π (Q.L₀ x) (Q.L₁ x) :=
  exists_local hπ Q x

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_localDeligneDatum (solution)
