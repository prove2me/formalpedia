-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormOneGroup.cond_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:50.6789+00:00
-- url     : https://prove2.me/submissions/47332268-32d8-4039-8001-1b6f9fb962ab

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_conjO_mem_extP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_map_mem_extP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormOneGroup
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup
theorem _root_.solution (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hvk : v ≤ k) {b : 𝓞 K}
    (hc : conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v)) (x y x' y' : ↥L)
    (hx : x' - b • x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (hy : y' - b • y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  have e3 : ∀ c : 𝓞 K, algebraMap (𝓞 K) K (conjO K c) = star (algebraMap (𝓞 K) K c) :=
    fun _ => rfl
  have eφ : ∀ a : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) :=
    fun _ => rfl
  have hψ : ∀ a c : 𝓞 F, algebraMap F K ((a * c : 𝓞 F) : F) =
      algebraMap F K (a : F) * algebraMap F K (c : F) := fun a c => by
    rw [show ((a * c : 𝓞 F) : F) = (a : F) * (c : F) from rfl, map_mul]
  have hfix : ∀ a : 𝓞 F, star (algebraMap F K (a : F)) = algebraMap F K (a : F) :=
    fun a => (hF _).mpr ⟨_, rfl⟩
  have hsmul1 : ∀ (c : 𝓞 K) (u w : V), h (c • u) w = star (algebraMap (𝓞 K) K c) * h u w :=
    fun c u w => by rw [← algebraMap_smul K c u, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hsmul2 : ∀ (c : 𝓞 K) (u w : V), h u (c • w) = algebraMap (𝓞 K) K c * h u w :=
    fun c u w => by rw [← algebraMap_smul K c w, map_smul, smul_eq_mul]
  have hA : ∀ w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L), ∀ u : ↥L,
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (w : V) (u : V)) ∧
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V)) := by
    intro w hw u
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro c hc m _
      obtain ⟨r1, hr1⟩ := Submodule.mem_one.mp (hLi m m.2 u u.2)
      obtain ⟨r2, hr2⟩ := Submodule.mem_one.mp (hLi u u.2 m m.2)
      refine ⟨⟨conjO K c * r1, Ideal.mul_mem_right _ _ (conjO_mem_extP hF 𝔭 k hc), ?_⟩,
        ⟨c * r2, Ideal.mul_mem_right _ _ hc, ?_⟩⟩
      · rw [map_mul, e3, hr1, Submodule.coe_smul, hsmul1]
      · rw [map_mul, hr2, Submodule.coe_smul, hsmul2]
    · intro w1 w2 h1 h2
      obtain ⟨⟨z1, hz1, ez1⟩, ⟨z1', hz1', ez1'⟩⟩ := h1
      obtain ⟨⟨z2, hz2, ez2⟩, ⟨z2', hz2', ez2'⟩⟩ := h2
      refine ⟨⟨z1 + z2, add_mem hz1 hz2, ?_⟩, ⟨z1' + z2', add_mem hz1' hz2', ?_⟩⟩
      · rw [map_add, ez1, ez2, Submodule.coe_add, map_add, LinearMap.add_apply]
      · rw [map_add, ez1', ez2', Submodule.coe_add, map_add]
  have hB : ∀ u w : ↥L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ r ∈ extP K 𝔭 ^ v,
      algebraMap (𝓞 K) K r = algebraMap F K (t : F) * h (u : V) (w : V) := by
    intro u w
    obtain ⟨t1, ht1, a1, ha1⟩ := he.2.2 u u.2
    obtain ⟨t2, ht2, a2, ha2⟩ := he.2.2 w w.2
    refine ⟨t1 * t2, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht1 ht2,
      conjO K a1 * a2 * algebraMap (𝓞 F) (𝓞 K) n, Ideal.mul_mem_left _ _ (map_mem_extP hv), ?_⟩
    have h1 := congrArg₂ (fun p q => h p q) ha1 ha2
    simp only [hsmul1, hsmul2, hn, eφ, hfix] at h1
    rw [map_mul, map_mul, e3, eφ, hψ]
    linear_combination -h1
  obtain ⟨⟨z1, hz1, ez1⟩, -⟩ := hA (x' - b • x) hx y'
  obtain ⟨-, ⟨z2, hz2, ez2⟩⟩ := hA (y' - b • y) hy (b • x)
  obtain ⟨t, ht, r, hr, er⟩ := hB x y
  refine ⟨t, ht, algebraMap (𝓞 F) (𝓞 K) t * (z1 + z2) + (conjO K b * b - 1) * r, ?_, ?_⟩
  · refine add_mem (Ideal.mul_mem_left _ _ (add_mem hz1 hz2)) ?_
    have hpow : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - v) * extP K 𝔭 ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvk]
    rw [hpow]
    exact Ideal.mul_mem_mul hc hr
  · rw [map_add, map_mul, map_mul, map_add, ez1, ez2, er, map_sub, map_mul, map_one, e3, eφ]
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, LinearMap.sub_apply, hsmul1, hsmul2]
    ring
end Formalism.HermitianLattices.Ext.L3.NormOneGroup
