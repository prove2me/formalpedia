-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.nk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:58.829049+00:00
-- url     : https://prove2.me/submissions/557eea60-d50f-4ecb-9b2a-45a89ee9bc34

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_comap_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_congrP_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
private theorem exists_mem_ideal_form_eq_of_mem_ideal_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (I : Ideal (𝓞 K)) (w x : ↥L)
    (hx : x ∈ (I • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ I, h (w : V) (x : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (w : V) w.2 (m : V) m.2)
    refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by rw [Submodule.coe_add, map_add, hu', hv', map_add]⟩
private theorem exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (w x : ↥L)
    (hx : x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ extP K 𝔭 ^ k, h (x : V) (w : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (m : V) m.2 (w : V) w.2)
    refine ⟨conjO K r * o, Ideal.mul_mem_right _ _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k r hr), ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ho]
    congr 1 <;> simp [conjO]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by
      rw [Submodule.coe_add, map_add, LinearMap.add_apply, hu', hv', map_add]⟩
section Frame
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)
variable {z g}
end Frame
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F)
    (y₀ : ↥L) (n₀ : 𝓞 F) (h₀ : h (y₀ : V) (y₀ : V) = algebraMap F K (n₀ : F)) :
    (∃ y : ↥L, (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
        Submodule.Quotient.mk y₀ ∧ CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F))) ↔
      n₀ - n ∈ 𝔭 ^ k := by
  have hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o := fun y =>
    let ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)
    ⟨o, ho.symm⟩
  have hn : ∀ m : 𝓞 F, algebraMap F K (m : F) = algebraMap (𝓞 K) K (ι m) := fun m => rfl
  obtain ⟨o₀, ho₀⟩ := hint y₀
  have ho₀' : o₀ = ι n₀ := IsFractionRing.injective (𝓞 K) K (by rw [← ho₀, h₀, hn])
  have hcong : ∀ y : ↥L, (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk y₀ → ∀ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o →
      Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ := by
    intro y hy o ho
    rw [Submodule.Quotient.eq] at hy
    obtain ⟨u1, hu1, he1⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy
    obtain ⟨u2, hu2, he2⟩ := exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy
    obtain ⟨u3, hu3, he3⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy
    have hyx : y = y₀ + (y - y₀) := by abel
    have hsum : o = o₀ + u1 + u2 + u3 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [← ho, hyx]
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
      rw [he1, he2, he3, ← ho₀]
      ring
    rw [Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]
    exact Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3
  have key : ∀ o : 𝓞 K, Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ →
      (CongrP 𝔭 k (algebraMap (𝓞 K) K o) (algebraMap F K (n : F)) ↔ n₀ - n ∈ 𝔭 ^ k) := by
    intro o hoo
    rw [hn, integralBasisSpans.congrP_int h𝔭, hoo, ho₀', Ideal.Quotient.eq, ← map_sub,
      ← MeanB.comap_extP_pow (K := K) 𝔭 k, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, hc⟩
    obtain ⟨o, ho⟩ := hint y
    rw [ho] at hc
    exact (key o (hcong y hy o ho)).mp hc
  · intro hmem
    refine ⟨y₀, rfl, ?_⟩
    rw [ho₀]
    exact (key o₀ rfl).mpr hmem
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
