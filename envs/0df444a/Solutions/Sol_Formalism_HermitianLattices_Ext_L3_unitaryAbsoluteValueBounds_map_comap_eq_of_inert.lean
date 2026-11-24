-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.map_comap_eq_of_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:14.932285+00:00
-- url     : https://prove2.me/submissions/6a3d329b-93a2-4a73-b133-a24aaaa0cb11

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
private lemma coe_conjO_eq_star (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl
private lemma conjO_conjO_unimodular_class_representatives (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star, coe_conjO_eq_star, star_star]
private lemma mem_conjIdeal_iff' (P : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ conjO K r ∈ P := by
  have hS : {r : 𝓞 K | ∃ s ∈ P, algebraMap (𝓞 K) K r = star (algebraMap (𝓞 K) K s)} =
      ((P.comap (conjO K) : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    ext r
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_comap]
    constructor
    · rintro ⟨s, hs, h⟩
      have : conjO K r = s := by
        apply RingOfIntegers.ext
        rw [coe_conjO_eq_star]
        change star (algebraMap (𝓞 K) K r) = algebraMap (𝓞 K) K s
        rw [h, star_star]
      rwa [this]
    · intro h
      refine ⟨conjO K r, h, ?_⟩
      change (r : K) = star ((conjO K r : 𝓞 K) : K)
      rw [coe_conjO_eq_star, star_star]
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  rw [hS, Ideal.span_eq, Ideal.mem_comap]
private lemma conjO_algebraMap_of_fixed_field (hF : IsFixF K F) (x : 𝓞 F) :
    conjO K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star]
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (algebraMap (𝓞 F) F x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x)) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x)
  rw [h1]
  exact (hF _).mpr ⟨_, rfl⟩
private lemma exists_algebraMap_eq_of_conjO_eq (hF : IsFixF K F) (y : 𝓞 K) (hy : conjO K y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) a = y := by
  have h1 : star (y : K) = y := by rw [← coe_conjO_eq_star, hy]
  obtain ⟨f, hf⟩ := (hF _).mp h1
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (algebraMap F K).injective, hf]
    exact RingOfIntegers.isIntegral_coe y
  let a : 𝓞 F := ⟨f, (mem_integralClosure_iff ℤ F).mpr hint⟩
  refine ⟨a, RingOfIntegers.ext ?_⟩
  have h2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (algebraMap (𝓞 F) F a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = (y : K)
  rw [h2, ← hf]
  rfl
private lemma extP_comap_eq_inf_conjIdeal_of_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P ⊓ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply le_antisymm
  · unfold extP
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_comap, Ideal.mem_inf, mem_conjIdeal_iff', conjO_algebraMap_of_fixed_field hF]
    exact ⟨hx, hx⟩
  · intro x hx
    rw [Ideal.mem_inf, mem_conjIdeal_iff'] at hx
    obtain ⟨hxP, hxc⟩ := hx
    have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
    have htc : t = conjO K θ := RingOfIntegers.ext (by rw [coe_conjO_eq_star]; exact ht)
    subst htc
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_conjO_eq hF (x + conjO K x) (by rw [map_add, conjO_conjO_unimodular_class_representatives, add_comm])
    obtain ⟨b, hb⟩ := exists_algebraMap_eq_of_conjO_eq hF (conjO K θ * x + θ * conjO K x)
      (by rw [map_add, map_mul, map_mul, conjO_conjO_unimodular_class_representatives, conjO_conjO_unimodular_class_representatives, add_comm])
    obtain ⟨g, hg⟩ := exists_algebraMap_eq_of_conjO_eq hF ((θ - conjO K θ) * (θ - conjO K θ))
      (by rw [map_mul, map_sub, conjO_conjO_unimodular_class_representatives]; ring)
    have ha𝔭 : a ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, ha]; exact P.add_mem hxP hxc
    have hb𝔭 : b ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, hb]; exact P.add_mem (P.mul_mem_left _ hxP) (P.mul_mem_left _ hxc)
    have hg𝔭 : g ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      rw [Ideal.mem_comap, hg]
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h <;> exact hθ h
    obtain ⟨e, i, hi, hei⟩ := h𝔭.exists_inv hg𝔭
    have hEI : algebraMap (𝓞 F) (𝓞 K) e * ((θ - conjO K θ) * (θ - conjO K θ)) +
        algebraMap (𝓞 F) (𝓞 K) i = 1 := by
      rw [← hg, ← map_mul, ← map_add, hei, map_one]
    have hx_eq : x = algebraMap (𝓞 F) (𝓞 K) e * (θ - conjO K θ) * θ * algebraMap (𝓞 F) (𝓞 K) a -
        algebraMap (𝓞 F) (𝓞 K) e * (θ - conjO K θ) * algebraMap (𝓞 F) (𝓞 K) b +
        algebraMap (𝓞 F) (𝓞 K) i * x := by
      rw [ha, hb]
      linear_combination (-x) * hEI
    have hmem : ∀ z ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)), algebraMap (𝓞 F) (𝓞 K) z ∈
        extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) := fun z hz => Ideal.mem_map_of_mem _ hz
    rw [hx_eq]
    exact Ideal.add_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hmem _ ha𝔭))
      (Ideal.mul_mem_left _ _ (hmem _ hb𝔭))) (Ideal.mul_mem_right _ _ (hmem _ hi))
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := by
  rw [extP_comap_eq_inf_conjIdeal_of_isMaximal hK hF hP, hc, inf_idem]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
