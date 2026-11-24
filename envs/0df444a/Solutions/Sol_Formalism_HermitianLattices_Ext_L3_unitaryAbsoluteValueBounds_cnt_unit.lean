-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cnt_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:38.894803+00:00
-- url     : https://prove2.me/submissions/b6a5c168-ef43-4ce8-8c44-8b211ffd932b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_map_comap_eq_of_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_extP_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_one_lt_q
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_comap_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_conjIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_eq_eulerFac_inert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_eq_eulerFac_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_eq_normRepCount
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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    (cnt hF 𝔭 k M (ι n) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * M - 1) * k) *
      (1 - etaF K F 𝔭 ^ M * (Ideal.absNorm 𝔭 : ℝ) ^ (-(M : ℤ))) := by
  classical
  have hinj : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h2 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx, map_zero]
    rw [map_eq_zero_iff _ (algebraMap F K).injective] at h2
    have : x = 0 := RingOfIntegers.ext (h2.trans (map_zero (algebraMap (𝓞 F) F)).symm)
    rw [this]
    exact 𝔭.zero_mem
  haveI := h𝔭
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hinj
  subst hPc
  have hq := one_lt_q h𝔭
  have hnP : ι n ∉ P := by rwa [Ideal.mem_comap] at hn
  have hfix : conjO K (ι n) = ι n := conjO_algebraMap_of_fixed_field hF n
  rw [cnt_eq_normRepCount]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hin := map_comap_eq_of_inert hK hF hP hc
    rw [hin, normRepCount_eq_eulerFac_inert hK hP hc M k hM hk _ hfix hnP]
    have hN := absNorm_comap_inert hK hF hP hc
    have hpr : ((P.comap ι).map ι).IsPrime := by
      have h3 := hin
      unfold extP at h3
      rw [h3]
      exact hP.isPrime
    have heta : etaF K F (P.comap ι) = -1 := by
      unfold etaF
      rw [if_pos hpr]
    unfold Formalism.HermitianLatticesTheory.eulerFac
    rw [if_pos hc, inv_inv, heta, ← hN]
    push_cast
    rw [Real.sqrt_sq (by positivity)]
  · have hsplit := extP_split hK hF hP hc
    rw [hsplit, normRepCount_eq_eulerFac_split hK hP hc M k hM hk _ hfix hnP]
    have hN := absNorm_comap_split hK hF hP hc
    have hcc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
      ext r
      rw [mem_conjIdeal_iff', mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
    have hc2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠
        Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      rw [hcc]
      exact Ne.symm hc
    have hNc := absNorm_conjIdeal hK P
    have hpr : ¬ ((P.comap ι).map ι).IsPrime := by
      intro hpr
      have h3 := hsplit
      unfold extP at h3
      rw [h3] at hpr
      rcases (hpr.mul_le).mp le_rfl with h | h
      · have h1 : P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := h.trans Ideal.mul_le_right
        apply hc
        refine le_antisymm ?_ h1
        intro r hr
        rw [mem_conjIdeal_iff'] at hr
        have h4 := h1 hr
        rwa [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives] at h4
      · have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P := h.trans Ideal.mul_le_left
        apply hc
        refine le_antisymm h1 ?_
        intro r hr
        rw [mem_conjIdeal_iff']
        apply h1
        rw [mem_conjIdeal_iff', conjO_conjO_unimodular_class_representatives]
        exact hr
    have heta : etaF K F (P.comap ι) = 1 := by
      unfold etaF
      rw [if_neg hpr]
    have hx : 0 < 1 - (Ideal.absNorm (P.comap ι) : ℝ) ^ (-(M : ℤ)) := by
      have hlt : (Ideal.absNorm (P.comap ι) : ℝ) ^ (-(M : ℤ)) < 1 := by
        rw [zpow_neg, zpow_natCast]
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
      linarith
    have hh : (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 := by norm_num
    unfold Formalism.HermitianLatticesTheory.eulerFac
    rw [if_neg hc, if_neg hc2, hNc, ← hN, heta, ← Real.rpow_add hx, hh, Real.rpow_neg_one, inv_inv,
      one_pow, one_mul]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
