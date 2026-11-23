-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:21.280889+00:00
-- url     : https://prove2.me/submissions/26488152-cdd6-457f-8208-67dd996c8877

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ θ : 𝓞 K, Ideal.span {θ - conjO K θ} ⊔ extP K 𝔭 = ⊤ := by
  have hne : extP K 𝔭 ≠ ⊤ := by
    intro h
    have h1 : ι 1 ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one, h]
      exact Submodule.mem_top
    rw [mem_pow_iff, pow_one] at h1
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hK.2.2 P hPmax
  have htc : t = conjO K θ := by
    apply RingOfIntegers.ext
    rw [coe_conjO_eq_star_coe]
    exact ht
  subst htc
  refine ⟨θ, ?_⟩
  have hδc : ((θ - conjO K θ : 𝓞 K) : K) = (θ : K) - star (θ : K) := by
    rw [← coe_conjO_eq_star_coe]
    rfl
  have hfix : star (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) =
      (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) := by
    have e : (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) =
        ((θ - conjO K θ : 𝓞 K) : K) * ((θ - conjO K θ : 𝓞 K) : K) := rfl
    rw [e, hδc, star_mul, star_sub, star_star]
    ring
  obtain ⟨r, hr⟩ := exists_iota_eq_of_star_coe_eq hF _ hfix
  have hr𝔭 : r ∉ 𝔭 := by
    intro hr'
    have h1 : ι r ∈ P := hPle (Ideal.mem_map_of_mem _ hr')
    rw [hr] at h1
    exact hθt ((hPmax.isPrime.mem_or_mem h1).elim id id)
  have h1 : Ideal.span {r} ⊔ 𝔭 = ⊤ := by
    refine h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right (fun h => hr𝔭 ?_))
    rw [h]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self r)
  have h2 := congrArg (Ideal.map ι) h1
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top] at h2
  rw [hr] at h2
  refine eq_top_iff.mpr ?_
  rw [← h2]
  exact sup_le_sup_right
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)) _
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
