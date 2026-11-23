-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_frac_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:49.539263+00:00
-- url     : https://prove2.me/submissions/2111ad42-6fc3-49d5-b117-e4049b950638

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_not_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locR_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
private theorem exists_int_preimage_of_star_fixed (hF : IsFixF K F) (x : 𝓞 K)
    (hx : star (algebraMap (𝓞 K) K x) = algebraMap (𝓞 K) K x) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) t = x := by
  obtain ⟨f, hf⟩ := (hF _).1 hx
  have h1 : IsIntegral ℤ (algebraMap F K f) := by
    rw [hf]
    exact NumberField.RingOfIntegers.isIntegral_coe x
  have hint : IsIntegral ℤ f :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F K) (algebraMap F K).injective).mp h1
  refine ⟨⟨f, hint⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  exact hf
end Formalism.HermitianLattices.Ext.L3.U0
end
end

set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsPrime) {a : K}
    (ha : a ∈ locRing P) (hfix : star a = a) :
    ∃ t s : 𝓞 F, s ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ a = toK K t / toK K s := by
  haveI := hP
  obtain ⟨r, s, hs, rfl⟩ := (WA.mem_locR_iff hP _).1 ha
  have hs1 : s ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P s hs
  have hs2 : conjO K s ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hs)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := WA.algebraMap_ne_zero_of_mem_hcompl hP hs
  have hs'K : algebraMap (𝓞 K) K (conjO K s) ≠ 0 :=
    WA.algebraMap_ne_zero_of_mem_hcompl hP (WA.conjO_mem_hcompl hs)
  have hconj : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s) := rfl
  have hNfix : star (algebraMap (𝓞 K) K (s * conjO K s)) = algebraMap (𝓞 K) K (s * conjO K s) := by
    rw [map_mul, hconj, star_mul, star_star, mul_comm]
  have hMfix : star (algebraMap (𝓞 K) K (r * conjO K s)) = algebraMap (𝓞 K) K (r * conjO K s) := by
    have e : algebraMap (𝓞 K) K (r * conjO K s) =
        (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) * algebraMap (𝓞 K) K (s * conjO K s) := by
      rw [map_mul, map_mul]
      field_simp
    rw [e, star_mul', hfix, hNfix]
  obtain ⟨tN, htN⟩ := exists_int_preimage_of_star_fixed hF _ hNfix
  obtain ⟨tM, htM⟩ := exists_int_preimage_of_star_fixed hF _ hMfix
  refine ⟨tM, tN, ?_, ?_⟩
  · intro h
    rw [Ideal.mem_comap, htN] at h
    exact (hP.mem_or_mem h).elim hs1 hs2
  · unfold toK
    rw [htM, htN, map_mul, map_mul, mul_div_mul_right _ _ hs'K]
end Formalism.HermitianLattices.Ext.L3.U0
