-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_image_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:04.424784+00:00
-- url     : https://prove2.me/submissions/8133cedd-adae-46b5-8cec-dd70d83f4ad8

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_map_mulLeft_den_span_image_eq_map_num

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) *
        (Ideal.absNorm J.num : ℚ) ^ Module.finrank E F =
      |Algebra.norm ℚ s| * |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| ^ Module.finrank E F := by
  set A := Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E)) with hA
  set c : 𝓞 F := algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) with hcdef
  have hc : (c : F) = algebraMap E F ((J.den : 𝓞 E) : E) := rfl
  have hden0 : ((J.den : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero J.den
    exact_mod_cast this
  have hc0 : (c : F) ≠ 0 := by rw [hc]; exact (map_ne_zero _).mpr hden0
  set f := LinearMap.mulLeft (𝓞 F) (c : F) with hf
  have hfinj : Function.Injective f := fun x y h => mul_left_cancel₀ hc0 h
  set I2 : Ideal (𝓞 F) := J.num.map (algebraMap (𝓞 E) (𝓞 F)) with hI2
  have hmapA : Submodule.map f A = Submodule.map (Algebra.linearMap (𝓞 F) F) I2 := map_mulLeft_den_span_image_eq_map_num J
  have hcs : (c : F) * s ∈ Submodule.map (Algebra.linearMap (𝓞 F) F) I2 := by
    rw [← hmapA]; exact ⟨s, hs, rfl⟩
  obtain ⟨t, ht, hts⟩ := hcs
  simp only [Algebra.linearMap_apply] at hts
  have hmaps : Submodule.map f (Submodule.span (𝓞 F) {s}) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (Ideal.span {t}) := by
    rw [Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    simp only [Algebra.linearMap_apply, hts]
    rfl
  have hginj : Function.Injective (Algebra.linearMap (𝓞 F) F) := RingOfIntegers.coe_injective
  have hrel : (((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf A.toAddSubgroup).index) =
      (Ideal.span {t}).toAddSubgroup.relIndex I2.toAddSubgroup := by
    change (Submodule.span (𝓞 F) {s}).toAddSubgroup.relIndex A.toAddSubgroup = _
    have h1 := AddSubgroup.relIndex_map_map_of_injective (f := (f : F →+ F))
      (Submodule.span (𝓞 F) {s}).toAddSubgroup A.toAddSubgroup hfinj
    rw [← h1, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hmaps, hmapA,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective
      (f := ((Algebra.linearMap (𝓞 F) F) : 𝓞 F →+ F)) _ _ hginj
  have hle : (Ideal.span {t}).toAddSubgroup ≤ I2.toAddSubgroup := by
    intro x hx
    exact (Ideal.span_singleton_le_iff_mem _).mpr ht hx
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, Ideal.absNorm_span_singleton, hI2,
    Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 F) F] at hmul
  rw [hrel]
  have hnt : ((Algebra.norm ℤ t : ℤ) : ℚ) = Algebra.norm ℚ s * (Algebra.norm ℚ ((J.den : 𝓞 E) : E)) ^ Module.finrank E F := by
    rw [Algebra.coe_norm_int, show ((t : F)) = (c : F) * s from hts, map_mul, hc, mul_comm]
    congr 1
    rw [← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow]
  have hq := congrArg (fun n : ℕ => (n : ℚ)) hmul
  simp only [Nat.cast_mul, Nat.cast_pow] at hq
  rw [hq, Nat.cast_natAbs, Int.cast_abs, hnt, abs_mul, abs_pow]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
