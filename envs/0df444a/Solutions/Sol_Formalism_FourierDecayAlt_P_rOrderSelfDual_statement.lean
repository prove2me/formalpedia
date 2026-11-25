-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rOrderSelfDual_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:20.72404+00:00
-- url     : https://prove2.me/submissions/1fbf763e-efc8-44f5-a79a-c70b3b966caa

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_mem_ROrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.OrderChainWeights
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.ROrderSelfDual := by
  intro o _ _ _ k0 _ _ _ ϖ hϖ a₁ a₂
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  have hϖ0 : algebraMap o k0 ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact hϖ.ne_zero
  have hmax : IsLocalRing.maximalIdeal o = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hres0 : IsLocalRing.residue o ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  constructor
  · intro h
    obtain ⟨y1, hy1⟩ := h ⟨(ϖ, 0), (mem_ROrd _).mpr (by simp [hres0])⟩
    obtain ⟨y2, hy2⟩ := h ⟨(0, ϖ), (mem_ROrd _).mpr (by simp [hres0])⟩
    obtain ⟨y3, hy3⟩ := h ⟨(1, 1), (mem_ROrd _).mpr rfl⟩
    have e1 : algebraMap o k0 y1 = a₁ := by
      rw [hy1]
      dsimp only
      rw [map_zero, mul_zero, sub_zero]
      field_simp
    have e2 : algebraMap o k0 y2 = -a₂ := by
      rw [hy2]
      dsimp only
      rw [map_zero, mul_zero, zero_sub]
      field_simp
    have e3 : algebraMap o k0 y3 = (a₁ - a₂) / algebraMap o k0 ϖ := by
      rw [hy3]
      dsimp only
      rw [map_one, mul_one, mul_one]
    have hd : y1 + y2 = ϖ * y3 := by
      apply hinj
      rw [map_add, map_mul, e1, e2, e3]
      field_simp
      try ring
    refine ⟨⟨(y1, -y2), (mem_ROrd _).mpr ?_⟩, e1, ?_⟩
    · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]
      exact ⟨y3, by rw [sub_neg_eq_add, hd]⟩
    · show algebraMap o k0 (-y2) = a₂
      rw [map_neg, e2, neg_neg]
  · rintro ⟨x, hx1, hx2⟩ b
    have hm := (mem_ROrd (x : o × o)).mp x.2
    have hb := (mem_ROrd (b : o × o)).mp b.2
    have hmem : (x : o × o).1 * (b : o × o).1 - (x : o × o).2 * (b : o × o).2 ∈ Ideal.span {ϖ} := by
      rw [← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, map_mul, hm, hb, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨y, ?_⟩
    rw [← hx1, ← hx2, eq_div_iff hϖ0, ← map_mul, ← map_mul, ← map_mul, ← map_sub, hy]
end Formalism.FourierDecayAlt.P
