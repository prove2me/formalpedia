-- Prove2me | solution 1 for Formalism.L2.Th1.H.UnitaryGauss_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:04:48.500803+00:00
-- url     : https://prove2.me/submissions/1a86415c-c322-470b-a26f-ec5430b283f6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_phiQ_mk
import Theorems.Thm_Formalism_L2_Th1_H_ud_isQuadFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (hG : GaussEighth) : UnitaryGauss := by
  intro V _ _ H Λ α δ Ae h S hS
  obtain ⟨hSΛ, hSinj, hSsurj⟩ := hS
  let f : S → Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ :=
    fun x => QuotientAddGroup.mk (⟨x.1, hSΛ x.1 x.2⟩ : Λ)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hSinj a.1 a.2 b.1 b.2
      have h1 : -(⟨a.1, hSΛ a.1 a.2⟩ : Λ) + ⟨b.1, hSΛ b.1 b.2⟩ ∈ (latA Λ δ Ae).addSubgroupOf Λ :=
        QuotientAddGroup.eq.mp hab
      have h2 := (latA Λ δ Ae).neg_mem (AddSubgroup.mem_addSubgroupOf.mp h1)
      have e : (a.1 : V) - b.1 = -(((-(⟨a.1, hSΛ a.1 a.2⟩ : Λ) + ⟨b.1, hSΛ b.1 b.2⟩ : Λ)) : V) := by
        push_cast
        abel
      rw [e]
      exact h2
    · intro q
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨x, hx, hyx⟩ := hSsurj y.1 y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply QuotientAddGroup.eq.mpr
      apply AddSubgroup.mem_addSubgroupOf.mpr
      have e : ((-(⟨x, hSΛ x hx⟩ : Λ) + y : Λ) : V) = (y : V) - x := by
        push_cast
        abel
      have h3 : ((-(⟨x, hSΛ x hx⟩ : Λ) + y : Λ) : V) ∈ latA Λ δ Ae := by
        rw [e]
        exact hyx
      exact h3
  letI : Fintype (Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) := Fintype.ofBijective f hf
  have hsum : ∑ x ∈ S, phiC H α Ae x = ∑ q : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ, phiQ H Λ α δ Ae q := by
    rw [← Finset.sum_coe_sort S]
    exact Fintype.sum_bijective f hf _ _ (fun x => (phiQ_mk h (⟨x.1, hSΛ x.1 x.2⟩ : Λ)).symm)
  have hcard : Fintype.card (Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) = S.card := by
    rw [← Fintype.card_coe S]
    exact (Fintype.card_of_bijective hf).symm
  have hq := hG (Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) (phiQ H Λ α δ Ae) (bQ H Λ δ Ae) (ud_isQuadFn h)
  have hpos : (0 : ℝ) < S.card := by
    obtain ⟨x, hx, _⟩ := hSsurj 0 Λ.zero_mem
    exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
  have hs : ((Real.sqrt S.card : ℝ) : ℂ) ^ 8 = (S.card : ℂ) ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hpos.le]
    first | norm_num | (push_cast; ring) | simp
  unfold gaussC
  rw [mul_pow, hsum, hq, hcard, inv_pow, hs]
  have hne : (S.card : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hpos.ne')
  exact inv_mul_cancel₀ hne
end Formalism.L2.Th1.H
