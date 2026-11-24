-- Prove2me | solution 1 for Formalism.L2.Th1.H.degenerateGaussSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:29:06.166421+00:00
-- url     : https://prove2.me/submissions/754247fd-f488-4519-96e6-e918f5ceef6e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn0_symm
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn0_phi_rad
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_symm
import Theorems.Thm_Formalism_L2_Th1_H_gaussSumEighthPower


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
open SemicharacterExponentialLemmas
namespace Formalism.L2.Th1.H
theorem _root_.solution : GaussDegenerate := by
  classical
  intro M _ _ φ b h hS
  set R : AddSubgroup M := h.rad with hR
  have hφR : ∀ x, ∀ r ∈ R, φ (x + r) = φ x := by
    intro x r hr
    rw [h.add, h.symm, hr x, h.phi_rad hS hr, mul_one, mul_one]
  have hbR : ∀ x y, ∀ r ∈ R, b (x + r) y = b x y := by
    intro x y r hr
    rw [h.left, hr y, mul_one]
  have : Fintype (M ⧸ R) := Fintype.ofFinite _
  have : Fintype R := Fintype.ofFinite _
  let φ' : M ⧸ R → ℂ := fun q => φ q.out
  let b' : M ⧸ R → M ⧸ R → ℂ := fun q q' => b q.out q'.out
  have hφ' : ∀ x : M, φ' (x : M ⧸ R) = φ x := by
    intro x
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R x
    change φ (Quotient.out (x : M ⧸ R)) = φ x
    rw [hr, hφR x r r.2]
  have hb' : ∀ x y : M, b' (x : M ⧸ R) (y : M ⧸ R) = b x y := by
    intro x y
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R x
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_out_eq_add R y
    change b (Quotient.out (x : M ⧸ R)) (Quotient.out (y : M ⧸ R)) = b x y
    rw [hr, hs, hbR x _ r r.2, h.symm, hbR y _ s s.2, h.symm]
  have hQ : IsQuadFn φ' b' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [← QuotientAddGroup.mk_add, hφ', hφ', hφ', hb', h.add]
    · intro p q s
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective s
      rw [← QuotientAddGroup.mk_add, hb', hb', hb', h.left]
    · intro k p
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      rw [← QuotientAddGroup.mk_nsmul, hφ', hφ', h.sq]
    · intro p
      exact h.ne _
    · intro p hp
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      rw [QuotientAddGroup.eq_zero_iff]
      intro y
      rw [← hb']
      exact hp _
  have hG := gaussSumEighthPower (M ⧸ R) φ' b' hQ
  have hbij : Function.Bijective (fun p : (M ⧸ R) × R => (p.1.out + (p.2 : M) : M)) := by
    constructor
    · rintro ⟨q, r⟩ ⟨q', r'⟩ hqr
      simp only at hqr
      have hq : q = q' := by
        have h1 : ((q.out + (r : M) : M) : M ⧸ R) = ((q'.out + (r' : M) : M) : M ⧸ R) := by rw [hqr]
        rw [QuotientAddGroup.mk_add_of_mem _ r.2, QuotientAddGroup.mk_add_of_mem _ r'.2,
          QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h1
        exact h1
      subst hq
      have hr : (r : M) = r' := add_left_cancel hqr
      rw [Subtype.ext hr]
    · intro x
      obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R x
      refine ⟨((x : M ⧸ R), -r), ?_⟩
      simp only [hr, AddSubgroup.coe_neg]
      abel
  have hsum : ∑ x, φ x = (Fintype.card R : ℂ) * ∑ q, φ' q := by
    rw [← hbij.sum_comp φ, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : ∀ r : R, φ (q.out + (r : M)) = φ' q := fun r => hφR _ r r.2
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨(Fintype.card R : ℝ) ^ 8 * (Fintype.card (M ⧸ R) : ℝ) ^ 4, ?_, ?_⟩
  · have h1 : 0 < Fintype.card R := Fintype.card_pos
    have h2 : 0 < Fintype.card (M ⧸ R) := Fintype.card_pos
    positivity
  · rw [hsum, mul_pow, hG]
    push_cast
    ring
end Formalism.L2.Th1.H
