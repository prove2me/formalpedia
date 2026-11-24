-- Prove2me | solution 1 for Formalism.L2.Th1.H.mem_lattice_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:29.731655+00:00
-- url     : https://prove2.me/submissions/effaaefb-0ed2-45c4-a038-1105ca42ca96

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_cayleyGaussianIntegrals_lin_fact
import Theorems.Thm_Formalism_L2_Th1_H_cayleyGaussianIntegrals_self_fact
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_altE_swap
import Theorems.Thm_Formalism_L2_Th1_F_altEBasis
import Theorems.Thm_Formalism_L2_Th1_H_altE_swap


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
theorem _root_.solution (L : PeriodPair) (u : ℂ)
    (h1 : ∃ m : ℤ, Formalism.L2.Th1.F.altE L u L.ω₁ = (m : ℝ))
    (h2 : ∃ m : ℤ, Formalism.L2.Th1.F.altE L u L.ω₂ = (m : ℝ)) : u ∈ L.lattice := by
  obtain ⟨m₁, h1⟩ := h1
  obtain ⟨m₂, h2⟩ := h2
  have hu := L.basis.sum_repr u
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one, Complex.real_smul, Complex.real_smul] at hu
  set s := L.basis.repr u 0
  set t := L.basis.repr u 1
  have hsw := Formalism.L2.Th1.F.OperatorUThetaLemmas.altE_swap L L.ω₁ L.ω₂
  rw [← hu, cayleyGaussianIntegrals_lin_fact, cayleyGaussianIntegrals_self_fact, hsw] at h1
  rw [← hu, cayleyGaussianIntegrals_lin_fact, cayleyGaussianIntegrals_self_fact] at h2
  have hE := Formalism.L2.Th1.F.altEBasis L
  rw [← hu]
  split_ifs at hE
  · rw [hE] at h1 h2
    refine PeriodPair.mem_lattice.mpr ⟨-m₂, m₁, ?_⟩
    have hs : s = -(m₂ : ℝ) := by linarith
    have ht : t = (m₁ : ℝ) := by linarith
    rw [hs, ht]
    push_cast
    ring
  · rw [hE] at h1 h2
    refine PeriodPair.mem_lattice.mpr ⟨m₂, -m₁, ?_⟩
    have hs : s = (m₂ : ℝ) := by linarith
    have ht : t = -(m₁ : ℝ) := by linarith
    rw [hs, ht]
    push_cast
    ring
end Formalism.L2.Th1.H
