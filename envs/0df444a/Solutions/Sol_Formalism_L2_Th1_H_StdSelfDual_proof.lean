-- Prove2me | solution 1 for Formalism.L2.Th1.H.StdSelfDual_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:16.378326+00:00
-- url     : https://prove2.me/submissions/e1acd774-9614-46d1-a8bc-647d8d2b6fbc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_altE_std
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat
import Theorems.Thm_Formalism_L2_Th1_H_mem_lattice_of_dual
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_altEInt


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
theorem _root_.solution : StdSelfDual := by
  intro L n _ _
  refine AddSubgroup.ext fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩
  · rw [mem_stdLat]
    intro i
    have key : ∀ ω ∈ L.lattice, ∃ m : ℤ, Formalism.L2.Th1.F.altE L (x i) ω = (m : ℝ) := by
      intro ω hω
      have hy : (Pi.single i ω : n → ℂ) ∈ stdLat L n := by
        rw [mem_stdLat]
        intro j
        by_cases hj : j = i
        · subst hj
          rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hj]
          exact L.lattice.zero_mem
      obtain ⟨m, hm⟩ := hx _ hy
      refine ⟨m, ?_⟩
      rw [altE_std, Finset.sum_eq_single i] at hm
      · rwa [Pi.single_eq_same] at hm
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm]
      · intro h
        exact absurd (Finset.mem_univ i) h
    exact mem_lattice_of_dual L (x i) (key _ L.ω₁_mem_lattice) (key _ L.ω₂_mem_lattice)
  · rw [mem_stdLat] at hx hy
    choose k hk using fun i => Formalism.L2.Th1.F.altEInt L (x i) (y i) (hx i) (hy i)
    refine ⟨∑ i, k i, ?_⟩
    rw [altE_std]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hk i
end Formalism.L2.Th1.H
