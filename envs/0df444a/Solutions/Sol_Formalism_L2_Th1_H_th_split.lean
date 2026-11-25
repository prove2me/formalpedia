-- Prove2me | solution 1 for Formalism.L2.Th1.H.th_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:08.273277+00:00
-- url     : https://prove2.me/submissions/45cdb335-9d48-45af-957a-2f0bd4682a90

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Th0TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Theorems.Thm_Formalism_L2_Th1_H_mem_stdLat
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_sq
import Theorems.Thm_Formalism_L2_Th1_H_stdChar_single
import Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_th0Char_sq
import Theorems.Thm_Formalism_L2_Th1_F_th0Line
import Theorems.Thm_Formalism_L2_Th1_H_stdH_apply


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
theorem _root_.solution (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h0 : ω₀ ∈ L.lattice)
    (hh : ω₀ / 2 ∉ L.lattice) (α : (n → ℂ) → ℂ) (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x)
    (G : (n → ℂ) → ℂ) (hG : G ∈ Th (stdH L n) α (stdLat L n)) (w : n → ℂ) (i : n) :
    G w = G (Function.update w i 0) * Formalism.L2.Th1.F.th0 L (ω₀ / 2) (w i) := by
  obtain ⟨hGa, hGf⟩ := hG
  have hu : Differentiable ℂ (fun t : ℂ => Function.update w i t) := by
    rw [differentiable_pi]
    intro j
    by_cases h : j = i
    · subst h
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne h]
      exact differentiable_const _
  have hGd : Differentiable ℂ G := fun z => (hGa z (Set.mem_univ z)).differentiableAt
  have hline := Formalism.L2.Th1.F.th0Line L ω₀ (fun t => G (Function.update w i t)) h0 hh (hGd.comp hu) ?_
    (w i)
  · simpa only [Function.update_eq_self] using hline
  · intro ω hω t
    have hx : (Pi.single i ω : n → ℂ) ∈ stdLat L n := by
      rw [mem_stdLat]
      intro j
      by_cases hj : j = i
      · subst hj
        rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj]
        exact L.lattice.zero_mem
    have hfix := hGf _ hx (Function.update w i t)
    have hsum : Function.update w i t + Pi.single i ω = Function.update w i (t + ω) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    have hH1 : stdH L n (Function.update w i t) (Pi.single i ω) = Formalism.L2.Th1.F.herm L t ω := by
      rw [stdH_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp [Formalism.L2.Th1.F.herm]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hH2 : stdH L n (Pi.single i ω) (Pi.single i ω) = Formalism.L2.Th1.F.herm L ω ω := by
      rw [stdH_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp [Formalism.L2.Th1.F.herm]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hα _ hx, stdChar_single, opU, hsum, hH1, hH2] at hfix
    have hsq := th0Char_sq L ω₀ ω h0 hω
    have he : Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    show G (Function.update w i (t + ω)) = _
    rw [← hfix]
    linear_combination
      (-(G (Function.update w i (t + ω))) * (Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2))) * hsq
      - G (Function.update w i (t + ω)) * he
end Formalism.L2.Th1.H
