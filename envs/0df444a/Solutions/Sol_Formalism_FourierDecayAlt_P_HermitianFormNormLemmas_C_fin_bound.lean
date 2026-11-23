-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.fin_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:13.900453+00:00
-- url     : https://prove2.me/submissions/4229d911-525a-438f-9a1e-c72a463eff12

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
theorem _root_.solution (hW : Formalism.HermitianLatticeCounting.S4.WeightedCS) {Cl J V : Type} [NormedAddCommGroup V] (U : Cl → J → V)
    (W : J → ℝ) (y : Cl → J → ℝ) (S1 M : ℝ) (hS1 : 0 ≤ S1)
    (hWpos : ∀ c j, U c j ≠ 0 → 0 < W j) (hy : ∀ c j, ‖U c j‖ ^ 2 ≤ y c j)
    (h1 : ∀ (c : Cl) (T : Finset J), (∀ j ∈ T, U c j ≠ 0) → ∑ j ∈ T, (W j)⁻¹ ≤ S1)
    (h2 : ∀ T : Finset (Cl × J), (∀ x ∈ T, U x.1 x.2 ≠ 0) → ∑ x ∈ T, W x.2 * y x.1 x.2 ≤ M)
    (Cs : Finset Cl) (T : Finset J) : ∑ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2 ≤ S1 * M := by
  classical
  unfold Formalism.HermitianLatticeCounting.S4.WeightedCS at hW
  have hc : ∀ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2 ≤ S1 * ∑ j ∈ T with U c j ≠ 0, W j * y c j := by
    intro c _
    have hW' : ‖∑ j ∈ T with U c j ≠ 0, U c j‖ ^ 2 ≤ (∑ j ∈ T with U c j ≠ 0, (W j)⁻¹) *
        ∑ j ∈ T with U c j ≠ 0, W j * ‖U c j‖ ^ 2 := by
      have h := hW (↥(T.filter (fun j => U c j ≠ 0))) V (fun j => U c j.1) (fun j => W j.1)
        (fun j => hWpos c j.1 (Finset.mem_filter.1 j.2).2)
      simp only [Finset.univ_eq_attach] at h
      rw [Finset.sum_attach _ (U c), Finset.sum_attach _ (fun j => (W j)⁻¹),
        Finset.sum_attach _ (fun j => W j * ‖U c j‖ ^ 2)] at h
      exact h
    have hs : ∑ j ∈ T with U c j ≠ 0, U c j = ∑ j ∈ T, U c j := Finset.sum_filter_ne_zero _
    rw [← hs]
    refine hW'.trans ?_
    refine mul_le_mul (h1 c _ (fun j hj => (Finset.mem_filter.1 hj).2))
      (Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hy c j)
        (hWpos c j (Finset.mem_filter.1 hj).2).le)) ?_ hS1
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (hWpos c j (Finset.mem_filter.1 hj).2).le
      (sq_nonneg _))
  calc ∑ c ∈ Cs, ‖∑ j ∈ T, U c j‖ ^ 2
      ≤ ∑ c ∈ Cs, S1 * ∑ j ∈ T with U c j ≠ 0, W j * y c j := Finset.sum_le_sum hc
    _ = S1 * ∑ x ∈ Cs ×ˢ T with U x.1 x.2 ≠ 0, W x.2 * y x.1 x.2 := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.sum_filter, Finset.sum_product]
    _ ≤ S1 * M := mul_le_mul_of_nonneg_left (h2 _ (fun x hx => (Finset.mem_filter.1 hx).2)) hS1
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
