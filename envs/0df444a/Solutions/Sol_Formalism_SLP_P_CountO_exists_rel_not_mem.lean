-- Prove2me | solution 1 for Formalism.SLP.P.CountO.exists_rel_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:42.515528+00:00
-- url     : https://prove2.me/submissions/883321b6-b1c7-4e5b-971c-ee9ceaf06e8d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_exists_local_min

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution {X : Type} [AddCommGroup X] [Module R X]
    (htf : ∀ a : R, a ≠ 0 → ∀ x : X, a • x = 0 → x = 0)
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) {ι : Type} (t : Finset ι) (v : ι → X)
    (g : ι → R) (hg : ∑ i ∈ t, g i • v i = 0) (hne : ∃ i ∈ t, g i ≠ 0) :
    ∃ i0 ∈ t, ∃ d : ι → R, d i0 ∉ P ∧ ∑ i ∈ t, d i • v i = 0 := by
  obtain ⟨i0, hi0, hne0, s, hs, d, hd⟩ := exists_local_min P hP t g hne
  refine ⟨i0, hi0, d, ?_, ?_⟩
  · have h1 : s * g i0 = g i0 * d i0 := hd i0 hi0
    have h2 : d i0 = s := by
      apply mul_left_cancel₀ hne0
      rw [← h1]; ring
    rw [h2]; exact hs
  · apply htf (g i0) hne0
    rw [Finset.smul_sum]
    calc ∑ i ∈ t, g i0 • d i • v i = ∑ i ∈ t, s • g i • v i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [smul_smul, smul_smul, hd i hi]
      _ = s • ∑ i ∈ t, g i • v i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hg, smul_zero]
end Formalism.SLP.P.CountO
