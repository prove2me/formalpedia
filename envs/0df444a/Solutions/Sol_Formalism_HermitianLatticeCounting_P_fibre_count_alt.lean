-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.fibre_count_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:46.453035+00:00
-- url     : https://prove2.me/submissions/287919b2-d1bd-4ec9-9b1e-24f90e9bc285

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : FibreCount := by
  classical
  intro α S r β π c hc h0 hr hstep
  have key : ∀ i, i ≤ r → ((S.image (π i)).card : ℝ) ≤ ∏ k ∈ range i, c k := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.prod_empty]
      have : (S.image (π 0)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        exact h0 x hx y hy
      exact_mod_cast this
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hfib : ∀ b ∈ S.image (π i),
          (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) ≤ c i := by
        intro b _
        obtain ⟨T, hTF, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
          (f := π (i+1)) (S.filter (fun x => π i x = b))
          ((S.filter (fun x => π i x = b)).image (π (i+1)))
          (by
            intro v hv
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
            exact ⟨x, hx, rfl⟩)
        rw [← himg, Finset.card_image_of_injOn hinj]
        apply hstep i (by omega) T
        · intro x hx; exact (Finset.mem_filter.mp (hTF hx)).1
        · intro y hy z hz
          rw [(Finset.mem_filter.mp (hTF hy)).2, (Finset.mem_filter.mp (hTF hz)).2]
        · intro y hy z hz hyz
          exact hinj hy hz hyz
      have hsub : S.image (π (i+1)) ⊆ (S.image (π i)).biUnion
          (fun b => (S.filter (fun x => π i x = b)).image (π (i+1))) := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_biUnion.mpr ⟨π i x, Finset.mem_image_of_mem _ hx,
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
      calc ((S.image (π (i+1))).card : ℝ)
          ≤ (((S.image (π i)).biUnion
              (fun b => (S.filter (fun x => π i x = b)).image (π (i+1)))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ∑ b ∈ S.image (π i), (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ b ∈ S.image (π i), c i := Finset.sum_le_sum hfib
        _ = (S.image (π i)).card * c i := by simp
        _ ≤ (∏ k ∈ range i, c k) * c i := by
            apply mul_le_mul_of_nonneg_right ih' (hc i)
        _ = _ := (Finset.prod_range_succ _ _).symm
  have := key r le_rfl
  rwa [Finset.card_image_of_injOn (fun x hx y hy h => hr x hx y hy h)] at this
end Formalism.HermitianLatticeCounting.P
