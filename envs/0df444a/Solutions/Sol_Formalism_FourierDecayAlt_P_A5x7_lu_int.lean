-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.lu_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:55.920323+00:00
-- url     : https://prove2.me/submissions/54101297-f631-4e68-8d39-6c017305a51c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution {n : ℕ} {h u : Matrix (Fin n) (Fin n) K} (hh : IsLowUni h) (hu : IsUpUni u)
    (hI : IsInt R (h * u)) : IsInt R h ∧ IsInt R u := by
  obtain ⟨hhT, hhD⟩ := hh
  obtain ⟨huT, huD⟩ := hu
  have key : ∀ m : ℕ, ∀ i j : Fin n, min i.val j.val = m → h i j ∈ R ∧ u i j ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i j hm
    have IH : ∀ a b : Fin n, min a.val b.val < m → h a b ∈ R ∧ u a b ∈ R :=
      fun a b hab => ih _ hab a b rfl
    have hM : (h * u) i j = ∑ k, h i k * u k j := Matrix.mul_apply
    by_cases hij : i.val ≤ j.val
    · have hterm : ∀ k ∈ Finset.univ.erase i, h i k * u k j ∈ R := by
        intro k hk
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · have hv := Fin.lt_iff_val_lt_val.1 hlt
          exact R.mul_mem (IH i k (by omega)).1 (IH k j (by omega)).2
        · rw [hhT hgt, zero_mul]
          exact R.zero_mem
      have hsum : h i i * u i j + ∑ k ∈ Finset.univ.erase i, h i k * u k j = ∑ k, h i k * u k j :=
        Finset.add_sum_erase Finset.univ (fun k => h i k * u k j) (Finset.mem_univ i)
      have hu' : u i j ∈ R := by
        have e : u i j = (h * u) i j - ∑ k ∈ Finset.univ.erase i, h i k * u k j := by
          rw [hM, ← hsum, hhD i, one_mul, add_sub_cancel_right]
        rw [e]
        exact R.sub_mem (hI i j) (Subring.sum_mem _ hterm)
      refine ⟨?_, hu'⟩
      rcases lt_or_eq_of_le hij with hlt | heq
      · rw [hhT (show i < j from hlt)]
        exact R.zero_mem
      · rw [Fin.ext heq, hhD j]
        exact R.one_mem
    · push_neg at hij
      have hterm : ∀ k ∈ Finset.univ.erase j, h i k * u k j ∈ R := by
        intro k hk
        have hkj : k ≠ j := Finset.ne_of_mem_erase hk
        rcases lt_or_gt_of_ne hkj with hlt | hgt
        · have hv := Fin.lt_iff_val_lt_val.1 hlt
          exact R.mul_mem (IH i k (by omega)).1 (IH k j (by omega)).2
        · rw [huT hgt, mul_zero]
          exact R.zero_mem
      have hsum : h i j * u j j + ∑ k ∈ Finset.univ.erase j, h i k * u k j = ∑ k, h i k * u k j :=
        Finset.add_sum_erase Finset.univ (fun k => h i k * u k j) (Finset.mem_univ j)
      have hh' : h i j ∈ R := by
        have e : h i j = (h * u) i j - ∑ k ∈ Finset.univ.erase j, h i k * u k j := by
          rw [hM, ← hsum, huD j, mul_one, add_sub_cancel_right]
        rw [e]
        exact R.sub_mem (hI i j) (Subring.sum_mem _ hterm)
      refine ⟨hh', ?_⟩
      rw [huT (show j < i from hij)]
      exact R.zero_mem
  exact ⟨fun a b => (key _ a b rfl).1, fun a b => (key _ a b rfl).2⟩
end Formalism.FourierDecayAlt.P.A5x7
