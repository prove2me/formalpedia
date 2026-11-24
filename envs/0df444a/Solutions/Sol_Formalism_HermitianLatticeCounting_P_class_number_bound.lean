-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.class_number_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:34.892253+00:00
-- url     : https://prove2.me/submissions/61cc3b50-73e3-42c5-a52f-cba44a0c9d1b

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minkowski_constant_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_count_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ClassNumberBound := by
  intro E _ _ hc
  classical
  set D : ℝ := Real.sqrt |(discr E : ℝ)| with hD
  have hD1 : 1 ≤ D := by
    rw [hD, Real.one_le_sqrt]
    have h0 : discr E ≠ 0 := discr_ne_zero E
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs h0
    exact_mod_cast this
  obtain ⟨hfin, hcount⟩ := ideal_count_bound E D hD1
  refine le_trans ?_ hcount

  have hr2 : finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h3 : InfinitePlace.nrRealPlaces E = 0 := by
      rw [InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr w.2) (hc w.1)⟩
    omega
  have hM : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) ≤ D := by
    have h1 := minkowski_constant_bound (InfinitePlace.nrComplexPlaces E)
    rw [← hr2] at h1
    have h2 : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces E ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      rw [div_le_one Real.pi_pos]; exact Real.two_le_pi
    have h3 : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) =
      ((4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E * ((finrank ℚ E).factorial : ℝ) /
        (finrank ℚ E : ℝ) ^ (finrank ℚ E)) * D := by ring
    rw [h3]
    calc _ ≤ 1 * D := by
          apply mul_le_mul_of_nonneg_right (h1.trans h2) (by linarith)
      _ = D := one_mul D
  choose I hI1 hI2 using exists_ideal_in_class_of_norm_le (K := E)
  have hinj : Function.Injective (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E))) := by
    intro C C' h
    have : I C = I C' := Subtype.ext h
    rw [← hI1 C, ← hI1 C', this]
  have hle : Fintype.card (ClassGroup (𝓞 E)) ≤ hfin.toFinset.card := by
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)))
    · intro C _
      rw [Finset.mem_coe, hfin.mem_toFinset]
      exact ⟨nonZeroDivisors.ne_zero (I C).2, (hI2 C).trans hM⟩
    · exact hinj.injOn
  rw [Set.ncard_eq_toFinset_card _ hfin, classNumber]
  exact_mod_cast hle
end Formalism.HermitianLatticeCounting.P
