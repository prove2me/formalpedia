-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.class_number_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:14.253693+00:00
-- url     : https://prove2.me/submissions/56912ed6-4cea-41cd-838b-89a1b584b3b2

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_norm_le_count
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_factorial_mul_two_pow_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ClassNumberBound := by
  intro E _ _
  classical
  set d := finrank ℚ E
  have hd : 1 ≤ d := Module.finrank_pos
  set D : ℝ := |(NumberField.discr E : ℝ)|
  have hD1 : 1 ≤ D := by
    have h0 := NumberField.discr_ne_zero E
    have : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs h0
    simp only [D]; exact_mod_cast this
  set x : ℝ := Real.sqrt D
  have hx1 : 1 ≤ x := by simp only [x]; rw [Real.one_le_sqrt]; exact hD1

  have hr2 : NumberField.InfinitePlace.nrComplexPlaces E ≤ d - 1 := by
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
    omega
  have hc : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
      ((d.factorial : ℝ) / (d : ℝ) ^ d) ≤ 1 := by
    have hpi : 4 / Real.pi ≤ 2 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    have h1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E ≤ (2:ℝ) ^ (d - 1) :=
      (pow_le_pow_left₀ (by positivity) hpi _).trans (pow_le_pow_right₀ (by norm_num) hr2)
    have h2 := factorial_mul_two_pow_le_pow d hd
    have hdd : (0:ℝ) < (d:ℝ) ^ d := by positivity
    calc (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
          ((d.factorial : ℝ) / (d : ℝ) ^ d)
        ≤ (2:ℝ) ^ (d - 1) * ((d.factorial : ℝ) / (d : ℝ) ^ d) := by gcongr
      _ = ((d.factorial : ℝ) * 2 ^ (d - 1)) / (d : ℝ) ^ d := by ring
      _ ≤ 1 := by rw [div_le_one hdd]; exact h2
  obtain ⟨hfin, hcount⟩ := ideal_norm_le_count E x hx1

  have hch : ∀ C : ClassGroup (𝓞 E), ∃ I : (Ideal (𝓞 E))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 E)) : ℝ) ≤ x := by
    intro C
    obtain ⟨I, hI, hN⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    refine ⟨I, hI, hN.trans ?_⟩
    have hx0 : 0 ≤ x := by positivity
    calc (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
          ((d.factorial : ℝ) / (d : ℝ) ^ d * x)
        = ((4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces E *
          ((d.factorial : ℝ) / (d : ℝ) ^ d)) * x := by ring
      _ ≤ 1 * x := by gcongr
      _ = x := one_mul x
  choose f hf1 hf2 using hch
  have hinj : Function.Injective (fun C => (f C : Ideal (𝓞 E))) := by
    intro C C' h
    have : f C = f C' := Subtype.ext h
    rw [← hf1 C, ← hf1 C', this]
  have hcard : NumberField.classNumber E ≤
      {I : Ideal (𝓞 E) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    unfold NumberField.classNumber
    rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
    apply Finset.card_le_card
    intro I hI
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.1 hI
    rw [Set.Finite.mem_toFinset]
    exact ⟨nonZeroDivisors.coe_ne_zero (f C), hf2 C⟩
  have hxD : x ^ (1 + Real.logb 2 d) = D ^ ((1 + Real.logb 2 d) / 2) := by
    simp only [x]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    ring_nf
  calc (NumberField.classNumber E : ℝ)
      ≤ (({I : Ideal (𝓞 E) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ x ^ (1 + Real.logb 2 d) := hcount
    _ = D ^ ((1 + Real.logb 2 d) / 2) := hxD
end Formalism.HermitianLatticeCounting.P
