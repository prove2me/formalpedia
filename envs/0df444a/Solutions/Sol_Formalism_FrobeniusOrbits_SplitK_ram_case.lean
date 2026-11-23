-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.ram_case
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:20.885428+00:00
-- url     : https://prove2.me/submissions/776101e8-cf7d-47c3-ad91-876f9de7019d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_bK_sq_int
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_fund
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd : d.Prime) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime] (hpd : p = d)
    (P : Ideal (𝓞 (Kd b))) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 1 := by
  subst hpd
  have hd0 : 0 < p := hd.pos
  obtain ⟨B, hB, hB2⟩ := odd_lift (bK b) (-(p : ℤ)) (bK_sq_int hb)
  have hdP : ((p : ℤ) : 𝓞 (Kd b)) ∈ P := (odd_intCast_mem_iff p P _).mpr dvd_rfl
  have hBP : B ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hB2, Int.cast_neg]
    exact P.neg_mem hdP
  have hmap : map (algebraMap ℤ (𝓞 (Kd b))) (span {(p : ℤ)}) = span {((p : ℤ) : 𝓞 (Kd b))} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hle : span {((p : ℤ) : 𝓞 (Kd b))} ≤ P ^ 2 := by
    rw [Ideal.span_singleton_le_iff_mem]
    have : ((p : ℤ) : 𝓞 (Kd b)) = -(B ^ 2) := by
      rw [hB2]
      simp
    rw [this]
    exact (P ^ 2).neg_mem (Ideal.pow_mem_pow hBP 2)
  have hne : map (algebraMap ℤ (𝓞 (Kd b))) (span {(p : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd.ne_zero
  have he : 2 ≤ P.ramificationIdx ℤ := by
    rw [IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(p : ℤ)}) P hne]
    apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
    · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
    · rw [Ideal.dvd_iff_le, hmap]
      exact hle
  have hf := P.inertiaDeg_pos ℤ
  have hm := fund hd0 hb p P
  set g := (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard
  set e := P.ramificationIdx ℤ
  set f := P.inertiaDeg ℤ
  have hef : 2 ≤ e * f := by nlinarith
  rcases Nat.lt_or_ge g 2 with hg | hg
  · interval_cases g
    · simp at hm
    · rfl
  · nlinarith
end Formalism.FrobeniusOrbits.SplitK
