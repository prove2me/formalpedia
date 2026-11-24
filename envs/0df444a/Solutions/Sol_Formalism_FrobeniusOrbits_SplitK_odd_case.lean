-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.odd_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:43.783807+00:00
-- url     : https://prove2.me/submissions/7d07c20f-af98-4205-984d-d3cc1acbb50c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_quad_K
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_bK_sq_int
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_exists_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_apply_bK_of_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_eq_of_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ncard_one
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ncard_two
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_smul_mem_of_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_smul_intCast
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_coe_smul
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
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
theorem _root_.solution (hd : d.Prime) (hb : b ^ 2 = -(d : L)) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : p ≠ d) (P : Ideal (𝓞 (Kd b))) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔ jacobiSym (-(d : ℤ)) p = 1 := by
  have hd0 := hd.pos
  have := quad_K hd0 hb
  have hpb : span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have : Finite (𝓞 (Kd b) ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (Kd b ≃ₐ[ℚ] Kd b) P
  have hnd : ¬ (p : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg]
    intro h'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp.out hd).mp (by exact_mod_cast h'))
  have hsgn := odd_frob_sgn p hp2 P τ hτ (bK b) _ (bK_sq_int hb) hnd
  have hcop : Int.gcd (-(d : ℤ)) p = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hd hp.out).mpr (Ne.symm hpd)
  rcases jacobiSym.eq_one_or_neg_one hcop with hj | hj
  · simp only [hj, iff_true]
    obtain ⟨ι, hι⟩ := exists_ne_one hd0 hb
    apply ncard_two hd0 hb p P ι
    intro heq
    have hleg : legendreSym p (-(d : ℤ)) = 1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact hj
    have h0 : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hnd
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p h0).mp hleg
    set t : ℤ := (r.val : ℤ) with ht
    have htd : (p : ℤ) ∣ t ^ 2 + d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
      push_cast at hr
      linear_combination -hr
    obtain ⟨B, hB, hB2⟩ := odd_lift (bK b) (-(d : ℤ)) (bK_sq_int hb)
    have hιB : ι • B = -B := by
      apply RingOfIntegers.coe_injective
      show ((ι • B : 𝓞 (Kd b)) : Kd b) = ((-B : 𝓞 (Kd b)) : Kd b)
      rw [odd_coe_smul, hB, apply_bK_of_ne hd0 hb ι hι]
      simp [hB]
    have hprod : (B - (t : 𝓞 (Kd b))) * (B + (t : 𝓞 (Kd b))) ∈ P := by
      have he : (B - (t : 𝓞 (Kd b))) * (B + (t : 𝓞 (Kd b))) = -((t ^ 2 + d : ℤ) : 𝓞 (Kd b)) := by
        rw [show (B - (t : 𝓞 (Kd b))) * (B + (t : 𝓞 (Kd b))) = B ^ 2 - (t : 𝓞 (Kd b)) ^ 2 by ring,
          hB2]
        push_cast
        ring
      rw [he]
      exact P.neg_mem ((odd_intCast_mem_iff p P _).mpr htd)
    have h2t : ((2 * t : ℤ) : 𝓞 (Kd b)) ∈ P := by
      rcases hP.mem_or_mem hprod with h | h
      · have h' := smul_mem_of_eq ι P heq _ h
        rw [smul_sub, hιB, smul_intCast] at h'
        have := P.neg_mem (P.add_mem h h')
        convert this using 1
        push_cast
        ring
      · have h' := smul_mem_of_eq ι P heq _ h
        rw [smul_add, hιB, smul_intCast] at h'
        have := P.add_mem h h'
        convert this using 1
        push_cast
        ring
    rw [odd_intCast_mem_iff p P] at h2t
    have hpt : (p : ℤ) ∣ t := by
      rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h2t with h | h
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
      · exact h
    apply hnd
    have h1 : (p : ℤ) ∣ t ^ 2 := dvd_pow hpt two_ne_zero
    exact dvd_neg.mpr ((dvd_add_right h1).mp htd)
  · rw [hj]
    have hne : τ ≠ 1 := by
      intro h1
      rw [h1, hj] at hsgn
      simp [sgn] at hsgn
    have hall : ∀ σ : Kd b ≃ₐ[ℚ] Kd b, σ • P = P := by
      intro σ
      by_cases hσ : σ = 1
      · rw [hσ]
        exact one_smul _ _
      · rw [eq_of_ne_one hd0 hb σ τ hσ hne]
        exact MulAction.mem_stabilizer_iff.mp (IsArithFrobAt.mem_stabilizer hτ)
    rw [ncard_one hd0 hb p P hall]
    norm_num
end Formalism.FrobeniusOrbits.SplitK
