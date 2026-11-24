-- Prove2me | solution 1 for Formalism.HC.Der.kc_exists_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:25.981934+00:00
-- url     : https://prove2.me/submissions/ce368cf2-e5dc-42da-9974-9640758da106

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
private theorem liesOver_span_of_natCast_mem_prime {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (p : ℕ)
    (hp : p.Prime) (h : (p : 𝓞 M) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by
  constructor
  have hmax : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine hmax.eq_of_le (inferInstance : (P.under ℤ).IsPrime).ne_top ?_
  rw [Ideal.span_singleton_le_iff_mem]
  show algebraMap ℤ (𝓞 M) (p : ℤ) ∈ P
  simpa using h
variable (C : HostCore H)
include C
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Formalism.HC.Der
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (hm : (n : 𝓞 M) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ P.LiesOver (span {(p : ℤ)}) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hm))
  have hpm := Nat.minFac_prime hn1
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  have hm' : (n.minFac : 𝓞 M) * (k : 𝓞 M) ∈ P := by
    rw [← Nat.cast_mul, ← hk]
    exact hm
  rcases hP.mem_or_mem hm' with h | h
  · exact ⟨n.minFac, hpm, Nat.minFac_dvd n, liesOver_span_of_natCast_mem_prime P _ hpm h⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
      exact hn hk
    have hkn : k < n := by
      have h2 := hpm.two_le
      have hkpos := Nat.pos_of_ne_zero hk0
      rw [hk]
      nlinarith
    obtain ⟨p, hp, hpk, hl⟩ := ih k hkn hk0 h
    exact ⟨p, hp, hpk.trans (Dvd.intro_left _ hk.symm), hl⟩
end Formalism.HC.Der
