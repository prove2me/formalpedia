-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.mul_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:19.473533+00:00
-- url     : https://prove2.me/submissions/1d0a0cd7-eda8-4fa9-bb72-8c1607df19af

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
section DedekindLFunctions
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
private theorem not_pow_dvd_mul_of_not_pow_dvd_of_not_pow_dvd (hpr : Prime P) (i : ℕ) :
    ∀ (j : ℕ) (A B : Ideal R), ¬ P ^ (i + 1) ∣ A → ¬ P ^ (j + 1) ∣ B →
      ¬ P ^ (i + j + 1) ∣ A * B := by
  induction i with
  | zero =>
    intro j A B hA hB h
    apply hB
    have hA' : ¬ P ∣ A := by simpa using hA
    have h' : P ^ (j + 1) ∣ A * B := by simpa using h
    exact hpr.pow_dvd_of_dvd_mul_left (j + 1) hA' h'
  | succ i ih =>
    intro j A B hA hB h
    by_cases hPA : P ∣ A
    · obtain ⟨A1, rfl⟩ := hPA
      apply ih j A1 B
      · intro h1
        apply hA
        rw [pow_succ']
        exact mul_dvd_mul_left P h1
      · exact hB
      · have h2 : P * P ^ (i + j + 1) ∣ P * (A1 * B) := by
          rw [← pow_succ', ← mul_assoc]
          have e : i + j + 1 + 1 = i + 1 + j + 1 := by omega
          rw [e]
          exact h
        exact (mul_dvd_mul_iff_left hpr.ne_zero).mp h2
    · apply hB
      have h3 := hpr.pow_dvd_of_dvd_mul_left (i + 1 + j + 1) hPA h
      exact dvd_trans (pow_dvd_pow P (by omega)) h3
end DedekindLFunctions
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution (hP : P.IsPrime) (hP0 : P ≠ ⊥) {a b : R} {i j : ℕ} (ha : a ∉ P ^ (i + 1))
    (hb : b ∉ P ^ (j + 1)) : a * b ∉ P ^ (i + j + 1) := by
  intro hab
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  refine not_pow_dvd_mul_of_not_pow_dvd_of_not_pow_dvd hpr i j (Ideal.span {a}) (Ideal.span {b}) ?_ ?_ ?_
  · rwa [Ideal.dvd_span_singleton]
  · rwa [Ideal.dvd_span_singleton]
  · rwa [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
