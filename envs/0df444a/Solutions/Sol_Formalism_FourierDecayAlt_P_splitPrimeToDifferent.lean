-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.splitPrimeToDifferent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:16.255044+00:00
-- url     : https://prove2.me/submissions/75c1570c-39b9-498e-aa07-ba9e30ca75c1

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x4
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.SplitCoprime := by
  intro E _ _ _ p ⟨hp, h⟩
  unfold PrimeToDifferent
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hD : differentIdeal ℤ (𝓞 E) ≤ P := le_sup_left.trans hle
  have hpP : (p : 𝓞 E) ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have h2 := (h P hPmax.isPrime hpP).2
  let p0 : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hmap : p0.map (algebraMap ℤ (𝓞 E)) = Ideal.span {(p : 𝓞 E)} := by
    simp [p0, Ideal.map_span]
  have hp0 : p0 ≠ ⊥ := by
    simp [p0, hp.ne_zero]
  have : p0.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have : Finite (ℤ ⧸ p0) := Ideal.finiteQuotientOfFreeOfNeBot p0 hp0
  obtain ⟨Q, hQ⟩ : P ∣ p0.map (algebraMap ℤ (𝓞 E)) :=
    Ideal.dvd_iff_le.2 (by rw [hmap, Ideal.span_singleton_le_iff_mem]; exact hpP)
  have hcop : IsCoprime P Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hc
    have he : P = P ⊔ Q := hPmax.eq_of_le hc le_sup_left
    have hQP : Q ≤ P := by rw [he]; exact le_sup_right
    apply h2
    have : p0.map (algebraMap ℤ (𝓞 E)) ≤ P ^ 2 := by
      rw [hQ, pow_two]; exact Ideal.mul_mono_right hQP
    exact this (by rw [hmap]; exact Ideal.mem_span_singleton_self _)
  exact not_dvd_differentIdeal_of_isCoprime ℤ P Q hcop hQ.symm (Ideal.dvd_iff_le.2 hD)
end Formalism.FourierDecayAlt.P
