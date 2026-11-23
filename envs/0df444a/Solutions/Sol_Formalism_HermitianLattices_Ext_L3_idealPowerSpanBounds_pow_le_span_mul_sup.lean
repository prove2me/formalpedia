-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.pow_le_span_mul_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:37.944664+00:00
-- url     : https://prove2.me/submissions/499bcc3d-a447-4a2b-ab5c-d003db33bffc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mul_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
theorem _root_.solution (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c k : ℕ} (hg : g ∉ P ^ (c + 1))
    (hck : c ≤ k) : P ^ k ≤ Ideal.span {g} * P ^ (k - c) ⊔ P ^ (k + 1) := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hP0 hP.ne_top (by omega : k - c < k - c + 1))
  have hdvd : Ideal.span {g} * P ^ (k - c) ⊔ P ^ (k + 1) ∣ P ^ (k + 1) :=
    Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr (k + 1)).mp hdvd
  rw [associated_iff_eq] at hm
  have hgx : g * x ∈ P ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hx)
  have hmk : m ≤ k := by
    by_contra h
    have h1 := mul_notMem hP hP0 hg hx'
    have e : c + (k - c) + 1 = k + 1 := by omega
    rw [e] at h1
    exact h1 (Ideal.pow_le_pow_right (by omega) hgx)
  rw [hm]
  exact Ideal.pow_le_pow_right hmk
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
