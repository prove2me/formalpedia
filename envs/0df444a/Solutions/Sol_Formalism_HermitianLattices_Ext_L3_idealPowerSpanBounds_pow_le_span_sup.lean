-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.pow_le_span_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:55.092577+00:00
-- url     : https://prove2.me/submissions/85d84e24-08ef-40a7-9044-14f082b2dc9b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup

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
theorem _root_.solution (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c : ℕ} (hg : g ∉ P ^ (c + 1)) (N : ℕ) :
    P ^ c ≤ Ideal.span {g} ⊔ P ^ N := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : Ideal.span {g} ⊔ P ^ N ∣ P ^ N := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr N).mp hdvd
  rw [associated_iff_eq] at hm
  have hgm : g ∈ P ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self g)
  have hmc : m ≤ c := by
    by_contra h
    exact hg (Ideal.pow_le_pow_right (by omega) hgm)
  rw [hm]
  exact Ideal.pow_le_pow_right hmc
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
