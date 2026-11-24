-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Mu.mu_le_ram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:14:14.526803+00:00
-- url     : https://prove2.me/submissions/6296b1b2-1b29-463e-b182-88b62530631f

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.Mu
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] (k : ℕ) (hk : ((p : ℤ) : 𝓞 L) ∈ Q ^ k) :
    k ≤ Q.ramificationIdx ℤ := by
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) = span {((p : ℤ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, algebraMap_int_eq, eq_intCast]
  have hne0 : ((p : ℤ) : 𝓞 L) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 L) L) h0
    have h2 : (p : L) = 0 := by simpa using h1
    exact hp.out.ne_zero (by exact_mod_cast h2)
  have hne : Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hne0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(p : ℤ)}) Q hne]
  have hdvd : Q ^ k ∣ Ideal.map (algebraMap ℤ (𝓞 L)) (span {(p : ℤ)}) := by
    rw [Ideal.dvd_iff_le, hmap, Ideal.span_singleton_le_iff_mem]
    exact hk
  have hQ : ¬ IsUnit Q := by
    rw [Ideal.isUnit_iff]
    exact Ideal.IsPrime.ne_top ‹_›
  first
    | exact (FiniteMultiplicity.of_not_isUnit hQ hne).le_multiplicity_of_pow_dvd hdvd
    | exact (multiplicity_finite_of_not_isUnit hQ hne).le_multiplicity_of_pow_dvd hdvd
    | exact ((pow_dvd_iff_le_multiplicity (FiniteMultiplicity.of_not_isUnit hQ hne)).mp hdvd)
end Formalism.FrobeniusOrbits.Mu
