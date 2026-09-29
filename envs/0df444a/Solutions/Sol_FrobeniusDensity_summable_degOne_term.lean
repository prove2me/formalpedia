-- Prove2me | solution 1 for FrobeniusDensity.summable_degOne_term
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a50fda54-3e1c-5f9e-9c3b-8ee2b430cf97

import Theorems.Thm_FrobeniusDensity_idealSum_ne_top
import Theorems.Thm_FrobeniusDensity_primeSum_eq_degOneSum_add
import Definitions.Def_FrobeniusDensity_PrimeSums
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_summable_degOne_term

set_option autoImplicit false

p2m_open "Ideal NumberField IsDedekindDomain Ideal.IsDedekindDomain"
open scoped ENNReal

namespace FrobeniusDensity
p2m_export "FrobeniusDensity" "idealSum_ne_top normRpow idealSum primeSum degOneSum degOneCount primeSum_eq_degOneSum_add"
p2m_open "FrobeniusDensity"

variable (K : Type*) [Field K] [NumberField K]

private lemma primeSum_le_idealSum (s : ℝ) : primeSum K s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (⟨v.asIdeal, v.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) :=
    fun v w h => HeightOneSpectrum.ext (by simpa using congrArg Subtype.val h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

private lemma degOneSum_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) : degOneSum K S₀ s ≠ ⊤ := by
  have h1 : degOneSum K S₀ s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K S₀ s, add_assoc]
    exact self_le_add_right _ _
  exact (h1.trans_lt ((primeSum_le_idealSum K s).trans_lt
    (idealSum_ne_top K hs).lt_top)).ne

omit [NumberField K] in
private theorem toReal_term (S₀ : Finset ℕ) (s : ℝ) (ℓ : ℕ) :
    ((if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)).toReal
      = (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

end FrobeniusDensity

p2m_open "FrobeniusDensity P2MW.S_FrobeniusDensity_summable_degOne_term.FrobeniusDensity"

theorem solution (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) :=
  (ENNReal.summable_toReal (degOneSum_ne_top K S₀ hs)).congr (toReal_term K S₀ s)

end S_FrobeniusDensity_summable_degOne_term
end P2MW
export P2MW.S_FrobeniusDensity_summable_degOne_term (solution)
