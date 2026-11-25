-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg.isUnit_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:57.661266+00:00
-- url     : https://prove2.me/submissions/063571b7-e832-4091-b338-7c40b15e1728

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanDirAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
open NumberField Matrix
variable (E : Type) [Field E] [NumberField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (d : ℤ) (hd : ¬ (g : ℤ) ∣ d) : IsUnit (d : V) := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hd
  have h1 : (u : V) * (g : V) + (v : V) * (d : V) = 1 := by
    have := congrArg (Int.cast : ℤ → V) huv
    push_cast at this
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hgV
  · exact isUnit_of_mul_isUnit_right h
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
