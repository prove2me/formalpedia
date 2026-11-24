-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.rdE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:43:43.536414+00:00
-- url     : https://prove2.me/submissions/b5544236-90ce-4ebd-b48f-c607e45f9ebf

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.DiscrB
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
variable {e q d : ℕ} {ζ a b : L}
namespace Formalism.FrobeniusOrbits.DiscrB
theorem _root_.solution (e q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    |(((2 : ℤ) ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) : ℤ) : ℝ)| ^
        ((1 : ℝ) / (2 ^ (e + 2) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * d := by positivity
  have hB : 4 ≤ 2 ^ (e + 2) * (e + 1) := by
    have : 4 ≤ 2 ^ (e + 2) := by
      rw [pow_add]; norm_num; exact Nat.one_le_two_pow
    nlinarith
  push_cast
  rw [abs_of_nonneg (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast (2 : ℝ) (2 ^ (e + 2) * (e + 1) - 4), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((q : ℝ) * d) (2 ^ (e + 1)), ← Real.rpow_mul hX, Real.sqrt_eq_rpow]
  congr 2
  · rw [Nat.cast_sub hB, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring
end Formalism.FrobeniusOrbits.DiscrB
