-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Orbits.prim_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:48.84215+00:00
-- url     : https://prove2.me/submissions/a0e77fed-a4b1-48ed-aadb-464525b06e3e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Orbits
namespace Formalism.FrobeniusOrbits.Orbits
theorem _root_.solution {E K : Type*} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] [Algebra E K]
    [IsScalarTower ℚ E K] [FiniteDimensional ℚ E] [FiniteDimensional E K] (g : ℕ) (hg : g.Prime)
    (μ : K) (hμ : IsPrimitiveRoot μ g) :
    g - 1 ≤ Module.finrank ℚ E * Module.finrank E K := by
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : CharZero K := by
    first
    | exact algebraRat.charZero K
    | exact (algebraMap ℚ K).charZero
  rw [Module.finrank_mul_finrank ℚ E K]
  have hint : IsIntegral ℚ μ := .of_finite ℚ μ
  have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {μ}) = g - 1 := by
    haveI : NeZero g := ⟨hg.ne_zero⟩
    have hroot : aeval μ (cyclotomic g ℚ) = 0 := by
      rw [aeval_def, ← eval_map, map_cyclotomic]
      exact (isRoot_cyclotomic_iff.mpr hμ)
    rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hg.pos) hroot (cyclotomic.monic g ℚ),
      natDegree_cyclotomic, Nat.totient_prime hg]
  rw [← h1, ← Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {μ}) K]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos
end Formalism.FrobeniusOrbits.Orbits
