-- Prove2me | solution 1 for Formalism.BehrendSets.Stab.totient_le_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:44.01191+00:00
-- url     : https://prove2.me/submissions/417b08e6-91d3-40f6-bd60-b1b3174e99df

import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TotientLeOfIsPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Module Matrix
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Stab
namespace Formalism.BehrendSets.Stab
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K]
    [FiniteDimensional E K] {g : ℕ} (hg : 0 < g) {ζ : K} (hζ : IsPrimitiveRoot ζ g) :
    Nat.totient g ≤ finrank ℚ E * finrank E K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : FiniteDimensional ℚ K := Module.Finite.trans E K
  rw [Module.finrank_mul_finrank ℚ E K]
  have h1 := minpoly.natDegree_le (A := ℚ) ζ
  rw [← cyclotomic_eq_minpoly_rat hζ hg, natDegree_cyclotomic] at h1
  exact h1
end Formalism.BehrendSets.Stab
