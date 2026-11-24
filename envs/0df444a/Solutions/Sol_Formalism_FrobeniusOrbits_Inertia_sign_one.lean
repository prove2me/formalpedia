-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.sign_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:43.375014+00:00
-- url     : https://prove2.me/submissions/c88d69ba-b4db-4d9a-afb3-bc40fbccbcf6

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sqrt_fixed

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
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution (X : hostE ζ a b) (s : ℤˣ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hXs : ((σ X : hostE ζ a b) : L) = ((s : ℤ) : L) * (X : L)) {r : ℕ} (hr : r.Prime)
    (hr4 : r % 4 = 3) (hX : (X : L) ^ 2 = -(r : L)) {p : ℕ} (hp : p.Prime) (hpr : p ≠ r)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) : s = 1 := by
  rcases Int.units_eq_one_or s with hs | hs
  · exact hs
  · exfalso
    have hX' : X ^ 2 = -(r : hostE ζ a b) := by
      apply (algebraMap (hostE ζ a b) L).injective
      simpa using hX
    have hσX : σ X = -X := by
      apply Subtype.ext
      rw [hXs, hs]
      simp
    exact sqrt_fixed hr hr4 hp hpr P σ hX' hσX hσ
end Formalism.FrobeniusOrbits.Inertia
