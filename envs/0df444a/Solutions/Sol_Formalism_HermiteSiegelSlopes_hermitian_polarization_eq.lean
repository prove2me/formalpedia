-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.hermitian_polarization_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:08.633803+00:00
-- url     : https://prove2.me/submissions/ba20f7bc-2bb8-4651-ba70-7332b4eb1e00

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {V : Type} [AddCommGroup V] [Module F V] (H1 H2 : V → V → ℂ) (τ : F →+* ℂ)
    (a1 : ∀ x y z, H1 (x + y) z = H1 x z + H1 y z) (b1 : ∀ x y z, H1 x (y + z) = H1 x y + H1 x z)
    (r1 : ∀ s x y, H1 x (s • y) = τ s * H1 x y)
    (l1 : ∀ s x y, H1 (s • x) y = starRingEnd ℂ (τ s) * H1 x y)
    (a2 : ∀ x y z, H2 (x + y) z = H2 x z + H2 y z) (b2 : ∀ x y z, H2 x (y + z) = H2 x y + H2 x z)
    (r2 : ∀ s x y, H2 x (s • y) = τ s * H2 x y)
    (l2 : ∀ s x y, H2 (s • x) y = starRingEnd ℂ (τ s) * H2 x y)
    (hN : ∀ x, H1 x x = H2 x x) (s0 : F) (hs0 : starRingEnd ℂ (τ s0) ≠ τ s0) (x y : V) :
    H1 x y = H2 x y := by
  have hD : ∀ u v : V, H1 u v + H1 v u = H2 u v + H2 v u := by
    intro u v
    have e1 := hN (u + v)
    rw [a1, b1, b1, a2, b2, b2] at e1
    linear_combination e1 - hN u - hN v
  have h1 := hD x y
  have h2 := hD (s0 • x) y
  rw [l1, r1, l2, r2] at h2
  have h3 : (starRingEnd ℂ (τ s0) - τ s0) * (H1 x y - H2 x y) = 0 := by
    linear_combination h2 - τ s0 * h1
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) hs0
  · exact sub_eq_zero.1 h
end Formalism.HermiteSiegelSlopes
