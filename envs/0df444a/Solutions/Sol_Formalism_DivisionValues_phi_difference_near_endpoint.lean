-- Prove2me | solution 1 for Formalism.DivisionValues.phi_difference_near_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:31.419422+00:00
-- url     : https://prove2.me/submissions/e845e69e-4fab-4456-91ee-19187006ee13

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_phi_lipschitz_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain Finset
noncomputable section
namespace Formalism.DivisionValues
namespace PlaceSumConjugation
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Star
end PlaceSumConjugation
open PlaceSumConjugation
private theorem phpair_lemma (u u' A La lo D : ℝ) (hu : 1 ≤ u) (hu' : 1 ≤ u') (hA : u ≤ A)
    (hA' : u' ≤ A) (hLa : La = Real.log A) (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La)
    (hD : |u - u'| ≤ D) :
    |(Formalism.LatticeIndexTer.ph u - u * lo) - (Formalism.LatticeIndexTer.ph u' - u' * lo)| ≤ 2 * (D * La) := by
  have hP := phi_lipschitz_bound u u' A hu hu' hA hA'
  rw [← hLa] at hP
  have hY : |(u - u') * lo| ≤ |u - u'| * La := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlo (abs_nonneg _)
  have hDL : |u - u'| * La ≤ D * La := mul_le_mul_of_nonneg_right hD hLa0
  rw [abs_le] at hP hY ⊢
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hY1, hY2⟩ := hY
  constructor <;> linarith
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution (w a Δ A La lo y y' : ℝ) (hw : 1 ≤ w) (ha : 0 ≤ a) (hy : a ≤ y ∧ y ≤ a + Δ)
    (hy' : a ≤ y' ∧ y' ≤ a + Δ) (hA : y + w ≤ A) (hA' : y' + w ≤ A) (hLa : La = Real.log A)
    (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La) :
    |(Formalism.LatticeIndexTer.ph (y + w) - (y + w) * lo) - (Formalism.LatticeIndexTer.ph (y' + w) - (y' + w) * lo)| ≤
      2 * (Δ * La) := by
  have hD : |y + w - (y' + w)| ≤ Δ := by
    rw [show y + w - (y' + w) = y - y' by ring, abs_le]
    constructor <;> linarith [hy.1, hy.2, hy'.1, hy'.2]
  exact phpair_lemma (y + w) (y' + w) A La lo Δ (by linarith [hy.1]) (by linarith [hy'.1])
    hA hA' hLa hLa0 hlo hD
end Formalism.DivisionValues
