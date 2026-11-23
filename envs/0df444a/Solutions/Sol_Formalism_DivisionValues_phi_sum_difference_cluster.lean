-- Prove2me | solution 1 for Formalism.DivisionValues.phi_sum_difference_cluster
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:31.643829+00:00
-- url     : https://prove2.me/submissions/d4996988-5ce5-4e81-9229-da9541584acc

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
theorem _root_.solution (n : ℕ) (w Sc A La lo : ℝ) (c c' : Fin n → ℝ) (hw : 1 ≤ w) (hA : w + Sc ≤ A)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ Sc) (hc' : ∀ i, 0 ≤ c' i ∧ c' i ≤ Sc) (hLa : La = Real.log A)
    (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La) :
    |(∑ i, Formalism.LatticeIndexTer.ph (w + c i) - (∑ i, (w + c i)) * lo) -
      (∑ i, Formalism.LatticeIndexTer.ph (w + c' i) - (∑ i, (w + c' i)) * lo)| ≤ 2 * ((n : ℝ) * Sc * La) := by
  have hterm : ∀ i, |(Formalism.LatticeIndexTer.ph (w + c i) - (w + c i) * lo) -
      (Formalism.LatticeIndexTer.ph (w + c' i) - (w + c' i) * lo)| ≤ 2 * (Sc * La) := by
    intro i
    apply phpair_lemma (w + c i) (w + c' i) A La lo Sc (by linarith [(hc i).1])
      (by linarith [(hc' i).1]) (by linarith [(hc i).2]) (by linarith [(hc' i).2]) hLa hLa0 hlo
    rw [show w + c i - (w + c' i) = c i - c' i by ring, abs_le]
    constructor <;> linarith [(hc i).1, (hc i).2, (hc' i).1, (hc' i).2]
  calc |(∑ i, Formalism.LatticeIndexTer.ph (w + c i) - (∑ i, (w + c i)) * lo) -
        (∑ i, Formalism.LatticeIndexTer.ph (w + c' i) - (∑ i, (w + c' i)) * lo)|
      = |∑ i, ((Formalism.LatticeIndexTer.ph (w + c i) - (w + c i) * lo) -
        (Formalism.LatticeIndexTer.ph (w + c' i) - (w + c' i) * lo))| := by
        congr 1; simp only [Finset.sum_sub_distrib, Finset.sum_mul]
    _ ≤ ∑ i, |(Formalism.LatticeIndexTer.ph (w + c i) - (w + c i) * lo) -
        (Formalism.LatticeIndexTer.ph (w + c' i) - (w + c' i) * lo)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * (Sc * La) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 2 * ((n : ℝ) * Sc * La) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
end Formalism.DivisionValues
