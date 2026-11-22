-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.psd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:39.82127+00:00
-- url     : https://prove2.me/submissions/20e0e5f6-dfca-4d15-893b-db4b4586706d

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
variable {α X : Type}
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution {F : Finset α} {k k' : α → α → ℂ} (h : A5.IsPSD F k) (h' : A5.IsPSD F k') :
    A5.IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (h a).1, (h' a).1]
  exact ⟨by simp, add_nonneg (h a).2 (h' a).2⟩
end Formalism.FourierDecayAlt.P.Jx9
