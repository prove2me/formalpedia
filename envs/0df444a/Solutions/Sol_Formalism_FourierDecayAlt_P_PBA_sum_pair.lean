-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.sum_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:33.381906+00:00
-- url     : https://prove2.me/submissions/f98733d0-0abf-4ccc-b70e-af0fe7c2ca9c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {W : Type} (s t : Finset W) (a b f g : W → ℝ) (hb : ∑ y ∈ t, b y = 1)
    (ha : ∑ x ∈ s, a x = 1) :
    ∑ x ∈ s ×ˢ t, a x.1 * b x.2 * ((f x.1 + g x.2) / 2) =
      ((∑ x ∈ s, a x * f x) + ∑ y ∈ t, b y * g y) / 2 := by
  have key : ∀ x, ∑ y ∈ t, a x * b y * ((f x + g y) / 2) =
      (a x * f x + a x * ∑ y ∈ t, b y * g y) / 2 := by
    intro x
    have split : ∀ y, a x * b y * ((f x + g y) / 2) =
        (a x * f x / 2) * b y + (a x / 2) * (b y * g y) := by
      intro y; ring
    simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_product]
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ha]
  ring
end Formalism.FourierDecayAlt.P.PBA
