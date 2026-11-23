-- Prove2me | solution 1 for Formalism.UG.P.ind_biInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:54.758838+00:00
-- url     : https://prove2.me/submissions/627b5d25-2012-4845-a779-6a8175ce1f7a

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution (k : Type) [CommRing k] (K : Subgroup G) (T : Set G)
    (hT : ∀ a b : K, ∀ x : G, x ∈ T → (a : G) * x * b ∈ T) :
    IsBiInv K (T.indicator (1 : G → k)) := by
  unfold IsBiInv
  intro a b x
  by_cases hx : x ∈ T
  · simp [Set.indicator_apply, hx, hT a b x hx]
  · have h' : (a : G) * x * b ∉ T := by
      intro h
      apply hx
      have := hT a⁻¹ b⁻¹ _ h
      simpa [mul_assoc] using this
    simp [Set.indicator_apply, hx, h']
end Formalism.UG.P
