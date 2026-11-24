-- Prove2me | solution 1 for Formalism.L2.G.Cmp.hform_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:57:40.723794+00:00
-- url     : https://prove2.me/submissions/9de59bf3-3da8-48b8-8b95-64c96ab35bba

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsHypA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {T K : Type} [CommRing T] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
  (φ : T ≃+* K × K) (σ : T →+* T) (hσ : ∀ t, φ (σ t) = swapR K (φ t)) (Ov : Subring K) (S : Subring T)
  (hS : ∀ t, t ∈ S ↔ (φ t).1 ∈ Ov ∧ (φ t).2 ∈ Ov) (J : Matrix n n T) (Λ : Submodule S (n → T))
  (hΛ : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform σ J z y ∈ S)
include hσ
namespace Formalism.L2.G.Cmp
theorem _root_.solution (z y : n → T) :
    (φ (hform σ J z y)).2 = ∑ i, ∑ j, (φ (z i)).1 * (φ (J i j)).2 * (φ (y j)).2 := by
  simp [hform, map_sum, map_mul, Prod.snd_sum, hσ, swapR]
end Formalism.L2.G.Cmp
