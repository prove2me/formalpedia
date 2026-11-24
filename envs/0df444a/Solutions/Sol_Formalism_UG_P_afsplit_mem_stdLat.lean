-- Prove2me | solution 1 for Formalism.UG.P.afsplit_mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:07.657359+00:00
-- url     : https://prove2.me/submissions/2f005724-bc50-4526-ab02-efc93534bed9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (S : Subring A) (x : n → A) :
    x ∈ stdLat (n := n) (A := A) S ↔ ∀ i, x i ∈ S := by
  constructor
  · intro h i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ((Submodule.mem_pi.mp h) i (Set.mem_univ i))
    rw [← hy]
    exact y.2
  · intro h
    exact Submodule.mem_pi.mpr fun i _ => LinearMap.mem_range.mpr ⟨⟨x i, h i⟩, rfl⟩
end Formalism.UG.P
