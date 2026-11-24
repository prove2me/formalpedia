-- Prove2me | solution 1 for Formalism.UG.P.map_mulVec_mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:58.817604+00:00
-- url     : https://prove2.me/submissions/968f6df7-f3b0-4c59-b5a1-0ee1bfaef7d1

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Theorems.Thm_P2M_Formalism_UG_P_mem_stdLat_iff__3723b4f8990e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (M : Matrix n n R) (x : n → A)
    (hx : x ∈ stdLat (n := n) (A := A) R) :
    (M.map (algebraMap R A)) *ᵥ x ∈ stdLat (n := n) (A := A) R := by
  rw [mem_stdLat_iff'] at hx ⊢
  choose y hy using hx
  have hxy : x = fun j => algebraMap R A (y j) := funext fun j => (hy j).symm
  subst hxy
  intro i
  refine ⟨(M *ᵥ y) i, ?_⟩

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
end Formalism.UG.P
