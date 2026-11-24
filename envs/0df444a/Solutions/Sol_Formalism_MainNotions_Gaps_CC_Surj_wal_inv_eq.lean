-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:00:33.843173+00:00
-- url     : https://prove2.me/submissions/758c4f18-e354-4599-9788-ebaa53875e4e

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


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
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (τ : A →+* A) (J Ji : Matrix n n A) (hJi : Ji * J = 1) (u : GL n A)
    (hu : u ∈ UJ τ J) :
    ((u⁻¹ : GL n A) : Matrix n n A) = Ji * cT τ (u : Matrix n n A) * J := by
  have h : cT τ (u : Matrix n n A) * J * (u : Matrix n n A) = J := hu
  have h2 : Ji * cT τ (u : Matrix n n A) * J * (u : Matrix n n A) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT τ _), h, hJi]
  calc ((u⁻¹ : GL n A) : Matrix n n A) = 1 * ((u⁻¹ : GL n A) : Matrix n n A) := (Matrix.one_mul _).symm
    _ = Ji * cT τ (u : Matrix n n A) * J * (u : Matrix n n A) * ((u⁻¹ : GL n A) : Matrix n n A) := by
        rw [h2]
    _ = Ji * cT τ (u : Matrix n n A) * J := by
        rw [Matrix.mul_assoc _ (u : Matrix n n A), Units.mul_inv, Matrix.mul_one]
end Formalism.MainNotions.Gaps.CC.Surj
