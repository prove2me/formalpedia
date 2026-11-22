-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Ent.det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:54.272313+00:00
-- url     : https://prove2.me/submissions/f01c872b-07c2-4b4b-abcb-54806b560bf1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_exists_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {m n o : Type*}
namespace Formalism.HermitianLattices.Ext.L3.HU
namespace Ent
theorem _root_.solution [Fintype n] [DecidableEq n] {M : Matrix n n K} (hM : Ent S M) : M.det ∈ S := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  have h := RingHom.map_det S.subtype M₀
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (M₀.det).2
end Ent
end Formalism.HermitianLattices.Ext.L3.HU
