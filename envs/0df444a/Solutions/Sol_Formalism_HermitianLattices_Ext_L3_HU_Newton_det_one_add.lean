-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Newton.det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:07.937659+00:00
-- url     : https://prove2.me/submissions/72a9b033-075c-4fee-8ed1-f9a7f8b20be1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
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
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
open Formalism.HermitianLattices.Ext.L3.HU.Newton
namespace Formalism.HermitianLattices.Ext.L3.HU.Newton
theorem _root_.solution (hϖ : ϖ ∈ S) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  set w : S := ⟨ϖ, hϖ⟩ with hw
  obtain ⟨c, h⟩ : ∃ c : S, (1 + w • M₀).det = 1 + M₀.trace * w + c * w ^ 2 :=
    ⟨_, Matrix.det_one_add_smul w M₀⟩
  refine ⟨((M₀.trace + c * w : S) : K), Subtype.prop _, ?_⟩
  have key : (1 + ϖ • M₀.map S.subtype) = S.subtype.mapMatrix (1 + w • M₀) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hw]
    · simp [Matrix.one_apply_ne hij, hw]
  have h2 : (1 + M₀.trace * w + c * w ^ 2 : S) = 1 + w * (M₀.trace + c * w) := by ring
  rw [key, ← RingHom.map_det, h, h2]
  simp [hw]
end Formalism.HermitianLattices.Ext.L3.HU.Newton
