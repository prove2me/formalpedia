-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Cayley.exists_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:44.965117+00:00
-- url     : https://prove2.me/submissions/7103b638-fc71-4c01-8ba6-f4e81360fcb7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsInvOneAdd
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
namespace Formalism.HermitianLattices.Ext.L3.HU
namespace Cayley
theorem _root_.solution (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  let ϖ₀ : S := ⟨ϖ, hS.mem⟩
  refine ⟨((Matrix.trace M₀ + (Matrix.det (1 + (Polynomial.X : Polynomial S) •
      M₀.map Polynomial.C)).divX.divX.eval ϖ₀ * ϖ₀ : S) : K), SetLike.coe_mem _, ?_⟩
  have hmap : (1 : Matrix n n K) + ϖ • M₀.map S.subtype = S.subtype.mapMatrix (1 + ϖ₀ • M₀) := by
    ext i j
    by_cases h : i = j <;> simp [h, ϖ₀]
  rw [hmap, ← RingHom.map_det, Matrix.det_one_add_smul ϖ₀ M₀]
  simp only [map_add, map_mul, map_one, map_pow, Subring.coe_subtype]
  simp only [Subring.coe_add, Subring.coe_mul, ϖ₀]
  ring
end Cayley
end Formalism.HermitianLattices.Ext.L3.HU
