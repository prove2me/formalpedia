-- Prove2me | solution 1 for Formalism.L2.NG.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:13:24.323087+00:00
-- url     : https://prove2.me/submissions/9c931bcc-a676-425e-9964-1e7f814afd3e

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
import Theorems.Thm_Formalism_L2_NG_exists_level_multiset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
namespace Formalism.L2.NG
theorem _root_.solution (f : (ZMod p)[X]) (h0 : f.coeff 0 ≠ 0) : ∃ d, LevelOf f d := by
  apply exists_level_multiset
  intro h
  have h1 := (Polynomial.mem_roots'.mp h).2
  rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map] at h1
  exact h0 ((map_eq_zero _).mp h1)
end Formalism.L2.NG
