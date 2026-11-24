-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:53.239301+00:00
-- url     : https://prove2.me/submissions/e2d300b7-cefe-4724-9bb3-231c6b3b85ab

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_span
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_mem_locP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (p : Ideal ℤ) [p.IsPrime] (hp : p = Ideal.span {3}) :
    (localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Submodule.mem_comap, Submodule.coe_subtype, exampleZ_mem_locP]
  obtain ⟨s, hs, hx⟩ := (exampleZ_mem_locP _ _ _).mp x.2
  obtain ⟨n, hn⟩ := (exampleZ_mem_one _).mp hx
  have h2 : (2 : ℤ) ∉ p := by
    rw [hp, Ideal.mem_span_singleton]; decide
  refine ⟨2 * s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim h2 hs,
    (exampleZ_mem_span _ _).mpr ⟨n, ?_⟩⟩
  push_cast
  rw [mul_assoc, ← hn]; ring
end Formalism.HermitianLatticesTheory
