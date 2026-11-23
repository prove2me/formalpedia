-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_mem_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:04.48766+00:00
-- url     : https://prove2.me/submissions/8778861d-2853-46a3-8bb8-2ac725292b2e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ

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
theorem _root_.solution (p : Ideal ℤ) [p.IsPrime] (L : Submodule ℤ ℚ) (x : ℚ) :
    x ∈ localization₂ p L ↔ ∃ s : ℤ, s ∉ p ∧ (s : ℚ) * x ∈ L := by
  unfold localization₂ locS
  change (∃ s ∈ p.primeCompl, s • x ∈ L) ↔ _
  simp [zsmul_eq_mul, Ideal.primeCompl]
end Formalism.HermitianLatticesTheory
