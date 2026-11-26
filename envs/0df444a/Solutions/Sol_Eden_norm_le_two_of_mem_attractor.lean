-- Prove2me | solution 1 for Eden.norm_le_two_of_mem_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:36.353661+00:00
-- url     : https://prove2.me/submissions/a4c2aa82-3db0-4571-83e1-22661c36f78a

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
import Theorems.Thm_Eden_norm_sq_phaseSpace

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {p : PhaseSpace} (hp : p ∈ attractor) :
    ‖p‖ ≤ 2 := by
  have hn := norm_sq_phaseSpace p
  rcases hp with ⟨h₁, h₂, h₄⟩
  rw [h₄] at hn
  nlinarith [norm_nonneg p]
end Eden
