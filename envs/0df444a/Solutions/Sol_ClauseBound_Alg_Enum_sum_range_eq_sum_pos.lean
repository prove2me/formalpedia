-- Prove2me | solution 1 for ClauseBound.Alg.Enum.sum_range_eq_sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:04.970232+00:00
-- url     : https://prove2.me/submissions/e0d00a17-05e7-4cf7-a6dd-bfe4ae322e51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_ClauseBound_Alg_Enum_pos_bijOn

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {g : ℕ}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (G : ℕ → ℕ) : ∑ j ∈ range (g * g), G j = ∑ p : Fin g × Fin g, G (pos p) :=
  (sum_nbij pos (fun p _ => pos_bijOn.mapsTo trivial) (fun p _ q _ h => pos_bijOn.injOn trivial trivial h)
    (fun j hj => by
      obtain ⟨p, _, e⟩ := pos_bijOn.surjOn hj
      exact ⟨p, mem_coe.2 (mem_univ p), e⟩) fun _ _ => rfl).symm
end ClauseBound.Alg.Enum
