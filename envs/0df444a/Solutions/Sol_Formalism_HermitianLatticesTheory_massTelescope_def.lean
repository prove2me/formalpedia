-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:30.601781+00:00
-- url     : https://prove2.me/submissions/696db585-ca42-4a36-9577-452b13b059e3

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_form_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_trace_pos
import Theorems.Thm_Formalism_HermitianLatticesTheory_massTelescope_trace_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hCM : IsCMUnram K) (n : ℕ) (x : Fin n → K) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (massTelescope_form K n x x) := by
  rw [massTelescope_form_apply, map_sum]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  exact Finset.sum_pos' (fun j _ => massTelescope_trace_nonneg K hCM (x j))
    ⟨i, Finset.mem_univ _, massTelescope_trace_pos K hCM (x i) hi⟩
end Formalism.HermitianLatticesTheory
