-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gnExt_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:39.249732+00:00
-- url     : https://prove2.me/submissions/07b979af-b1af-48d1-8fbe-c8b4b76d2594

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (v : {i // p i} → ℂ) (i : ι) :
    (gnExt p *ᵥ v) i = if h : p i then v ⟨i, h⟩ else 0 := by
  simp only [Matrix.mulVec, _root_.dotProduct, gnExt]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp
    · intro b _ hb
      have hne : i ≠ b.val := fun e => hb (Subtype.ext e.symm)
      simp [hne]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro j _
    have hne : i ≠ j.val := fun e => h (by rw [e]; exact j.property)
    simp [hne]
end Formalism.QuantumDeterminants
