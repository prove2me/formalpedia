-- Prove2me | solution 1 for Formalism.HF.P.dirDensity_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:59.034455+00:00
-- url     : https://prove2.me/submissions/ebb4f1ae-a233-46f5-8ad8-788ee45575be

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution {S T : Set ℕ} {δ : ℝ} (h : DirDensity S δ)
    (hST : ∀ p : ℕ, p.Prime → (p ∈ S ↔ p ∈ T)) : DirDensity T δ := by
  have hset : {p : ℕ | p.Prime ∧ p ∈ S} = {p : ℕ | p.Prime ∧ p ∈ T} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun ⟨hp, hs⟩ => ⟨hp, (hST p hp).1 hs⟩, fun ⟨hp, ht⟩ => ⟨hp, (hST p hp).2 ht⟩⟩
  unfold DirDensity at h ⊢
  rw [← hset]
  exact h
end Formalism.HF.P
