-- Prove2me | solution 1 for Formalism.L2.Col.HPsym_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:36.379573+00:00
-- url     : https://prove2.me/submissions/44629ce9-ebe5-45f1-8f73-57b19a2db781

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]
namespace Formalism.L2.Col
theorem _root_.solution (k rS : ℕ) : ((HPsym κ n k rS : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) =
    uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) := by
  ext M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq]
  have hU := Set.ext_iff.mp (uniUT_full_eq (n := n) (κ := κ)) M
  simp only [SetLike.mem_coe, uSet, Set.mem_setOf_eq] at hU
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨d, o⟩ := hU.mp h1
    refine ⟨d, fun i j hne hP => ?_⟩
    by_cases hlt : i < j
    · have hh : rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k := by
        by_contra hc
        exact hP ⟨hlt, hc⟩
      exact h2 i j hh.1 hh.2.1 hh.2.2
    · exact o i j hne hlt
  · rintro ⟨d, o⟩
    show M ∈ uniUT n κ n [] ∧ ∀ i j : Fin n, rS ≤ i.val → i.val < rS + k → j.val = rS + k → (M : Matrix (Fin n) (Fin n) κ) i j = 0
    refine ⟨hU.mpr ⟨d, fun i j hne hlt => o i j hne (fun h => hlt h.1)⟩, fun i j h1 h2 h3 => ?_⟩
    have hlt : i < j := by
      show i.val < j.val
      omega
    exact o i j (ne_of_lt hlt) (fun h => h.2 ⟨h1, h2, h3⟩)
end Formalism.L2.Col
