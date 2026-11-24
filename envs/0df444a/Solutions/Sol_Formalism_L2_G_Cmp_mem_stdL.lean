-- Prove2me | solution 1 for Formalism.L2.G.Cmp.mem_stdL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:56.622326+00:00
-- url     : https://prove2.me/submissions/f7f3a732-706b-4449-8863-a0ee0e794b13

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (x : Fin k → Qq) : x ∈ stdL (k := k) (Qq := Qq) W ↔ ∀ a, x a ∈ (algebraMap W Qq).range := by
  show x ∈ Submodule.span W (Set.range fun c : Fin k => fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      intro a
      by_cases h : a = c
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩
    | zero => intro a; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro a
      obtain ⟨u, hu⟩ := hy a
      obtain ⟨v, hv⟩ := hz a
      exact ⟨u + v, by simp [hu, hv]⟩
    | smul w y _ hy =>
      intro a
      obtain ⟨u, hu⟩ := hy a
      exact ⟨w * u, by simp [hu, Algebra.smul_def]⟩
  · intro h
    simp only [RingHom.mem_range] at h
    choose w hw using h
    have e : x = ∑ c, w c • (fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) := by
      ext i
      simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def, hw]
    rw [e]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
end Formalism.L2.G.Cmp
