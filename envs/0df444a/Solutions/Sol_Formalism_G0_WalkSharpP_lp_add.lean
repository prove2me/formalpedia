-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.lp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:46.813837+00:00
-- url     : https://prove2.me/submissions/c9b9962f-3f3e-462e-bb42-a3544c87fd40

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ}
namespace Formalism.G0.WalkSharpP
theorem _root_.solution (y : Fin V → Module.End R X) (hc : ∀ v w, Commute (y v) (y w))
    (l : List (Fin V)) (e₁ e₂ : Fin V → ℕ) :
    lp y l (fun u => e₁ u + e₂ u) = lp y l e₁ * lp y l e₂ := by

  induction l with
  | nil => simp [lp]
  | cons u l ih =>
    simp only [lp, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, pow_add]
    have hcomm : Commute (y u ^ e₂ u) ((l.map fun w => y w ^ e₁ w).prod) := by
      apply Commute.list_prod_right
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨w, _, rfl⟩ := hp
      exact (hc u w).pow_pow _ _
    calc y u ^ e₁ u * y u ^ e₂ u * ((l.map fun w => y w ^ e₁ w).prod * (l.map fun w => y w ^ e₂ w).prod)
        = y u ^ e₁ u * (y u ^ e₂ u * (l.map fun w => y w ^ e₁ w).prod) * (l.map fun w => y w ^ e₂ w).prod := by
          simp only [mul_assoc]
      _ = y u ^ e₁ u * ((l.map fun w => y w ^ e₁ w).prod * y u ^ e₂ u) * (l.map fun w => y w ^ e₂ w).prod := by
          rw [hcomm.eq]
      _ = y u ^ e₁ u * (l.map fun w => y w ^ e₁ w).prod * (y u ^ e₂ u * (l.map fun w => y w ^ e₂ w).prod) := by
          simp only [mul_assoc]
end Formalism.G0.WalkSharpP
