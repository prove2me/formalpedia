-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.alg_CT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:45:15.708404+00:00
-- url     : https://prove2.me/submissions/6b8a7d74-f603-4f5f-91dc-9b17d94200c4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Theorems.Thm_Formalism_L2_Pj_GenSect_isAlgebraic_map_adjoin
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_not


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω)
    (hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀)) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) := by
  have hC : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C ω : CT Ω D j₀) := by
    intro ω
    have h1 := isAlgebraic_map_adjoin (IsScalarTower.toAlgHom K Ω (CT Ω D j₀)) (C_injective _ _) _
      (halg ω)
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h1
    rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, -⟩
    exact hr k
  constructor
  intro c
  have hc : c ∈ Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪ Set.range (C : Ω → CT Ω D j₀)) := by
    induction c using MvPolynomial.induction_on with
    | C a => exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
    | add p r hp hr => exact add_mem hp hr
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩))
  have h0 : IsAlgebraic (Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪
      Set.range (C : Ω → CT Ω D j₀))) c :=
    isAlgebraic_algebraMap (⟨c, hc⟩ : Algebra.adjoin K _)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h0
  rintro y ⟨hy | ⟨ω, rfl⟩, -⟩
  · obtain ⟨q, rfl⟩ := hy
    have hq : (X q : CT Ω D j₀) ∈ Algebra.adjoin K (Set.range (gs (D := D) x j₀)) :=
      Algebra.subset_adjoin ⟨q.1, by rw [gs, if_neg q.2, xv_of_not q.2]⟩
    exact isAlgebraic_algebraMap (⟨X q, hq⟩ : Algebra.adjoin K _)
  · exact hC ω
end Formalism.L2.Pj.GenSect
