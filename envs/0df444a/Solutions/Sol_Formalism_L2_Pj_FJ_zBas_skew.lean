-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.zBas_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:46.795083+00:00
-- url     : https://prove2.me/submissions/d687e411-aa42-4d1b-8d9c-3aa5e0660051

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (h : ∃ bs, IsZBasis X cu bs) (k : Fin (nZ X ρ)) :
    IsSkew (zBas X cu k) := by
  have hs : LinearIndependent ℤ (zBas X cu) ∧
      ∀ β, β ∈ zGam X cu ↔ β ∈ Submodule.span ℤ (Set.range (zBas X cu)) := Classical.epsilon_spec h
  have hm : zBas X cu k ∈ zGam X cu := (hs.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
  exact hm.1
end Formalism.L2.Pj.FJ
