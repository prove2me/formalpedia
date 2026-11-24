-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.ortho_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:29.814384+00:00
-- url     : https://prove2.me/submissions/62c4f35f-55dd-4391-b46e-f40ae521fa80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_ortho_fam
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_linInd

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
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Herm4
theorem _root_.solution (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = finrank K V) :
    ∃ b : Basis n K V, ∀ i j, i ≠ j → h (b i) (b j) = 0 := by
  rcases isEmpty_or_nonempty n with hne | hne
  · have h0 : finrank K V = 0 := by rw [← hn, Fintype.card_eq_zero]
    exact ⟨basisOfFinrankZero h0, fun i => isEmptyElim i⟩
  · obtain ⟨v, hv0, hv⟩ := H.ortho_fam (finrank K V) le_rfl
    let e : n ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq hn
    have hli : LinearIndependent K (v ∘ e) :=
      H.linInd (v ∘ e) (fun i => hv0 _) (fun i j hij => hv _ _ (fun h' => hij (e.injective h')))
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hn, fun i j hij => ?_⟩
    simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply]
    exact hv _ _ (fun h' => hij (e.injective h'))
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
