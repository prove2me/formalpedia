-- Prove2me | solution 1 for Formalism.HN.duality_muMax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:14.242842+00:00
-- url     : https://prove2.me/submissions/236fe423-4795-4972-8d0a-54411a75b518

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_basic
import Theorems.Thm_Formalism_HN_duality_ne_bot
import Theorems.Thm_Formalism_HN_duality_compl
import Theorems.Thm_Formalism_HN_duality_zl_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u
namespace Formalism.HN
theorem _root_.solution (h1 : MuChar.{0, u, u}) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : L ≠ ⊥) :
    muMax (AddMonoidHom.id E) (dualZ L) = - muMin (AddMonoidHom.id E) L := by
  obtain ⟨hDd, hDr, hDdeg, hDD⟩ := duality_basic L
  have hD0 := duality_ne_bot L hL
  have hlat : ∀ M : Submodule ℤ E, DiscreteTopology M → IsLat (AddMonoidHom.id E) M := by
    intro M hM
    unfold IsLat
    refine ⟨fun x _ y _ h => by simpa using h, ?_⟩
    rw [duality_zl_id]
    exact hM
  have hA := (h1 ℤ E E (AddMonoidHom.id E) (dualZ L) (hlat _ hDd) hD0).1
  have hB := (h1 ℤ E E (AddMonoidHom.id E) L (hlat _ inferInstance) hL).2.1
  have key : ∀ θ : ℝ, muMax (AddMonoidHom.id E) (dualZ L) ≤ θ ↔
      -θ ≤ muMin (AddMonoidHom.id E) L := by
    intro θ
    rw [hA θ, hB (-θ)]
    simp only [deg, rk, duality_zl_id]
    have := hDd
    constructor
    · intro h N hN
      obtain ⟨M, hM, hr, hd⟩ := duality_compl L N hN
      have hMd := h M hM
      have hr' : (Formalism.F.rk M : ℝ) + Formalism.F.rk N = Formalism.F.rk L := by
        exact_mod_cast hr
      have hc : (Formalism.F.rk M : ℝ) = Formalism.F.rk L - Formalism.F.rk N := by
        linarith
      rw [hc] at hMd
      rw [neg_mul]
      linarith
    · intro h M hM
      obtain ⟨N, hN, hr, hd⟩ := duality_compl (dualZ L) M hM
      rw [hDD] at hN
      have hNd := h N hN
      have hr' : (Formalism.F.rk N : ℝ) + Formalism.F.rk M = Formalism.F.rk L := by
        rw [← hDr]
        exact_mod_cast hr
      have hc : (Formalism.F.rk M : ℝ) = Formalism.F.rk L - Formalism.F.rk N := by
        linarith
      rw [hc]
      rw [neg_mul] at hNd
      linarith
  apply le_antisymm
  · exact (key _).mpr (neg_neg _).le
  · have h2 := (key _).mp le_rfl
    linarith
end Formalism.HN
