-- Prove2me | solution 1 for Formalism.HN.le_of_imageLattice_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:29.503571+00:00
-- url     : https://prove2.me/submissions/552d31e1-bb19-4291-a332-199be8e068cc

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Theorems.Thm_Formalism_HN_satR_mem_zl


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
namespace Formalism.HN
theorem _root_.solution {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) (L N₁ N₂ : Submodule R V)
    (hinj : Set.InjOn ρ (L : Set V)) (h₁ : N₁ ≤ L) (h₂ : N₂ ≤ L) (h : zl ρ N₁ ≤ zl ρ N₂) :
    N₁ ≤ N₂ := by
  intro x hx
  have hx' : ρ x ∈ zl ρ N₂ :=
    h ((satR_mem_zl ρ N₁ (ρ x)).2 ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := (satR_mem_zl ρ N₂ (ρ x)).1 hx'
  have hxy : y = x := hinj (h₂ hy) (h₁ hx) hyx
  rw [← hxy]
  exact hy
end Formalism.HN
