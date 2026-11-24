-- Prove2me | solution 1 for Formalism.HN.shiftInv_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:26.300816+00:00
-- url     : https://prove2.me/submissions/5a735f88-6aeb-4981-a438-1ebf2a3a0e83

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance

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
universe u v w w₂
namespace Formalism.HN
theorem _root_.solution {R : Type u} {V : Type v} {E : Type w} {E₂ : Type w₂} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [FiniteDimensional ℝ E₂] (h1 : MuChar.{u, v, w}) (h1' : MuChar.{u, v, w₂})
    (ρ : V →+ E) (ρ₂ : V →+ E₂) (L : Submodule R V) (c : ℝ) (hL : IsLat ρ L)
    (hL₂ : IsLat ρ₂ L)
    (hsh : ∀ N : Submodule R V, N ≤ L → rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N + c * rk ρ N)
    (hL0 : L ≠ ⊥) : muMax ρ₂ L = muMax ρ L + c ∧ muMin ρ₂ L = muMin ρ L + c := by
  obtain ⟨hmax, hmin, -, -, -⟩ := h1 R V E ρ L hL hL0
  obtain ⟨hmax₂, hmin₂, -, -, -⟩ := h1' R V E₂ ρ₂ L hL₂ hL0
  have hrL := (hsh L le_rfl).1
  have hdL := (hsh L le_rfl).2
  constructor
  · apply le_antisymm
    · rw [hmax₂]
      intro N hN
      rw [(hsh N hN).1, (hsh N hN).2]
      have := (hmax (muMax ρ L)).1 le_rfl N hN
      linarith
    · have key : muMax ρ L ≤ muMax ρ₂ L - c := by
        rw [hmax]
        intro N hN
        have := (hmax₂ (muMax ρ₂ L)).1 le_rfl N hN
        rw [(hsh N hN).1, (hsh N hN).2] at this
        linarith
      linarith
  · apply le_antisymm
    · have key : muMin ρ₂ L - c ≤ muMin ρ L := by
        rw [hmin]
        intro N hN
        have := (hmin₂ (muMin ρ₂ L)).1 le_rfl N hN
        rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2] at this
        linarith
      linarith
    · rw [hmin₂]
      intro N hN
      rw [hrL, (hsh N hN).1, hdL, (hsh N hN).2]
      have := (hmin (muMin ρ L)).1 le_rfl N hN
      linarith
end Formalism.HN
