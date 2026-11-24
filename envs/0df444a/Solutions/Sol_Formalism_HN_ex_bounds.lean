-- Prove2me | solution 1 for Formalism.HN.ex_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:22.302449+00:00
-- url     : https://prove2.me/submissions/a713b888-0d92-40f7-867d-a6158857c154

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_one_le_norm
import Theorems.Thm_Formalism_HN_PolygonExample_discrete_of_le
import Theorems.Thm_Formalism_HN_PolygonExample_rk_Lx
import Theorems.Thm_Formalism_HN_PolygonExample_covol_Lx
import Theorems.Thm_Formalism_F_covolAntiSameRank
import Theorems.Thm_Formalism_F_covolBasic
import Theorems.Thm_Formalism_F_shortVector


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
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2
namespace Formalism.HN
theorem _root_.solution (N : Submodule ℤ E2) (hN : N ≤ Lx) :
    Formalism.F.rk N ≤ 2 ∧ Formalism.F.deg N ≤ 0 ∧ (Formalism.F.rk N = 2 → Formalism.F.deg N ≤ - Real.log 2) := by
  haveI hd : DiscreteTopology N := discrete_of_le N hN
  haveI : DiscreteTopology Lx := discrete_of_le Lx le_rfl
  haveI : Module.Finite ℤ Lx := by
    rw [Lx]
    exact Module.Finite.span_of_finite ℤ (Set.toFinite _)
  have hrk : Formalism.F.rk N ≤ 2 := by
    exact (Submodule.finrank_mono hN).trans rk_Lx.le
  have h2 : Formalism.F.rk N = 2 → 2 ≤ Formalism.F.covol N := by
    intro h
    have := Formalism.F.covolAntiSameRank E2 N Lx inferInstance hN (by rw [h, rk_Lx])
    rwa [covol_Lx] at this
  have h1 : 1 ≤ Formalism.F.covol N := by
    by_cases hb : N = ⊥
    · subst hb
      rw [(Formalism.F.covolBasic E2).1]
    obtain ⟨v, hv, hv0, hvn⟩ := Formalism.F.shortVector E2 N hd hb
    have hv1 := one_le_norm (hN hv) hv0
    obtain h | h | h : Formalism.F.rk N = 0 ∨ Formalism.F.rk N = 1 ∨ Formalism.F.rk N = 2 := by omega
    · rw [h] at hvn
      simp at hvn
      exact absurd hvn hv0
    · rw [h] at hvn
      simp at hvn
      linarith
    · linarith [h2 h]
  refine ⟨hrk, ?_, fun h => ?_⟩
  · simp only [Formalism.F.deg]
    linarith [Real.log_nonneg h1]
  · simp only [Formalism.F.deg]
    linarith [Real.log_le_log (by norm_num) (h2 h)]
end Formalism.HN
