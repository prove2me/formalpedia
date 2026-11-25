-- Prove2me | solution 1 for Formalism.HN.ex_Psat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:58:37.777273+00:00
-- url     : https://prove2.me/submissions/7e0de584-19c7-49e4-8bf2-9314e5352da4

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_zl_id
import Theorems.Thm_Formalism_HN_PolygonExample_coord1
import Theorems.Thm_Formalism_HN_PolygonExample_Px_le

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
theorem _root_.solution : IsSat ρx Lx Px := by
  refine ⟨Px_le, ?_⟩
  rw [zl_id, zl_id]
  refine ⟨Px_le, fun x hx hxs => ?_⟩
  rw [Lx, Submodule.mem_span_pair] at hx
  obtain ⟨m, n, rfl⟩ := hx
  rw [Px, Submodule.span_span_of_tower, Submodule.mem_span_singleton] at hxs
  obtain ⟨c, hc⟩ := hxs
  have h2 : (2 : ℝ) * n = 0 := by
    rw [← coord1 m n, ← hc]
    simp [e₀]
  have hn : n = 0 := by
    have : (n : ℝ) = 0 := by linarith
    exact_mod_cast this
  subst hn
  simp only [zero_smul, add_zero]
  exact Submodule.smul_mem _ m (Submodule.mem_span_singleton_self e₀)
end Formalism.HN
