-- Prove2me | solution 1 for Formalism.GM.M.pre_span_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:59.142839+00:00
-- url     : https://prove2.me/submissions/bee2f32f-c02e-46ee-87c4-bcc2bfc898cd

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_zmon_eq
import Theorems.Thm_Formalism_GM_M_gens_mem_SSZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)
namespace Formalism.GM.M
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (hL : D.LevelOK j jp) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℤ_[p] (Bset (p := p) D j jp)) : pre D j jp * Q ∈ D.SSZ p (r := r) := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    refine gens_mem_SSZ D j jp hL _ ⟨y, hy, g, hg, ?_⟩
    rw [pre, ← zmon_eq]; ring
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
end Formalism.GM.M
