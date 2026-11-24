-- Prove2me | solution 1 for Formalism.GM.M.memV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:59.401798+00:00
-- url     : https://prove2.me/submissions/54da4b00-4bd1-401f-ac94-8c997a9729bc

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_gens_sub

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) :
    ∃ Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp), v = pre D j jp * Q := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := gens_sub D j jp x hx
    exact ⟨b, Submodule.subset_span hb, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, rfl⟩ := hx
    obtain ⟨Q', hQ', rfl⟩ := hy
    exact ⟨Q + Q', Submodule.add_mem _ hQ hQ', by rw [mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨Q, hQ, rfl⟩ := hx
    exact ⟨c • Q, Submodule.smul_mem _ c hQ, by rw [mul_smul_comm]⟩
end Formalism.GM.M
