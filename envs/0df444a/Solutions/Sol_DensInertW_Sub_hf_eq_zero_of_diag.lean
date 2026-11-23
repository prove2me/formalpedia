-- Prove2me | solution 1 for DensInertW.Sub.hf_eq_zero_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:29.402692+00:00
-- url     : https://prove2.me/submissions/fc59d0c6-148d-4814-bc69-f1c15501fd8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Theorems.Thm_DensInertW_Sub_hf_add_right
import Theorems.Thm_DensInertW_Sub_hf_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0)
    (W : Submodule L (Fin n → L)) (h0 : ∀ v ∈ W, hf q M v v = 0) :
    ∀ x ∈ W, ∀ y ∈ W, hf q M x y = 0 := by
  intro x hx y hy
  have key : ∀ c : L, c * hf q M x y + (c * hf q M x y) ^ q = 0 := by
    intro c
    have h1 := h0 (c • x + y) (W.add_mem (W.smul_mem c hx) hy)
    rw [hf_add_left, hf_add_right hadd, hf_add_right hadd, h0 _ (W.smul_mem c hx), h0 y hy,
      hf_symm hadd hinv hM (c • x) y, hf_smul_left] at h1
    linear_combination h1
  by_contra hz
  obtain ⟨c, hc⟩ := htr _ hz
  exact hc (key c)
end DensInertW.Sub
