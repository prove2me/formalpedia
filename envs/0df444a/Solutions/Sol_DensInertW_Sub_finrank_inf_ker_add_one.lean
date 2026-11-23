-- Prove2me | solution 1 for DensInertW.Sub.finrank_inf_ker_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:34.116643+00:00
-- url     : https://prove2.me/submissions/53882cfb-06c4-4ebb-a139-31bbbf943bec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne

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
theorem _root_.solution (W : Submodule L (Fin n → L)) (f : (Fin n → L) →ₗ[L] L)
    (u : Fin n → L) (hu : u ∈ W) (hfu : f u ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker f) + 1 = finrank L ↥W := by
  have hsurj : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun a => ⟨(a / f u) • u, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu]
  have hr : finrank L (LinearMap.range f) = 1 := by
    rw [hsurj, finrank_top, Module.finrank_self]
  have hk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, Module.finrank_fin_fun] at hk
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    refine eq_top_iff.mpr fun v _ => Submodule.mem_sup.mpr
      ⟨(f v / f u) • u, W.smul_mem _ hu, v - (f v / f u) • u, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu, sub_self]
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top, Module.finrank_fin_fun] at h
  omega
end DensInertW.Sub
