-- Prove2me | solution 1 for Formalism.GM.badCrit_goodCount_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:11.155515+00:00
-- url     : https://prove2.me/submissions/d517127c-3f1a-4017-9418-747cc8b8ddcc

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Theorems.Thm_Formalism_GM_badCrit_be_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
namespace Formalism.GM
theorem _root_.solution (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ)
    [Module.Finite ℤ_[p] L] :
    BddAbove {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} := by
  refine ⟨Module.finrank ℤ_[p] L, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hli : LinearIndependent ℤ_[p] (fun i => (⟨x i, hx i⟩ : L)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (fun v : L => be (v : Vs) (y i)) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, LinearMap.sum_apply,
      Submodule.coe_zero, map_zero, LinearMap.zero_apply] at h1
    simp only [badCrit_be_smul_left, hxy, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have hp : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    exact PadicInt.ext (((mul_eq_zero.1 h1).resolve_right hp).trans PadicInt.coe_zero.symm)
  simpa using hli.fintype_card_le_finrank
end Formalism.GM
