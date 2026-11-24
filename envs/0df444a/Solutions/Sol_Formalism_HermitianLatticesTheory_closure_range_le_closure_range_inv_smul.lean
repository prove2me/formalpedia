-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.closure_range_le_closure_range_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:51.140327+00:00
-- url     : https://prove2.me/submissions/de0c56b4-ce86-40eb-a8ae-9ff7c2bab9fe

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {V : Type*} [AddCommGroup V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {K : Type*} [Field K] [CharZero K] [Module K V] {n : ℕ} (u : Fin n → V)
    (e : ℤ) (he : e ≠ 0) :
    AddSubgroup.closure (Set.range u) ≤
      AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hx : u i = e • (((e : K)⁻¹) • u i) := by
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]
  have hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) :=
    AddSubgroup.subset_closure ⟨i, rfl⟩
  rw [SetLike.mem_coe, hx]
  exact AddSubgroup.zsmul_mem _ hm e
end Formalism.HermitianLatticesTheory
