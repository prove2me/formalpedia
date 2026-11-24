-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_le_Q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:56.018806+00:00
-- url     : https://prove2.me/submissions/fccacd18-a644-4d81-97b8-704b4c506a7d

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
    (e : ℤ) (he : e ≠ 0) (x : V) (hx : e • x ∈ AddSubgroup.closure (Set.range u)) :
    x ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  let f : V →+ V :=
    { toFun := fun v => ((e : K)⁻¹) • v
      map_zero' := smul_zero _
      map_add' := fun a b => smul_add _ a b }
  have hfx : f (e • x) = x := by
    show ((e : K)⁻¹) • (e • x) = x
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ heK, one_smul]
  have hle : AddSubgroup.closure (Set.range u) ≤
      (AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)).comap f := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    have hm : ((e : K)⁻¹) • u i ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) :=
      AddSubgroup.subset_closure ⟨i, rfl⟩
    exact hm
  have h1 := hle hx
  rw [AddSubgroup.mem_comap, hfx] at h1
  exact h1
end Formalism.HermitianLatticesTheory
