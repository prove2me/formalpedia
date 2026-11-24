-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:22.271099+00:00
-- url     : https://prove2.me/submissions/65918188-6469-431a-8aec-8c0010372fd5

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
    AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) ≤
      (AddSubgroup.closure (Set.range u)).comap (zsmulAddGroupHom e) := by
  have heK : (e : K) ≠ 0 := Int.cast_ne_zero.mpr he
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  have hx : (zsmulAddGroupHom e : V →+ V) (((e : K)⁻¹) • u i) = u i := by
    show e • (((e : K)⁻¹) • u i) = u i
    rw [← Int.cast_smul_eq_zsmul K, smul_smul, mul_inv_cancel₀ heK, one_smul]
  rw [hx]
  exact AddSubgroup.subset_closure ⟨i, rfl⟩
end Formalism.HermitianLatticesTheory
