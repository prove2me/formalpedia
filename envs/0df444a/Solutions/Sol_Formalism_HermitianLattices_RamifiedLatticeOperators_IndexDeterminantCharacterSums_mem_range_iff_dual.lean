-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.mem_range_iff_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:33.408894+00:00
-- url     : https://prove2.me/submissions/40cb6dec-47d1-4d21-81fd-c4175c4db9cf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (A : Matrix m k F) (v : m → F) :
    v ∈ LinearMap.range A.mulVecLin ↔ ∀ w : m → F, Aᵀ *ᵥ w = 0 → w ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ w hw
    rw [Matrix.mulVecLin_apply, dotProduct_mulVec, ← Matrix.mulVec_transpose, hw, zero_dotProduct]
  · intro h
    by_contra hv
    obtain ⟨φ, hφv, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    set w : m → F := fun i => φ (fun j => if i = j then 1 else 0) with hwdef
    have hφw : ∀ y, φ y = w ⬝ᵥ y := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ φ y, dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_eq_mul, mul_comm]
    apply hφv
    rw [hφw]
    apply h
    funext j
    rw [Matrix.mulVec_transpose]
    have hj : φ (A *ᵥ Pi.single j 1) = 0 := by
      have h1 : A *ᵥ Pi.single j 1 ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
      have h2 : φ (A *ᵥ Pi.single j 1) ∈ (LinearMap.range A.mulVecLin).map φ :=
        Submodule.mem_map_of_mem h1
      rw [hφ] at h2
      exact (Submodule.mem_bot F).mp h2
    rw [hφw, dotProduct_mulVec, dotProduct_single, mul_one] at hj
    simpa using hj
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
