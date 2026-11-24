-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.mO_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:35.945486+00:00
-- url     : https://prove2.me/submissions/2f4e7bc0-18dd-415e-830b-632c4352d514

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) : (1 : O) ∉ mO o O := by
  obtain ⟨l, hl⟩ := unram_one hU
  let J' : Ideal O :=
    { carrier := {x | ∀ y, l (y * x) ∈ IsLocalRing.maximalIdeal o}
      add_mem' := fun {a b} ha hb y => by
        rw [mul_add, map_add]; exact Ideal.add_mem _ (ha y) (hb y)
      zero_mem' := fun y => by rw [mul_zero, map_zero]; exact Ideal.zero_mem _
      smul_mem' := fun c x hx y => by
        rw [smul_eq_mul, ← mul_assoc]; exact hx (y * c) }
  have hle : mO o O ≤ J' := by
    rw [mO, Ideal.map_le_iff_le_comap]
    intro t ht y
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ht
  intro h1
  have := hle h1 1
  rw [mul_one, hl] at this
  exact (IsLocalRing.maximalIdeal.isMaximal o).ne_top ((Ideal.eq_top_iff_one _).2 this)
end Formalism.HermitianLatticeCounting.P.S4aux
