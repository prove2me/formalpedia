-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:29.93607+00:00
-- url     : https://prove2.me/submissions/b49e8b8c-19ea-46ee-a10b-6621862f7c73

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

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
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {X : Type} (A B : Finset X) (R : X → X → Prop) [∀ z, DecidablePred (R z)] (F : X → ℝ)
    (nb : X → ℕ) (h1 : ∀ z ∈ A, ∃ z' ∈ B, R z z')
    (h2 : ∀ z ∈ A, ∀ z' ∈ B, R z z' → (B.filter (R z)).card = nb z') :
    ∑ z ∈ A, F z = ∑ z ∈ A, ∑ z' ∈ B.filter (R z), F z / nb z' := by
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨z0, hz0, hR0⟩ := h1 z hz
  have hpos : 0 < (B.filter (R z)).card := Finset.card_pos.2 ⟨z0, Finset.mem_filter.2 ⟨hz0, hR0⟩⟩
  rw [Finset.sum_congr rfl (fun z' hz' => by
    rw [← h2 z hz z' (Finset.mem_filter.1 hz').1 (Finset.mem_filter.1 hz').2] :
      ∀ z' ∈ B.filter (R z), F z / nb z' = F z / ((B.filter (R z)).card : ℝ)),
    Finset.sum_const, nsmul_eq_mul]
  have : ((B.filter (R z)).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp
end Formalism.HermitianLatticeCounting.P.S4aux
