-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_perm_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:20.505641+00:00
-- url     : https://prove2.me/submissions/3742b1aa-714e-4fe2-81af-88fb0e4a3d77

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_antisymmetrizedProduct_adjacent_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (π : Equiv.Perm (Fin n))
    (arg : Fin n → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ π) = doublyAntisymmetrizedProduct E arg := by
  cases n with
  | zero =>
    have h : arg ∘ π = arg := funext fun k => k.elim0
    rw [h]
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    revert arg
    induction hπ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro arg
      exact antisymmetrizedProduct_adjacent_swap E i arg
    | one =>
      intro arg
      rfl
    | mul x y _ _ hx hy =>
      intro arg
      show doublyAntisymmetrizedProduct E ((arg ∘ x) ∘ y) = _
      rw [hy (arg ∘ x), hx arg]
end Formalism.HermitianLatticeCounting.P
