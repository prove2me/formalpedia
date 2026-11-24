-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.card_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:32.372857+00:00
-- url     : https://prove2.me/submissions/39e0dfeb-baff-4937-8bd5-4428834953f0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes
import Theorems.Thm_Formalism_HermitianLattices_RamifiedLatticeOperators_IndexDeterminantCharacterSums_card_fiber_prod

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
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module F V] [Finite V] [AddCommGroup W]
    [Module F W] (L : V →ₗ[F] W) (ψ : V →ₗ[F] F) (s : V) (hs : L s = 0) (hψ : ψ s ≠ 0) (c : F) :
    Fintype.card F * Nat.card {x : V // L x = 0 ∧ ψ x = c} = Nat.card {x : V // L x = 0} := by
  have hfib : ∀ c : F, Nat.card {x : V // L x = 0 ∧ ψ x = c} =
      Nat.card {x : V // L x = 0 ∧ ψ x = 0} := fun c =>
    card_fiber_prod L ψ ((c / ψ s) • s) 0 c (by rw [map_smul, hs, smul_zero])
      (by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hψ])
  have hsig : Nat.card {x : V // L x = 0} = ∑ c : F, Nat.card {x : V // L x = 0 ∧ ψ x = c} := by
    rw [← Nat.card_sigma (α := F) (β := fun c => {x : V // L x = 0 ∧ ψ x = c})]
    exact Nat.card_congr
      { toFun := fun x => ⟨ψ x.1, x.1, x.2, rfl⟩
        invFun := fun y => ⟨y.2.1, y.2.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => by rcases y with ⟨c, x, h1, rfl⟩; rfl }
  rw [hsig, Finset.sum_congr rfl (fun c _ => hfib c), hfib c, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
