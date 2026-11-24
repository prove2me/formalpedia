-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.limit_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:38.687128+00:00
-- url     : https://prove2.me/submissions/d64a274f-ceae-4c4e-82a1-c9dd907825e5

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Theorems.Thm_Formalism_NG_IdemLiftAlt_map_mem_smul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
variable [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Module.Finite O A]
omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (a L : A) (n : ℕ)
    (hL : ∀ j : ℕ, aeval a (nP (n + j)) - L ∈ IsLocalRing.maximalIdeal O ^ j • (⊤ : Submodule O A))
    {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (φ : A →ₗ[O] M) (c : M)
    (hφ : ∀ k, φ (aeval a (nP k)) = c) : φ L = c := by
  set I := IsLocalRing.maximalIdeal O
  have h : φ L - c = 0 := by
    refine IsHausdorff.haus (inferInstance : IsHausdorff I M) _ (fun j => ?_)
    rw [SModEq.sub_mem, sub_zero]
    have e : φ L - c = -φ (aeval a (nP (n + j)) - L) := by rw [map_sub, hφ]; abel
    rw [e]
    refine Submodule.neg_mem _ ?_
    exact map_mem_smul_top _ φ (hL j)
  exact sub_eq_zero.1 h
end Formalism.NG.IdemLiftAlt
