-- Prove2me | solution 1 for Formalism.L2.LamCM.isAdicComplete_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:26:19.340681+00:00
-- url     : https://prove2.me/submissions/1b962289-19d7-4b39-b8f1-d0941f501135

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Theorems.Thm_Formalism_L2_LamCM_mem_smul_top_iff_repr
import Theorems.Thm_Formalism_L2_LamCM_mem_smul_top_self_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open Polynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (I : Ideal R) (b : Module.Basis ι R M) (h : IsAdicComplete I R) : IsAdicComplete I M := by

  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    simp only [map_sub, Finsupp.sub_apply, SModEq.sub_mem, mem_smul_top_self_iff]
  haveI := h
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    have h0 : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus' (I := I) (b.repr x i) fun n => by simpa using (key n x 0).1 (hx n) i
    exact b.repr.injective (Finsupp.ext fun i => by simpa using h0 i)
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
      IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have hr : b.repr (b.equivFun.symm L) i = L i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hr]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end Formalism.L2.LamCM
