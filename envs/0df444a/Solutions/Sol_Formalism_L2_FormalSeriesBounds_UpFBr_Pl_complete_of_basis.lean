-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.complete_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:04.752145+00:00
-- url     : https://prove2.me/submissions/8a8563ab-1d8e-4034-85f1-874f5f2d321e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_mem_pow_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)
include β
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution [IsAdicComplete (Ideal.span {π}) Z] :
    IsAdicComplete (Ideal.span {algebraMap Z A π}) A where
  haus' := by
    intro x hx
    have h0 : ∀ i, β.repr x i = 0 := by
      intro i
      refine IsHausdorff.haus' (I := Ideal.span {π}) _ fun n => ?_
      rw [SModEq.sub_mem, sub_zero]
      have := hx n
      rw [SModEq.sub_mem, sub_zero] at this
      exact (mem_pow_iff π β n x).1 this i
    have : β.repr x = 0 := Finsupp.ext h0
    simpa using this
  prec' := by
    intro f hf
    have h1 : ∀ i, ∃ L : Z, ∀ n, β.repr (f n) i ≡ L [SMOD ((Ideal.span {π}) ^ n • (⊤ : Submodule Z Z))] := by
      intro i
      refine IsPrecomplete.prec' (I := Ideal.span {π}) (fun n => β.repr (f n) i) ?_
      intro m n hmn
      have := hf hmn
      rw [SModEq.sub_mem] at this ⊢
      have h2 := (mem_pow_iff π β m _).1 this i
      simpa using h2
    choose L hL using h1
    refine ⟨∑ i, L i • β i, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_iff π β]
    intro i
    have := hL i n
    rw [SModEq.sub_mem] at this
    have e : β.repr (∑ j, L j • β j) i = L i := by
      simp [Finsupp.single_apply]
    rw [map_sub, Finsupp.sub_apply, e]
    exact this
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
