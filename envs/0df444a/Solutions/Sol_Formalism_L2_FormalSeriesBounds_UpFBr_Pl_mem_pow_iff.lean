-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.mem_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:48.579828+00:00
-- url     : https://prove2.me/submissions/de2457f7-c42f-4a7e-96e8-84bb5a21aee5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis

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
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {algebraMap Z A π}) ^ n • (⊤ : Submodule A A)) ↔
      ∀ i, β.repr x i ∈ ((Ideal.span {π}) ^ n • (⊤ : Submodule Z Z)) := by
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨β.repr y i, ?_⟩
    rw [← map_pow, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · intro h
    choose d hd using h
    refine ⟨∑ i, d i • β i, ?_⟩
    conv_lhs => rw [← β.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, mul_smul, Algebra.smul_def (π ^ n), map_pow]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
