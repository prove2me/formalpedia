-- Prove2me | solution 1 for BookProof.YangMillsFriedrichs.weylOpDom_quadForm_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:38:44.578406+00:00
-- url     : https://prove2.me/submissions/72ff662e-bd46-43c1-a60a-9b9b5f53ed06

-- Generated from ChapterYangMillsFriedrichs.lean — solution of BookProof.YangMillsFriedrichs.weylOpDom_quadForm_inc
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.YangMillsFriedrichs




open BookProof.FarisLavine



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) (x : D) :
    quadForm (weylOp pi Bf) x
      = 1 / 2 * (∑ i, ‖((pi i x : D) : F)‖ ^ 2) + 1 / 2 * ∑ a, ‖((Bf a x : D) : F)‖ ^ 2 := by

  have hinner : (inner ℂ ((x : D) : F) (weylOp pi Bf x) : ℂ)
      = (((1 / 2 * (∑ i, ‖((pi i x : D) : F)‖ ^ 2)
          + 1 / 2 * ∑ a, ‖((Bf a x : D) : F)‖ ^ 2 : ℝ)) : ℂ) := by
    rw [weylOp_apply, inner_smul_right, inner_add_right, inner_sum, inner_sum,
      Finset.sum_congr rfl fun i _ => inner_sq_eq_normSq (hpi i) x,
      Finset.sum_congr rfl fun a _ => inner_sq_eq_normSq (hB a) x]
    push_cast
    ring
  rw [quadForm, hinner, Complex.ofReal_re]
