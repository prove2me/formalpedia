-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.apply_stdPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:47.034478+00:00
-- url     : https://prove2.me/submissions/ef3cc7aa-0649-4491-ba62-bdcb46d44d64

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
namespace CompanionTheory.D.gk.admitted.PrismTransfer
theorem _root_.solution {G V : Type} [AddCommGroup V] [Module ℂ V] (τ : G → Module.End ℂ V) (E : Module.End ℂ V)
    {M : ℕ} (g : Fin M → G) (ℓ : V →ₗ[ℂ] ℂ) (u : V) :
    ℓ (stdPoly E (fun i => τ (g i)) u) = ∑ π : Equiv.Perm (Fin M),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ℓ (word E ((List.ofFn fun i => g (π i)).map τ) u) := by
  simp only [stdPoly, LinearMap.sum_apply, map_sum, List.map_ofFn, Function.comp_def, Module.End.mul_apply,
    Module.End.intCast_apply, map_zsmul, zsmul_eq_mul]
end CompanionTheory.D.gk.admitted.PrismTransfer
