-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.small_irreducible_representation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:30.308685+00:00
-- url     : https://prove2.me/submissions/83ed15b9-9ed1-4ac2-a8a2-a07cc529a1cc

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_std_eq_zero
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
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : SmallPI := by
  intro V _ _ W Y _ hYW E hE M hM a ha w hw
  let b : Fin M → Module.End ℂ Y := fun i =>
    (E * a i).restrict (p := Y) (q := Y) fun y hy => hE _ (ha i y (hYW hy))
  have hb : ∀ l : List (Fin M), word E (l.map a) w = (((l.map b).prod ⟨E w, hE w hw⟩ : Y) : V) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.map_cons, word_cons, Module.End.mul_apply, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rfl
  have hdim : Module.finrank ℂ (Module.End ℂ Y) < M := by
    rw [Module.finrank_linearMap, ← sq]; exact hM
  have h0 := congrArg (fun T : Module.End ℂ Y => ((T ⟨E w, hE w hw⟩ : Y) : V)) (std_eq_zero hdim b)
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.zero_apply, Submodule.coe_zero] at h0
  rw [← h0, stdPoly, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e1 : (List.ofFn fun i => a (π i)) = (List.ofFn π).map a := by rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i => b (π i)) = (List.ofFn π).map b := by rw [List.map_ofFn]; rfl
  rw [e1, e2, Module.End.mul_apply, Module.End.mul_apply, hb, Module.End.intCast_apply, Module.End.intCast_apply,
    Submodule.coe_smul_of_tower]
end CompanionTheory.D.gk.admitted
