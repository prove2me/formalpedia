-- Prove2me | solution 1 for Bl.FunctionAtZero.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:07.259801+00:00
-- url     : https://prove2.me/submissions/583014cb-ac05-4b06-a38c-6359f46e826f

import Mathlib
import Definitions.Def_Lemmata_FunctionAtZero_FZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.FunctionAtZero
private lemma f_zero (f : Real → Complex) (hmul : ∀ s t, f (s + t) = f s * f t)
    (hn : ∀ s, ‖f s‖ = 1) : f 0 = 1 := by
  have h := hmul 0 0
  rw [add_zero] at h
  have h0 : f 0 ≠ 0 := by
    intro h'
    have := hn 0
    rw [h', norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ h0 (h.symm.trans (mul_one (f 0)).symm)
end Bl.FunctionAtZero
end

set_option autoImplicit false
open Bl Bl.FunctionAtZero
namespace Bl.FunctionAtZero
theorem _root_.solution :
  ∀ (f : Real → Complex),
  Continuous.{0, 0} f →
    (∀ (s t : Real), Eq.{1} (f (HAdd.hAdd.{0, 0, 0} s t)) (HMul.hMul.{0, 0, 0} (f s) (f t))) →
      (∀ (s : Real), Eq.{1} (Norm.norm.{0} (f s)) 1) →
        Exists.{1} fun (b : Real) ↦
          ∀ (s : Real),
            Eq.{1} (f s) (Complex.exp (HMul.hMul.{0, 0, 0} (Complex.ofReal (HMul.hMul.{0, 0, 0} b s)) Complex.I)) := by
  intro f hf hmul hn
  have h0 := f_zero f hmul hn
  let F : C(Real, Circle) := ⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩
  have hF : ∀ s, ((F s : Circle) : Complex) = f s := fun s => rfl
  obtain ⟨g, ⟨hg0, hgF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0
    (Circle.ext (by rw [Circle.coe_exp, hF, h0]; simp))
  have key : ∀ s, Complex.exp (↑(g s) * Complex.I) = f s := fun s => by
    rw [← Circle.coe_exp, ← hF]
    exact congrArg (fun z : Circle => (z : Complex)) (congrFun hgF s)
  have hadd : ∀ s t, g (s + t) = g s + g t := by
    intro s t
    have := Circle.isCoveringMap_exp.eq_of_comp_eq (g₁ := fun s => g (s + t))
      (g₂ := fun s => g s + g t)
      (g.continuous.comp (continuous_id.add continuous_const)) (g.continuous.add continuous_const)
      (by
        funext x
        apply Circle.ext
        simp only [Function.comp_apply, Circle.coe_exp, Complex.ofReal_add, add_mul,
          Complex.exp_add, key, hmul]) 0 (by simp [hg0])
    exact congrFun this s
  let G : Real →+ Real := AddMonoidHom.mk' g hadd
  have hlin : ∀ s, g s = s * g 1 := by
    intro s
    have := map_real_smul G (by exact g.continuous) s 1
    simpa [G] using this
  refine ⟨g 1, fun s => ?_⟩
  rw [← key s, hlin s, mul_comm s]
end Bl.FunctionAtZero
