-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.hasDerivAt_curve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:42.278069+00:00
-- url     : https://prove2.me/submissions/afbcc74c-4149-4ed1-92c4-b35379bcc56d

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)
namespace CompanionTheory.D.Inhab.HWRep
theorem _root_.solution (γ : ℝ → Matrix (Fin k) (Fin k) ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ a b, HasDerivAt (fun t => γ t a b) (Y a b) 0) (v : R.I → ℂ) :
    HasDerivAt (fun t => R.ρ (γ t) *ᵥ v) (R.D Y *ᵥ v) 0 := by
  have hγ' : HasDerivAt (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) (fun a b => Y a b) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hγ a b
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.mul_const ?_ _
  have hd := (R.diff (one' k) (by show (1 : Matrix (Fin k) (Fin k) ℂ).det ≠ 0; simp) i j).hasFDerivAt
  have e : one' k = (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) 0 := by
    funext a b; simp [h0, one']
  have hd' := hd.restrictScalars ℝ
  rw [e] at hd'
  have := hd'.comp_hasDerivAt (0 : ℝ) hγ'
  rw [← e] at this
  exact this
end CompanionTheory.D.Inhab.HWRep
