-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.curve_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:27.951537+00:00
-- url     : https://prove2.me/submissions/b353596e-018d-440f-8d71-f586ce09dfa9

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
theorem _root_.solution (a b c d : Fin k) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)
      ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d) 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
    ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)).const_add ((1 : Matrix (Fin k) (Fin k) ℂ) c d)
end CompanionTheory.D.Inhab.HWRep
