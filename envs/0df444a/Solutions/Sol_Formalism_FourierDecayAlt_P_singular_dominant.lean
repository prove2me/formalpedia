-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.singular_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:56:33.713802+00:00
-- url     : https://prove2.me/submissions/63d20c97-d666-4079-8fd6-7b306e507444

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors
attribute [local instance 100] LieRing.ofAssociativeRing
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.SingDom := by
  intro V _ _ _ n E ν v hE hv hv0 a b hab
  obtain ⟨hd, hr⟩ := hv
  have hab' : a ≠ b := ne_of_lt hab
  by_cases h0 : E a a - E b b = 0
  · refine ⟨0, ?_⟩
    have h1 : (E a a - E b b) v = 0 := by rw [h0]; rfl
    rw [LinearMap.sub_apply, hd, hd, ← sub_smul] at h1
    simpa [hv0] using h1
  · have e0 := hE a b b a
    have e1 := hE a a a b
    have e2 := hE b b a b
    have e3 := hE a a b a
    have e4 := hE b b b a
    simp [hab', hab'.symm] at e0 e1 e2 e3 e4
    have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
      { h_ne_zero := h0
        lie_e_f := by rw [Ring.lie_def, e0]
        lie_h_e_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E a b - E a b * (E a a - E b b)
              = (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
            _ = 2 • E a b := by rw [e1, e2]; abel
        lie_h_f_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E b a - E b a * (E a a - E b b)
              = (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
            _ = -(2 • E b a) := by rw [e3, e4]; abel }
    have pv : t.HasPrimitiveVectorWith v (ν a - ν b) :=
      { ne_zero := hv0
        lie_h := by
          show (E a a - E b b) v = (ν a - ν b) • v
          rw [LinearMap.sub_apply, hd, hd, sub_smul]
        lie_e := by
          show E a b v = 0
          exact hr a b hab }
    exact pv.exists_nat
end Formalism.FourierDecayAlt.P
