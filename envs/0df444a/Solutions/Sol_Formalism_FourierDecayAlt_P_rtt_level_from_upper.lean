-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rtt_level_from_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:39.113464+00:00
-- url     : https://prove2.me/submissions/ab0a504f-4dbd-4522-ac16-c80204a0824d

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormLevel_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QxPIRttLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_ll_tL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.RTTLevelFromUpper := by
  intro hU hLT hGI hFF _ k r i
  induction i using Fin.cases with
  | succ l => exact hU k r l
  | zero =>
    intro Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
    obtain ⟨π₁, π₁', D₁, f, hw, hw', hD₁, hf, hfJ⟩ := hFF Wp Wq k r z z' π π' D hz hz' hD J hJ
    have key : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2),
        Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z') ⟨1, by omega⟩
                  Y p q (Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z')
                    ⟨1, by omega⟩ Y' p' q' f) (Formalism.QuantumDeterminants.ιLev k 1 r g) =
          Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y p q (Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y' p' q' J) g := by
      intro Y Y' p q p' q'
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hg.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y p q).loc _ _ ?_ g hg
      intro x hx
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y' p' q').loc _ _ ?_ x hx
      intro y hy
      exact (hfJ y hy.1.1).2
    have hιg : Formalism.QuantumDeterminants.ιLev k 1 r g ∈ Formalism.FourierDecayAlt.Q.Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁ := by
      refine ⟨?_, (hfJ g hg.1.1).1.mpr hg.2⟩
      rw [hGI k 1 r]
      exact ⟨g, hg.1.1, rfl⟩
    have h1 : Formalism.FourierDecayAlt.Q.RTTAt k (1 + r) ⟨1, by omega⟩ := hU k (1 + r) ⟨0, by omega⟩
    have h := h1 Wp Wq _ _ π₁ π₁' D₁ hw hw' hD₁ f hf _ hιg u v a b c d
    simp only [key] at h
    exact h
end Formalism.FourierDecayAlt.P
