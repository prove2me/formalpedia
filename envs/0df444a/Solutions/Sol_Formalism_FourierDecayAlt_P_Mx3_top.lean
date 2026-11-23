-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:08.140796+00:00
-- url     : https://prove2.me/submissions/0b78408c-8cb3-4501-a1dd-2108598360ca

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_val_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_wid_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π π') :
    rho P π l = P.hi l := by
  have hl' := Finset.mem_Icc.1 hl
  have e : l - 1 + 1 = l := by omega
  by_contra hne
  apply h
  have hlt : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) < P.wid l := by
    by_contra hge
    apply hne
    have h2 := (π ⟨l - 1, by omega⟩).2
    simp only [e] at h2
    have h3 : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) = P.wid l := by omega
    rw [rho_eq P π l hl', h3, wid_eq P hP l hl]; ring
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(π i : ℕ) + 1, ?_⟩ else π i, ?_⟩
  · have : i = ⟨l - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [val_congr P π _ _ this, hi]; omega
  · intro i
    by_cases hi : (i : ℕ) + 1 = l
    · simp [hi]
    · simp [hi]
end Formalism.FourierDecayAlt.P.Mx3
