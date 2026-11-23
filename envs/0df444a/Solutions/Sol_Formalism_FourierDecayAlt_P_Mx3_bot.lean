-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:26.21819+00:00
-- url     : https://prove2.me/submissions/e8dfcaed-afba-4345-9cc4-bb814060a449

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_val_congr

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
theorem _root_.solution (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π' π) :
    rho P π l = P.lo l := by
  have hl' := Finset.mem_Icc.1 hl
  by_contra hne
  apply h
  have hpos : 0 < ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) := by
    by_contra hge
    apply hne
    have h3 : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) = 0 := by omega
    rw [rho_eq P π l hl', h3]; simp
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(π i : ℕ) - 1, ?_⟩ else π i, ?_⟩
  · have := (π i).2; omega
  · intro i
    by_cases hi : (i : ℕ) + 1 = l
    · have : i = ⟨l - 1, by omega⟩ := Fin.ext (by simp; omega)
      have h5 := val_congr P π _ _ this
      simp [hi]; omega
    · simp [hi]
end Formalism.FourierDecayAlt.P.Mx3
