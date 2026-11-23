-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.corner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:25.795924+00:00
-- url     : https://prove2.me/submissions/dd9a7c59-3727-4b90-b412-afd83b964175

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_gap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sq_lemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πl πj : Ty P) (h1 : Up P l π πl) (h2 : Up P j π πj) :
    Real.sqrt (Nrm P j πl) * Real.sqrt (Nrm P l π) * (rho P π j - rho P π l - 1) =
      Real.sqrt (Nrm P l πj) * Real.sqrt (Nrm P j π) * (rho P π j - rho P π l + 1) ∧
    Real.sqrt (Nrm P l πj) * Real.sqrt (Nrm P j πl) = Real.sqrt (Nrm P j π) * Real.sqrt (Nrm P l π) := by
  have hd := gap P hP l j hl hj hjl π πl πj h1 h2
  have hp : rho P π j - rho P π l + 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have hm : rho P π j - rho P π l - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have hp' : rho P π l - rho P π j + 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have hm' : rho P π l - rho P π j - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have s1 := nrm_shift P l j hl hj hjl π πj h2 hp hm
  have s2 := nrm_shift P j l hj hl hjl.symm π πl h1 hp' hm'
  exact sq_lemma _ _ _ _ _ (by linear_combination (-1) * s2) s1 hd
end Formalism.FourierDecayAlt.P.Mx4
