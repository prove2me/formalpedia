-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsTr.tau_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:38:14.153308+00:00
-- url     : https://prove2.me/submissions/bd655ed6-aa21-4db5-93b5-74634df9bcc0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_tau_normSq
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsTr
open Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.SG.Pf.AllRowsTr
theorem _root_.solution (a e : MonoidAlgebra ℂ G) (ha : a * a = a) (hsa : conjA a = a) (he : e * e = e)
    (hc : ∀ y, e * y = y * e) (hse : conjA e = e) :
    (a * e).coeff 1 = ((∑ h : G, Complex.normSq ((a * e).coeff h) : ℝ) : ℂ) := by
  have hx : conjA (a * e) * (a * e) = a * e := by
    rw [conjA_mul, hse, hsa, mul_assoc, ← mul_assoc a a e, ha, ← mul_assoc, hc a, mul_assoc, he]
  rw [← tau_normSq (a * e), hx]
end Formalism.L2.SG.Pf.AllRowsTr
