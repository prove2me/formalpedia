-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsTr.tau_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:58:32.829108+00:00
-- url     : https://prove2.me/submissions/a4daf5bd-1cdd-4a04-a0ec-d405d127001d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_coeff


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
theorem _root_.solution (x : MonoidAlgebra ℂ G) :
    (conjA x * x).coeff 1 = ((∑ h : G, Complex.normSq (x.coeff h) : ℝ) : ℂ) := by
  rw [coeff_mul_fin, Complex.ofReal_sum]
  simp only [conjA_coeff, mul_one]
  exact Fintype.sum_equiv (Equiv.inv G) _ _
    (fun h => by rw [Equiv.inv_apply, Complex.star_def, mul_comm, Complex.mul_conj])
end Formalism.L2.SG.Pf.AllRowsTr
