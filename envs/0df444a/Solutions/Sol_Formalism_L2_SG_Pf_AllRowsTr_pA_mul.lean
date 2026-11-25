-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsTr.pA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:38.449583+00:00
-- url     : https://prove2.me/submissions/ec017ff9-cc6d-4c39-b898-6e18abda8248

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsTr_pA_coeff
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin


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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
namespace Formalism.L2.SG.Pf.AllRowsTr
theorem _root_.solution (f g : ∀ i, MonoidAlgebra ℂ (G i)) : pA f * pA g = pA (fun i => f i * g i) := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin, pA_coeff]
  simp only [pA_coeff, coeff_mul_fin]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.prod_mul_distrib]
  rfl
end Formalism.L2.SG.Pf.AllRowsTr
