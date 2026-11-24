-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedConj0Pf.int_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:49:09.947841+00:00
-- url     : https://prove2.me/submissions/d91a117e-4502-4adc-bd33-c77203c0407d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_charP_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedConj0Pf
theorem _root_.solution (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (z : ℤ) :
    (z : 𝓞 I.E) ∈ w.asIdeal ↔ (p : ℤ) ∣ z := by
  haveI := charP_res I w p hp hcard
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
  exact CharP.intCast_eq_zero_iff _ p z
end Formalism.L2.SG.Pf.RedConj0Pf
