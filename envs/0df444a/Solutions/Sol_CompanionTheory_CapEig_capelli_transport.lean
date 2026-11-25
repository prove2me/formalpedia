-- Prove2me | solution 1 for CompanionTheory.CapEig.capelli_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:59.842437+00:00
-- url     : https://prove2.me/submissions/cecc8b01-d5a4-4a3a-a14f-9cc164062be4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Theorems.Thm_Formalism_FourierDecayAlt_P_contractions_covariant
import Theorems.Thm_Formalism_QuantumDeterminants_io_gl
import Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_repr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open CompanionTheory CompanionTheory.CapEig
namespace CompanionTheory.CapEig
theorem _root_.solution : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hsm hg
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have h1 := ioh_qminor_rep (ioh_repr (ε := ε) (E := E) P Q) id id u hx _ hg'
  have h2 := io_qminor_rep id id u hx _ hg'
  have hc := (Formalism.FourierDecayAlt.P.contractions_covariant (Module.End ℂ (ioS ε E)) n (ioE ε E) P Q (io_gl ε E)
    hQP hPQ u 0 0 0 0).1
  unfold capelliH capelli qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, h1, h2]
  exact congrArg (fun T : Module.End ℂ (ioS ε E) => (T x).1 ⟨_, hg'⟩) hc
end CompanionTheory.CapEig
