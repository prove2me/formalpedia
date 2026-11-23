-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.psiB_sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:23.88331+00:00
-- url     : https://prove2.me/submissions/a9018fe7-9d53-48c2-aa20-fb69deefabba

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (hψ : ∀ r ∈ R, ψ r = 1)
    (x : KR R) (hx : ∀ r : R, psiB R ψ hψ (r • x) = 1) : x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  have : a ∈ R := by
    rw [← hsd a]
    intro r hr
    have h1 := hx ⟨r, hr⟩
    rw [← Submodule.Quotient.mk_smul] at h1
    have h2 : psiKR R ψ (Submodule.Quotient.mk ((⟨r, hr⟩ : R) • a)) = 1 := h1
    rw [psiKR_mk R ψ hψ] at h2
    rw [mul_comm]
    exact h2
  exact ⟨⟨a, this⟩, rfl⟩
end Formalism.FourierDecayAlt.P.A5x2
