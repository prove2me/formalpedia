-- Prove2me | solution 1 for Formalism.L2.Th1.H.KerPNonzero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:17.294678+00:00
-- url     : https://prove2.me/submissions/9710dc1c-5545-404c-802d-c0fa8779aec4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionFiltrationStable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_DiagonalIntegral
import Theorems.Thm_Formalism_L2_Th1_H_fundamentalDomainExists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (hD : DiagIntegral) : KerPNonzero := by
  intro V _ _ _ H Λ α hH hPos hL hS hC
  by_contra hne
  push_neg at hne
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨D, hD1, hD2, hD3, -⟩ :=
    fundamentalDomainExists V MeasureTheory.Measure.addHaar (Λ ⊓ Λ) (by rw [inf_idem]; exact hL)
  have hint := hD V MeasureTheory.Measure.addHaar H Λ Λ α hH hPos hL hS hS hC hC D hD1 hD2 0 (zero_mem _)
  simp [opU, hne] at hint
  have h0 : (MeasureTheory.Measure.addHaar D).toReal = 0 := by
    exact_mod_cast hint.symm
  linarith
end Formalism.L2.Th1.H
