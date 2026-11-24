-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:26.943174+00:00
-- url     : https://prove2.me/submissions/3bf1af3c-8a1a-4383-9b83-a65651525730

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_fin
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_lidx_via
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (p : Ideal R) [p.IsPrime] (W : Submodule K V) (A B C : Submodule R V)
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) (hB : B.FG ∧ Submodule.span K (B : Set V) = W)
    (hC : C.FG ∧ Submodule.span K (C : Set V) = W) :
    lidx p A C = lidx p A B + lidx p B C := by
  have hD : ∀ X : Submodule R V, Submodule.span K (X : Set V) = W → X ≤ locS R⁰ (A ⊓ B ⊓ C) := by
    intro X hX
    rw [locBasic_locS_inf, locBasic_locS_inf]
    exact le_inf (le_inf (idxRules_le_locS hX hA.2) (idxRules_le_locS hX hB.2))
      (idxRules_le_locS hX hC.2)
  have hAD := idxRules_fin p A _ hA.1 (hD A hA.2)
  have hBD := idxRules_fin p B _ hB.1 (hD B hB.2)
  have hCD := idxRules_fin p C _ hC.1 (hD C hC.2)
  rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
      hAD hCD,
    indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
      hBD hCD]
  ring
end Formalism.EigenvalueLevelCeiling
