-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_scale_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:29.546413+00:00
-- url     : https://prove2.me/submissions/9d06c835-7893-4c14-a80a-20923f9ac972

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_diagonal
import Theorems.Thm_Formalism_DivisionValues_indexChange_diagonal


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
theorem _root_.solution (v : HeightOneSpectrum R) (n : ℕ) {a : K} (ha : a ≠ 0) :
    lidx v.asIdeal (Submodule.span R (Set.range (Pi.basisFun K (Fin n))))
        (scG a (Submodule.span R (Set.range (Pi.basisFun K (Fin n))))) =
      (n : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
  have h := indexChange_diagonal v (fun _ : Fin n => a) (fun _ => ha) (Pi.basisFun K (Fin n))
    (Pi.basisFun K (Fin n)).linearIndependent
  rw [idxChange_act_diagonal, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow] at h
  rw [← h]
  congr 1
  unfold scG
  rw [Submodule.map_span, ← Set.range_comp]
  rfl
end Formalism.EigenvalueLevelCeiling
