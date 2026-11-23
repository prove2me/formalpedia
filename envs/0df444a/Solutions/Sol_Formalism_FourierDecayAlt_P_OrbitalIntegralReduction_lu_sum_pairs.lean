-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_sum_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:59.577802+00:00
-- url     : https://prove2.me/submissions/e04d8245-c283-4544-89b1-d46e980e4c91

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {n : ℕ} (j : Fin n) (g : Pr n → K) :
    ∑ p : Pr n, (if p.1.2 = j then g p else 0) =
      ∑ k : Fin n, if h : k < j then g ⟨(k, j), h⟩ else 0 := by
  classical
  let G : Fin n × Fin n → K := fun q => if h : q.1 < q.2 then (if q.2 = j then g ⟨q, h⟩ else 0) else 0
  have e0 : ∑ p : Pr n, (if p.1.2 = j then g p else 0) = ∑ p : Pr n, G p.1 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : p.1.1 < p.1.2 := p.2
    simp only [G, hp, dite_true]
  have e1 : ∑ p : Pr n, G p.1 = ∑ q : Fin n × Fin n, G q := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun q : Fin n × Fin n => q.1 < q.2)
      (p := fun q : Fin n × Fin n => q.1 < q.2) (by simp) G, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : q.1 < q.2
    · simp [h]
    · simp [G, h]
  rw [e0, e1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [G]
  · intro l _ hl
    simp only [G]
    split_ifs <;> rfl
  · simp
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
