-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.H_lev_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:34.032588+00:00
-- url     : https://prove2.me/submissions/f14c01ce-65d2-47b3-938a-c94b64223524

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
  have hi := i.isLt
  have hj := j.isLt
  have hij : levPos k 1 r' i = levPos k 1 r' j ↔ i = j := by
    rw [Fin.ext_iff, Fin.ext_iff, lev_val, lev_val]
    exact ⟨fun h => by omega, fun h => by omega⟩
  have e1 : ((levPos k 1 r' i).val < 1 + r' ∧
      (levPos k 1 r' i).val + (levPos k 1 r' j).val = 2 * (1 + r') + k) ↔
      (i.val < r' ∧ i.val + j.val = 2 * r' + k) := by
    rw [lev_val, lev_val]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩⟩
  have e2 : ((levPos k 1 r' j).val < 1 + r' ∧
      (levPos k 1 r' i).val + (levPos k 1 r' j).val = 2 * (1 + r') + k) ↔
      (j.val < r' ∧ i.val + j.val = 2 * r' + k) := by
    rw [lev_val, lev_val]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩⟩
  have e3 : (1 + r' ≤ (levPos k 1 r' i).val ∧ (levPos k 1 r' i).val ≤ 1 + r' + k ∧
      levPos k 1 r' i = levPos k 1 r' j) ↔ (r' ≤ i.val ∧ i.val ≤ r' + k ∧ i = j) := by
    rw [hij, lev_val]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨by omega, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨by omega, by omega, h3⟩⟩
  have e4 : (levPos k 1 r' i).val = 1 + r' + k ↔ i.val = r' + k := by
    rw [lev_val]
    exact ⟨fun h => by omega, fun h => by omega⟩
  exact if_congr e1 rfl (if_congr e2 rfl (if_congr e3 (if_congr e4 rfl rfl) rfl))
end Formalism.FourierDecayAlt.P.B2x5
