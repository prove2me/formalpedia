-- Prove2me | solution 1 for Formalism.REAL.modularCharacter_eq_one_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:28.428489+00:00
-- url     : https://prove2.me/submissions/a972dc30-d45b-4cca-b23f-062bbed8d8ce

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Theorems.Thm_Formalism_REAL_map_mul_right_haar_modular_alt
import Theorems.Thm_Formalism_REAL_frobenius_ball_compact_pos_finite
import Theorems.Thm_Formalism_REAL_hermitian_small_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (g : UJ ε)
    (hk : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    modularCharacterAlt ε g = 1 := by
  obtain ⟨hc, hpos, hfin⟩ := frobenius_ball_compact_pos_finite ε
  set B := {g : UJ ε | hsG g ≤ (n : ℝ) + 1} with hB
  have hBm : MeasurableSet B := hc.isClosed.measurableSet
  have hpre : (fun x => x * g) ⁻¹' B = B := by
    ext x
    simp only [hB, Set.mem_preimage, Set.mem_ofPred_eq, hsG, Subgroup.coe_mul, Units.val_mul]
    rw [((hermitian_small_ball n ε).2 _ _ hk).1]
  have h1 := map_mul_right_haar_modular_alt ε g
  have h2 : (Measure.map (fun x => x * g) (muG ε)) B = muG ε B := by
    rw [Measure.map_apply (measurable_mul_const g) hBm, hpre]
  rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modularCharacterAlt ε g : ℝ≥0∞)) * muG ε B = 1 * muG ε B := by rw [h2, one_mul]
  rw [ENNReal.mul_left_inj hpos.ne' hfin.ne] at h3
  exact_mod_cast h3
end Formalism.REAL
