-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:51.200554+00:00
-- url     : https://prove2.me/submissions/e60f249f-589c-490f-b878-e1d09362bb03

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {A : ℝ} {m : ℕ} {v' : List (Mat k r)} (hv' : ∀ X ∈ v', unitLie k r X) {F : Mat k r → E}
    {c : ℝ} (hF : CCle A (m + v'.length) F c) : CCle A m (Rw v' F) c := by
  obtain ⟨hc, hb⟩ := hF
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · have hw : ∀ x ∈ wR v', inLie k r x.2 := by
      intro x hx
      simp only [wR, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv' X hX).1
    have hc' : CkOn ((m : ℕ∞) + ((wR v').length : ℕ∞)) (GV k r) F := by
      have e : (((m + v'.length : ℕ)) : ℕ∞) = (m : ℕ∞) + ((wR v').length : ℕ∞) := by simp [wR]
      rw [← e]; exact hc
    rw [← Dw_wR]
    exact CkOn_Dw hw hc'
  · have e : dLR u v (Rw v' F) = dLR u (v ++ v') F := by
      show u.foldr LdV (v.foldr RdV (v'.foldr RdV F)) = u.foldr LdV ((v ++ v').foldr RdV F)
      rw [List.foldr_append]
    rw [e]
    refine hb u (v ++ v') hu (fun X hX => ?_) (by simp only [List.length_append]; omega) g hg
    rcases List.mem_append.mp hX with h | h
    · exact hv X h
    · exact hv' X h
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
