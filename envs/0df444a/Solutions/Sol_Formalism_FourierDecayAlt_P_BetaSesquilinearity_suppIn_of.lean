-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.suppIn_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:47.443848+00:00
-- url     : https://prove2.me/submissions/926acff2-a6c0-4da1-8747-47da80ee05e7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Gf_cont

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) : SuppIn (GPos D) F := by
  intro g hg
  have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g} :=
    gv_closed.inter (isClosed_le continuous_const (Gf_cont D.z D.z'))
  have hsub : {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g} :=
    fun g hg => ⟨hg.1, h g hg.1 hg.2⟩
  have h2 := closure_minimal hsub hcl hg
  exact ⟨h2.1, lt_of_lt_of_le hε h2.2⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
