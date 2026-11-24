-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.ae_inSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:16.593576+00:00
-- url     : https://prove2.me/submissions/fe856391-f514-49a6-9880-d33f36bc0027

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ q ∂Ds.μSS, Ds.inSS q := by
  have key : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
      (P : α → Prop), (∀ᵐ x ∂μ, P x) → ∀ᵐ p ∂(μ.prod ν), P p.1 := by
    intro α β _ _ μ ν P h
    rw [ae_iff] at h ⊢
    refine le_antisymm ?_ zero_le
    calc (μ.prod ν) {p | ¬P p.1} = (μ.prod ν) ({x | ¬P x} ×ˢ Set.univ) := by
          congr 1
          ext p
          simp
      _ ≤ μ {x | ¬P x} * ν Set.univ := Measure.prod_prod_le _ _
      _ = 0 := by rw [h, zero_mul]
  have key2 : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
      (P : β → Prop), (∀ᵐ y ∂ν, P y) → ∀ᵐ p ∂(μ.prod ν), P p.2 := by
    intro α β _ _ μ ν P h
    rw [ae_iff] at h ⊢
    refine le_antisymm ?_ zero_le
    calc (μ.prod ν) {p | ¬P p.2} = (μ.prod ν) (Set.univ ×ˢ {y | ¬P y}) := by
          congr 1
          ext p
          simp
      _ ≤ μ Set.univ * ν {y | ¬P y} := Measure.prod_prod_le _ _
      _ = 0 := by rw [h, mul_zero]
  have h1 : ∀ᵐ x ∂Ds.μW, Matrix.of x ∈ UWset k r Ds.z := ae_iff.mpr Ds.haarW.conc
  have h2 : ∀ᵐ x ∂Ds.μN, Matrix.of x ∈ Nset k r := ae_iff.mpr Ds.haarN.conc
  have h3 : ∀ᵐ x ∂Ds.μW', Matrix.of x ∈ UWset k r Ds.z' := ae_iff.mpr Ds.haarW'.conc
  show ∀ᵐ q ∂((Ds.μW.prod Ds.μN).prod (Ds.μW'.prod Ds.μN)), Ds.inSS q
  filter_upwards [key _ _ _ (key _ _ _ h1), key _ _ _ (key2 _ _ _ h2), key2 _ _ _ (key _ _ _ h3),
    key2 _ _ _ (key2 _ _ _ h2)] with q a b c d
  exact And.intro a (And.intro b (And.intro c d))
end Formalism.FourierDecayAlt.P.TBBx2
