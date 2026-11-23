-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_AxiomsOfLocalModel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:46.772368+00:00
-- url     : https://prove2.me/submissions/3c532488-5904-4c9e-a861-043de974d04a

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_famOk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : AxiomsOfLocalModel := by
  rintro ⟨hA, hSch, hPD, hDS, hDP, hBD, hPL, hSO, hPh, hOS, hOD, hLP, hUH, hTP, hTU, hGL, hUM, hAS, hAF,
    hKL, hLK, hDM, hDA, hA2, hKG, hN0, -, -, h1, -, -, -⟩ h13 E W _ D hD
  have fam := fun i s hs hsi hi Y hY =>
    famOk hA hA2 hLP hPh hUH hN0 h13 hTP hTU h1 hSch hPD hOD hOS D hD i s hs hsi hi Y hY
  have hE : ∀ i, 1 ≤ i → i ≤ D.r + 1 → 0 ≤ D.e i ∧ D.e i ≤ 1 := by
    intro i h1 h2; rw [hD.2.2.2 i h1 h2]; constructor <;> norm_num
  refine ⟨?_, ?_, hE, ?_⟩
  · intro i Y
    obtain ⟨P, _, pl, η, cl, d, a, hK⟩ := hD.1 i Y
    refine hKL hSch hDS (TB.Pt E) P Y (D.Kr i)
      (fun p x y => if cl p x = cl p y then
          d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y) else 0) a hK ?_
    intro p
    refine hBD (TB.Pt E) (Option E) Y (cl p)
      (fun x y => d p x * conj (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y)) ?_
    intro b
    exact hDP (TB.Pt E) _ _ (d p)
      (hLK hA hKG (pl p).K (pl p).R (pl p).ψ (pl p).datum (TB.Pt E) (η p) _)
  · obtain ⟨Th, h2, -, -⟩ := hAF hUM hAS E W D (by
      intro i s hs hsi hi Y hY
      obtain ⟨P, _, S, a, hok, hN, hB, hL, hL'⟩ := fam i s hs hsi hi Y hY
      exact hGL hPL hSO E W P D i s S a Y hN hB hL hL' hok) hE hD.2.2.1
    exact h2
  · refine (hDA hPL hSO hDM E W D ?_).2
    intro T i s hs hsi hi
    obtain ⟨P, _, S, a, hok, hN, hB, hL, -⟩ := fam i s hs hsi hi (T.X (i - s))
      (fun h hh => ((T.isTower (i - s) h).1 hh).1)
    exact ⟨P, inferInstance, S, a, hok, fun t ht h hh h' hh' => hN t t ht ht h hh h' hh', hB, hL⟩
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
