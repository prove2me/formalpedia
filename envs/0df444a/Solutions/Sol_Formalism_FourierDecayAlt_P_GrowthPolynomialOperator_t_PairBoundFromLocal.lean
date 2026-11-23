-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PairBoundFromLocal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:34.920173+00:00
-- url     : https://prove2.me/submissions/ae9905f3-9259-4e50-939c-3df5251f776d

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB Finset NumberField
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : PairBoundFromLocal := by
  intro hMR hPB hLC hGC hLL hAx hStep hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ C₄ Cthr hC4
  obtain ⟨CA, C, h1, h2, h3, h4, hrest⟩ := hMR hLC hGC hLL hAx hStep C₄ Cthr hC4
  refine ⟨CA, C, h1, h2, h3, h4, ?_⟩
  intro C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb a1 a2 a3 a4 a5 a6
  refine ⟨k0, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk0 hSz hc hCf hU hInst hLM jn H _ _ _ Vt c sd
    hRI hDI P _ B hRows hMassData hEL τ Rw I HS H₁ _ _ _ _ _ _ X c5 Cn hLink hSplit hNum hBig hNsc hNG
  obtain ⟨m1, m2, m3, m4, m5⟩ := hk E W D e G bb Cp Cf Th de de' T T' du du' l hk0 hSz hc hCf hU hInst hLM
    jn H Vt c sd hRI hDI P B hRows hMassData hEL
  obtain ⟨lG, lS, ⟨typ, htyp⟩, ld, ld', lD⟩ := hLink
  obtain ⟨s1, s2, s3, s4, s5, s6, _⟩ := hSplit
  have htt : B.tt = (1 + 3 / (G.g1 : ℝ)) ^ G.f * (1 + 3 / (G.g2 : ℝ)) ^ G.f := by
    unfold S3.MassData.tt
    rw [Fintype.prod_equiv typ (fun p => 1 + 3 / B.g p)
      (fun x => 1 + 3 / (if x.1 then (G.g1 : ℝ) else (G.g2 : ℝ))) (fun p => by rw [htyp p])]
    rw [Fintype.prod_prod_type]
    simp [Sz.Glob.f, Finset.prod_const, Finset.card_univ]
  obtain ⟨hp, hμKo, _, _, _, _, _, _, _, _, _, _, _, _, _, hvolG, _, _, _, _, _, _, _, _, _, _, hdeg,
    _, _, _, _, hd, hd', _, _, _⟩ := hMassData.1
  have hD : 0 < B.Dstar := by
    unfold S3.MassData.Dstar S3.MassData.μKpp
    have : 0 < ∏ p, B.μKppp p := Finset.prod_pos (fun p _ => (hp p).2.2.2.2.2.2.2.1)
    positivity
  have hdd : 0 ≤ du * du' / (G.size de T du).Dstar := by
    rw [← lD, ← ld, ← ld']; positivity
  refine hPB hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ τ Rw I HS H₁ X G.k G.r G.f bb G.g1 G.g2 c5 Cn
    B.δ B.e1 _ hNum hdd m2 m3 (by linarith) m5 s1 s2 (htt ▸ s3) s4 s5 s6 hBig hNsc ?_ hNG
  show X.pairSum _ ≤ _
  rw [lS, ← lD, ← ld, ← ld']
  exact m1
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
