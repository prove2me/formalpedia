-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.blk_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:40.866506+00:00
-- url     : https://prove2.me/submissions/a70a2a45-abb8-47ec-97cd-747e17d780e0

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {a b c d a' b' c' d' : K} {r s u w r' s' u' w' : Fin M → K} {U U' : Matrix (Fin M) (Fin M) K}
    (h : blk a b r c d s u w U = blk a' b' r' c' d' s' u' w' U') :
    a = a' ∧ b = b' ∧ r = r' ∧ c = c' ∧ d = d' ∧ s = s' ∧ u = u' ∧ w = w' ∧ U = U' :=
  ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1, funext fun j => congrFun (congrFun h 0) j.succ.succ,
    congrFun (congrFun h 1) 0, congrFun (congrFun h 1) 1, funext fun j => congrFun (congrFun h 1) j.succ.succ,
    funext fun i => congrFun (congrFun h i.succ.succ) 0, funext fun i => congrFun (congrFun h i.succ.succ) 1,
    Matrix.ext fun i j => congrFun (congrFun h i.succ.succ) j.succ.succ⟩
end CompanionTheory.PlacePermOperatorBicommutantSpan
