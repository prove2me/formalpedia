-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_BoxLimitFromClaim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:59.28661+00:00
-- url     : https://prove2.me/submissions/c1543695-fc5d-49df-93b4-366aa358ed2c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_on_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : BoxLimitFromClaim := by
  intro hLB hLA hL2 hPair hCoef hLeib hCut S hL hFI hP hClaim
  have key : ∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ S.Ntot → S.OnBoxes (List.ofFn Y) →
      Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (plus (List.ofFn Y))) (𝓝[>] 0)
        (𝓝 (S.size (plus (List.ofFn Y)) * S.jn)) := by
    intro N Y hN hOn
    have hinf : ∀ a, ((S.fam N).J a).Infinite := by
      intro a; rw [S.fam_J]; exact Set.Icc_infinite (by linarith)
    have hde : ∀ Y' : Fin N → ℝ, LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) = S.dens (List.ofFn Y') := by
      intro Y'; funext ω; exact (S.fam_dens N Y' ω).symm
    have hcl : ∀ Y', (S.fam N).On Y' →
        Integrable (LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
      intro Y' h'
      rw [hde]
      exact (hClaim _ ((on_iff S N Y').mp h') (by rw [List.length_ofFn]; exact hN)).1
    have h := hLB hLA hL2 hPair hCoef hLeib hCut S.B N (S.fam N) S.c hinf (hFI N hN) hcl Y ((on_iff S N Y).mpr hOn)
    rw [hde, (hClaim _ hOn (by rw [List.length_ofFn]; exact hN)).2] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hP N Y hN hOn ε hε).symm
  intro w hOn hlen
  have := key w.length w.get hlen (by rw [List.ofFn_get]; exact hOn)
  rwa [List.ofFn_get] at this
end Formalism.FourierDecayAlt.P.LEx2
