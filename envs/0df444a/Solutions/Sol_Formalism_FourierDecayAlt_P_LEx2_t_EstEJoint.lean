-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_EstEJoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:32:57.067592+00:00
-- url     : https://prove2.me/submissions/0577bd36-e84a-4be3-8a9a-47210f50168d

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_size_ne_zero

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
theorem _root_.solution : EstEJoint := by
  intro E W _ D S loc hN hRoots hAdm hwt hgram hJ0 hlim
  have hj : ∀ v, (S v).jsq = (S v).jn := by
    intro v
    unfold Sys.jn Sys.jsq
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hJ0 v ω).symm)
  simp only [hj]
  intro w hw
  have hwW : w ∈ D.Wall ∧ D.cnt w ≤ D.Ntop := by simpa [TB.Data.Wb] using hw
  have hsz : ∀ v, (S v).size (loc w v) ≠ 0 := fun v => size_ne_zero (S v) (hRoots v) _ (hAdm w hwW.1 v).1
  have hl : Tendsto (fun ε : ℝ => ∏ v, (S v).principalHermitianLattice ε (loc w v)) (𝓝[>] 0)
      (𝓝 (∏ v, ((S v).size (loc w v) * (S v).jn))) :=
    tendsto_finset_prod _ (fun v _ => hlim v _ (hAdm w hwW.1 v).1
      (by rw [hN]; exact (hAdm w hwW.1 v).2.trans hwW.2))
  have h2 := hl.div_const (D.wt w)
  have hval : (∏ v, ((S v).size (loc w v) * (S v).jn)) / D.wt w = ∏ v, (S v).jn := by
    rw [hwt w hwW.1, Finset.prod_mul_distrib]
    have : (∏ v, (S v).size (loc w v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hsz v)
    field_simp
  rw [hval] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hgram ε hε w hwW.1]
end Formalism.FourierDecayAlt.P.LEx2
