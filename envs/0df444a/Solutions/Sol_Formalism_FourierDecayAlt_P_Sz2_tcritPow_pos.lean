-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.tcritPow_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:18.274966+00:00
-- url     : https://prove2.me/submissions/a89cc56d-074a-4983-b152-06148685f68e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution {ι : Type} [Fintype ι] (S : SizeData ι) (hOk : S.Ok)
    (hds : ∀ w, 0 < S.dsig w) (w : ι) : 0 < S.TcritPow w := by
  have hv := hOk.hv
  have hg10 : (0 : ℝ) < S.g1 := by
    have := hOk.hg1
    exact_mod_cast (by omega : 0 < S.g1)
  have hg20 : (0 : ℝ) < S.g2 := by
    have := hOk.hg2
    exact_mod_cast (by omega : 0 < S.g2)
  have h1 : 0 < S.ka := by unfold SizeData.ka; have := Real.pi_pos; positivity
  have h2 : 0 < S.rd := by unfold SizeData.rd; positivity
  have h3 : 0 < S.g := by unfold SizeData.g; positivity
  have h4 : 0 < S.VV w := by
    unfold SizeData.VV
    have h5 : 0 < sfac S.n := by
      unfold sfac
      exact Finset.prod_pos (fun i _ => Nat.factorial_pos i)
    have h6 : (0 : ℝ) < (sfac S.n : ℝ) := by exact_mod_cast h5
    exact mul_pos (hds w) h6
  have h5 := hOk.hVu w
  unfold SizeData.TcritPow Sz.TcritPow
  positivity
end Formalism.FourierDecayAlt.P.Sz2
