-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_hasSum_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:08.313802+00:00
-- url     : https://prove2.me/submissions/8026464f-26c7-4bca-97dc-2f8f41b2babf

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution {ι κ : Type*} (f : ι → ℂ) (g : κ → ℂ)
    (s z : ℂ) (hf : HasSum f s) (hg : HasSum g z)
    (hfn : Summable (fun p => ‖f p‖)) (hgn : Summable (fun p => ‖g p‖)) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (s*z) := by
  have hs := (hfn.mul_norm hgn).of_norm
  have he := tsum_mul_tsum_of_summable_norm hfn hgn
  rw [hf.tsum_eq,hg.tsum_eq] at he
  exact he.symm ▸ hs.hasSum
end FourierJacobi.Analysis
