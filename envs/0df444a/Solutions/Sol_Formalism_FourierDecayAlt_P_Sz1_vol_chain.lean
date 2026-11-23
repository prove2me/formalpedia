-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.vol_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:22.551936+00:00
-- url     : https://prove2.me/submissions/fd8dc0cf-0732-4322-8742-63431cc7f8ae

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz1
theorem _root_.solution {ι : Type} [Fintype ι] (S : SizeData ι) (hM : S.MassRatios) (d : ℕ)
    (hd : S.k + d ≤ S.n) :
    S.vol (S.k + d) =
      ((S.v / Real.pi) ^ (∑ M ∈ Ioc S.k (S.k + d), M) *
          ((∏ i ∈ Ico S.k (S.k + d), i.factorial : ℕ) : ℝ)) ^ S.f *
        (S.dF ^ (-(1 / 2 : ℝ))) ^ d * (∏ M ∈ Ioc S.k (S.k + d), S.Lv M) * S.vol S.k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := hM (S.k + d + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, ih (by omega)] at h
    rw [← Nat.add_assoc, h, Finset.sum_Ioc_succ_top (by omega), Finset.prod_Ioc_succ_top (by omega),
      Finset.prod_Ico_succ_top (by omega), pow_add, pow_succ]
    push_cast
    simp only [mul_pow]
    ring
end Formalism.FourierDecayAlt.P.Sz1
