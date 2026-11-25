-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:08.157011+00:00
-- url     : https://prove2.me/submissions/9e61d4e8-789e-417d-a1ae-bb7d620d96ef

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (p : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.C a) G = a * jetAt0 p G := by
  rw [mul_comm p]
  unfold jetAt0
  rw [Finset.mul_sum]
  refine (Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl fun m _ => ?_)
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h, mul_zero]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  · rw [MvPolynomial.coeff_C_mul]
    ring
end Formalism.L2.FormalSeriesBounds
