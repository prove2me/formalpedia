-- Prove2me | solution 1 for Bl.FirstBlockLemmaA.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:15.251009+00:00
-- url     : https://prove2.me/submissions/894faceb-1469-4b07-a842-68d5223c6180

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.FirstBlockLemmaA
namespace Bl.FirstBlockLemmaA
theorem _root_.solution :
  ∀ {k : Type u_1} [inst : Field.{u_1} k] {σ : Type u_2} [Fintype.{u_2} σ] (H : MvPolynomial.{u_2, u_1} σ k) (d : Nat),
  (∀ (m : Finsupp.{u_2, 0} σ Nat),
      Membership.mem.{u_2, u_2} (MvPolynomial.support.{u_1, u_2} H) m →
        Eq.{1} (DFunLike.coe.{max 1 (u_2 + 1), max 1 (u_2 + 1), 1} Finsupp.degree.{u_2, 0} m) d) →
    ∀ (c : k) (v : σ → k),
      Eq.{u_1 + 1}
        (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1), u_1 + 1}
          (MvPolynomial.eval.{u_1, u_2} (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} c v)) H)
        (HMul.hMul.{u_1, u_1, u_1} (HPow.hPow.{u_1, 0, u_1} c d)
          (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1), u_1 + 1} (MvPolynomial.eval.{u_1, u_2} v) H)) := by
  intro k _ σ _ H d h c v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← h m hm, Finsupp.degree_eq_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring
end Bl.FirstBlockLemmaA
