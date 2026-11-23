-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.card_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:53.666751+00:00
-- url     : https://prove2.me/submissions/34ab3203-c985-4ccd-b007-2f55255ed4fe

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_two_le_q
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_card_pm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2) :
    Nat.card {d : K // star d = d} = q := by
  have hq := two_le_q hc
  have hfix : Nat.card {d : K // star d = d} ≤ q := by
    have h1 := card_pm_le (K := K) hq (-1)
    have h2 : Nat.card {x : K // x ^ q + (-1) * x = 0} = Nat.card {d : K // star d = d} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [hs, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]))
    omega
  let Tr : K →+ K := AddMonoidHom.mk' (fun x => x + star x) (by intro a b; simp only [star_add]; ring)
  have hker : Nat.card Tr.ker ≤ q := by
    have h1 := card_pm_le (K := K) hq 1
    have h2 : Nat.card {x : K // x ^ q + 1 * x = 0} = Nat.card Tr.ker :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        rw [AddMonoidHom.mem_ker]
        show _ ↔ x + star x = 0
        rw [hs, one_mul, add_comm]))
    omega
  have hrange : Nat.card Tr.range ≤ Nat.card {d : K // star d = d} := by
    apply Nat.card_le_card_of_injective
      (fun y : Tr.range => (⟨y.1, by
        obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        show star (x + star x) = x + star x
        rw [star_add, star_star, add_comm]⟩ : {d : K // star d = d}))
    intro y y' h
    have h' : (y : K) = (y' : K) := congrArg (fun z : {d : K // star d = d} => z.1) h
    exact Subtype.ext h'
  have hmul : Nat.card Tr.ker * Nat.card Tr.range = q ^ 2 := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, Nat.card_eq_fintype_card, hc]
  nlinarith
end Formalism.FourierDecayAlt.P.S3x5
