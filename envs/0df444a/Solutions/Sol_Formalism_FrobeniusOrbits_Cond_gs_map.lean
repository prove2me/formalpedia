-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.gs_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:49.70041+00:00
-- url     : https://prove2.me/submissions/6c493e30-0856-4036-bfd2-ae749c6ace8c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_chi_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
variable {K : Type*} [Field K] [CharZero K]
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : x ^ p = 1) (σ : K →+* K)
    (v : ℕ) (hσ : σ x = x ^ v) (hv : (v : ZMod p) = -1) : σ (gs p hx) = -gs p hx := by
  have hχ : ∀ a : ZMod p, σ (chi p K a) = chi p K a := by
    intro a
    simp only [chi, MulChar.ringHomComp_apply]
    exact map_intCast σ _
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx (-a) := by
    intro a
    calc σ (AddChar.zmodChar p hx a) = (AddChar.zmodChar p hx a) ^ v := by
          rw [AddChar.zmodChar_apply, map_pow, hσ]
          ring
      _ = AddChar.zmodChar p hx (v • a) := by
          exact (AddChar.map_nsmul_eq_pow _ _ _).symm
      _ = AddChar.zmodChar p hx (-a) := by rw [nsmul_eq_mul, hv, neg_one_mul]
  have hc : ∀ a : ZMod p, chi p K a = chi p K (-1) * chi p K (-a) := by
    intro a
    rw [← map_mul, neg_one_mul, neg_neg]
  unfold gs gaussSum
  rw [map_sum]
  simp only [map_mul, hχ, hψ]
  calc ∑ a, chi p K a * AddChar.zmodChar p hx (-a)
        = ∑ a, chi p K (-1) * (chi p K (-a) * AddChar.zmodChar p hx (-a)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hc a, mul_assoc]
    _ = chi p K (-1) * ∑ a, chi p K a * AddChar.zmodChar p hx a := by
          rw [← Finset.mul_sum]
          congr 1
          exact Equiv.sum_comp (Equiv.neg (ZMod p)) (fun a => chi p K a * AddChar.zmodChar p hx a)
    _ = -∑ a, chi p K a * AddChar.zmodChar p hx a := by rw [chi_neg_one (K := K) hp4, neg_one_mul]
end Formalism.FrobeniusOrbits.Cond
