-- Prove2me | solution 1 for Formalism.L2.Ker.KS.exists_cmOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:30.681802+00:00
-- url     : https://prove2.me/submissions/6360cb28-289f-4bd4-be2e-01c616d7f9a8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_KernelLattices_KernelLocalFactors_SelfDualLatticeNorms_HalfPeriodStandardCM
import Theorems.Thm_Formalism_L2_Ker_KS_cmL_swap
import Theorems.Thm_Formalism_L2_Ker_KS_cmL_shift
import Theorems.Thm_Formalism_L2_Ker_KS_exists_form

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
open Formalism Formalism.L2 Formalism.L2.Ker Formalism.L2.Ker.KS
open Formalism.L2.Th1.H (cmL CmOK)
namespace Formalism.L2.Ker.KS
theorem _root_.solution (d : ℕ) (hd : 0 < d) (hd8 : d % 8 = 7) (hp : d.Prime) (L : PeriodPair)
    (hst : ∀ x ∈ L.lattice, Formalism.L2.Th1.F.cmTheta 1 d * x ∈ L.lattice) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d ∧ (cmL a b d ha hd lam hlam).lattice = L.lattice := by
  obtain ⟨a, b, c, ha, lam, hlam, h, hL⟩ := exists_form d hd L hst
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hc : 0 < c := by
    by_contra hcn
    push_neg at hcn
    have h0 : 0 < 4 * (a : ℤ) * c := by rw [h]; linarith [sq_nonneg b]
    nlinarith
  rcases Nat.even_or_odd a with hae | hao
  · rcases Int.even_or_odd c with hce | hco
    · obtain ⟨t, ht⟩ : Odd b := by
        rcases Int.even_or_odd b with ⟨t, ht⟩ | hbo
        · exfalso
          have e : 4 * ((a : ℤ) * c) = 4 * (t * t) + (d : ℤ) := by
            linear_combination h + (b + t + t) * ht
          generalize (a : ℤ) * c = P at e
          generalize t * t = Q at e
          omega
        · exact hbo
      have hs : 0 < (a : ℤ) + b + c := by
        have h4 : 0 < 4 * (((a : ℤ) + b + c) * c) := by
          rw [show 4 * (((a : ℤ) + b + c) * c) = (b + 2 * c) ^ 2 + d by linear_combination h]
          linarith [sq_nonneg (b + 2 * c)]
        by_contra hn
        push_neg at hn
        nlinarith
      obtain ⟨lam', hlam', hL'⟩ := cmL_shift a b c d ha hd lam hlam hs h
      obtain ⟨m, hm⟩ := hae
      obtain ⟨n, hn⟩ := hce
      refine ⟨((a : ℤ) + b + c).toNat, b + 2 * c, c, by omega, lam', hlam', ⟨?_, ?_, hd8, hp⟩, hL'.trans hL⟩
      · rw [Int.toNat_of_nonneg hs.le]
        linear_combination h
      · exact ⟨((a : ℤ) + b + c).toNat / 2, by omega⟩
    · obtain ⟨lam', hlam', hL'⟩ := cmL_swap a b c d ha hd lam hlam hc h
      obtain ⟨k, hk⟩ := hco
      refine ⟨c.toNat, -b, a, by omega, lam', hlam', ⟨?_, ?_, hd8, hp⟩, hL'.trans hL⟩
      · rw [Int.toNat_of_nonneg hc.le]
        linear_combination h
      · exact ⟨c.toNat / 2, by omega⟩
  · exact ⟨a, b, c, ha, lam, hlam, ⟨h, hao, hd8, hp⟩, hL⟩
end Formalism.L2.Ker.KS
