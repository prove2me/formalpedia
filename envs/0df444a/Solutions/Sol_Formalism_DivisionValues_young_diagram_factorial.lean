-- Prove2me | solution 1 for Formalism.DivisionValues.young_diagram_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:00.424445+00:00
-- url     : https://prove2.me/submissions/dd37189f-ef46-4151-a1c4-eb0577b71d6a

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_W8_log_nat_le
import Theorems.Thm_Formalism_DivisionValues_W8_ph_nat_le
import Theorems.Thm_Formalism_DivisionValues_W8_ph_nat_lt
import Theorems.Thm_Formalism_DivisionValues_W8_pair_abs
import Theorems.Thm_Formalism_DivisionValues_W8_phRows_add
import Theorems.Thm_Formalism_DivisionValues_W8_phRows_cons
import Theorems.Thm_Formalism_DivisionValues_W8_phRows_univ
import Theorems.Thm_Formalism_DivisionValues_W8_sum_ph_le_logFact
import Theorems.Thm_Formalism_DivisionValues_W8_phRows_blk
import Theorems.Thm_Formalism_DivisionValues_W8_telescope
import Theorems.Thm_P2M_Formalism_DivisionValues_W8_telescope__7f6de1e4cbc8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
namespace W8
end W8
open W8
private lemma neg_ph_natCast_le_one (r : ℕ) : -ph (r : ℝ) ≤ 1 := by
  have h0 : ph ((0 : ℕ) : ℝ) = 0 := by simp [ph]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · rw [hr, h0]
    norm_num
  · have := ph_nat_lt 0 r hr
    linarith
private lemma ph_add_ph_sub_add_phRows_le_ph_add_log_mul {aT w r0 rz : ℕ} {A Bl : ℝ} {blk : Multiset ℕ}
    (hA : 1 ≤ Real.log A) (haT : (aT : ℝ) + w ≤ A) (hr0 : r0 ≤ w) (hwA : (w : ℝ) ≤ A)
    (hblk : (blk.sum : ℝ) ≤ Bl) (hBl : Bl ≤ A) :
    ph ((aT + w : ℕ) : ℝ) + ph (r0 : ℝ) - ph (rz : ℝ) + phRows blk ≤
      ph (aT : ℝ) + ((2 * (w : ℝ) + Bl) * Real.log A + 1) := by
  have hL0 : 0 ≤ Real.log A := by linarith
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hd : |((aT + w : ℕ) : ℝ) - (aT : ℝ)| ≤ (w : ℝ) := by
    rw [abs_le]
    push_cast
    constructor <;> linarith
  have h1 := pair_abs (aT + w) aT (log_nat_le _ hA (by push_cast; linarith)) hA hd
  have hr0' : (r0 : ℝ) ≤ w := by exact_mod_cast hr0
  have h2 : ph (r0 : ℝ) ≤ (r0 : ℝ) * Real.log A := ph_nat_le r0 (log_nat_le r0 hA (by linarith))
  have h3 : (r0 : ℝ) * Real.log A ≤ (w : ℝ) * Real.log A := mul_le_mul_of_nonneg_right hr0' hL0
  have h4 := neg_ph_natCast_le_one rz
  have h5 := phRows_blk blk hA hblk hBl
  linarith
namespace W8
end W8
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open W8
namespace Formalism.DivisionValues
theorem _root_.solution : RowsFactorial := by
  intro n w S Bl sh A La fa ν ap hLaA hLa hwS hBl hfa
  subst hLaA
  have hL0 : 0 ≤ Real.log A := by linarith
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  refine ⟨fun hoff => ?_, fun aT haT htop => ?_⟩
  · obtain ⟨c, c', r, blk, sm, hI, hr, hblk, hν, hap⟩ := hoff
    subst hν
    subst hap
    have hcS : ∀ i, (c i : ℝ) ≤ S := fun i => (hI.1 i).2
    have hcA : ∀ i, ((w + c i : ℕ) : ℝ) ≤ A := fun i => by
      push_cast
      linarith [hcS i]
    have hν : phRows ((Finset.univ.val.map fun i => w + c i) + blk) =
        ∑ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) + ph ((w + c (Fin.last n) : ℕ) : ℝ) +
          phRows blk := by
      rw [phRows_add, phRows_univ, Fin.sum_univ_castSucc]
    have hfa' : ∑ i : Fin n, ph ((r i : ℕ) : ℝ) ≤ fa := le_trans (sum_ph_le_logFact r sm) hfa
    have hpair : ∀ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) - ph ((r i : ℕ) : ℝ) ≤
        ((c i.castSucc : ℝ) - c' i) * Real.log A + sh * Real.log A := by
      intro i
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hr i)
      have h2 : (c' i : ℝ) ≤ c i.castSucc := (hI.2 i).1
      have hd : |((w + c i.castSucc : ℕ) : ℝ) - ((r i : ℕ) : ℝ)| ≤
          ((c i.castSucc : ℝ) - c' i) + sh := by
        rw [abs_le]
        push_cast
        constructor <;> linarith
      have := pair_abs (w + c i.castSucc) (r i) (log_nat_le _ hLa (hcA _)) hLa hd
      linarith
    have hsum : ∑ i : Fin n, ph ((w + c i.castSucc : ℕ) : ℝ) - ∑ i : Fin n, ph ((r i : ℕ) : ℝ) ≤
        (∑ i : Fin n, ((c i.castSucc : ℝ) - c' i)) * Real.log A + (n : ℝ) * (sh * Real.log A) := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.sum_le_sum fun i _ => hpair i) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have htel : ∑ i : Fin n, ((c i.castSucc : ℝ) - c' i) ≤ S := telescope hI
    have hmul := mul_le_mul_of_nonneg_right htel hL0
    have hlast : ph ((w + c (Fin.last n) : ℕ) : ℝ) ≤ ((w : ℝ) + S) * Real.log A := by
      refine le_trans (ph_nat_le _ (log_nat_le _ hLa (hcA _))) ?_
      refine mul_le_mul_of_nonneg_right ?_ hL0
      push_cast
      linarith [hcS (Fin.last n)]
    have hb := phRows_blk blk hLa hblk hBl
    linarith
  · obtain ⟨c, c', r, r0, blk, sm, hI, hr, hr0, hblk, hν, hap⟩ := htop
    subst hν
    subst hap
    have hS0 : 0 ≤ S := le_trans (hI.1 0).1 (hI.1 0).2
    have hcS : ∀ i : Fin n, (c i : ℝ) ≤ S := fun i => le_trans (hI.2 i).1 (hI.1 i.castSucc).2
    have hcA : ∀ i : Fin n, ((w + c i : ℕ) : ℝ) ≤ A := fun i => by
      push_cast
      linarith [hcS i]
    have hν : phRows ((aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk)) =
        ph ((aT + w : ℕ) : ℝ) + ph ((r0 : ℕ) : ℝ) + ∑ i : Fin n, ph ((w + c i : ℕ) : ℝ) +
          phRows blk := by
      rw [phRows_cons, phRows_cons, phRows_add, phRows_univ]
      ring
    have hfa' : ∑ i : Fin (n + 1), ph ((r i : ℕ) : ℝ) ≤ fa := le_trans (sum_ph_le_logFact r sm) hfa
    have hfa2 : ∑ i : Fin (n + 1), ph ((r i : ℕ) : ℝ) =
        ph ((r 0 : ℕ) : ℝ) + ∑ i : Fin n, ph ((r i.succ : ℕ) : ℝ) := Fin.sum_univ_succ _
    have hpair : ∀ i : Fin n, ph ((w + c i : ℕ) : ℝ) - ph ((r i.succ : ℕ) : ℝ) ≤
        ((c i : ℝ) - c' i.succ) * Real.log A + sh * Real.log A := by
      intro i
      obtain ⟨h1a, h1b⟩ := abs_le.mp (hr i.succ)
      have h2 : (c' i.succ : ℝ) ≤ c i := (hI.2 i).2
      have hd : |((w + c i : ℕ) : ℝ) - ((r i.succ : ℕ) : ℝ)| ≤ ((c i : ℝ) - c' i.succ) + sh := by
        rw [abs_le]
        push_cast
        constructor <;> linarith
      have := pair_abs (w + c i) (r i.succ) (log_nat_le _ hLa (hcA _)) hLa hd
      linarith
    have hsum : ∑ i : Fin n, ph ((w + c i : ℕ) : ℝ) - ∑ i : Fin n, ph ((r i.succ : ℕ) : ℝ) ≤
        (∑ i : Fin n, ((c i : ℝ) - c' i.succ)) * Real.log A + (n : ℝ) * (sh * Real.log A) := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.sum_le_sum fun i _ => hpair i) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have htel : ∑ i : Fin n, ((c i : ℝ) - c' i.succ) ≤ S := telescope' hI
    have hmul := mul_le_mul_of_nonneg_right htel hL0
    have hrest := ph_add_ph_sub_add_phRows_le_ph_add_log_mul (rz := r 0) hLa haT hr0 (by linarith) hblk hBl
    linarith
end Formalism.DivisionValues
