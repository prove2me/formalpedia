-- Prove2me | solution 1 for CKLaneA3X.TMd.mul_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:48:25.481661+00:00
-- url     : https://prove2.me/submissions/3e8e7b4c-1f75-4e98-978c-1aa077d1769f

import Theorems.Thm_CKLaneA3X_Encl_mul
import Theorems.Thm_CKLaneA3X_entryBounds_spec
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_enclosure

open CKLaneA3X



/-!
# CKLaneA3X.Bound — rigorous magnitude bounds for `LPoly`/`SPoly`/`TPoly`

`L` ranges over `[Llo, Lhi]` (Mathlib `Real.log_two_gt_d9`, `Real.log_two_lt_d9`), `|σ| ≤ 1/2`,
`0 ≤ t ≤ Tq`.  All bound functions are kernel-evaluable (`List.rec`/`Nat.rec`).
-/

namespace CKLaneA3X



































/-! ## entry bounds for TPoly -/











/-! ## sums of entry bounds -/





theorem ldrop_zero (β : List ℚ) : ldrop β 0 = β := by cases β <;> rfl
theorem ldrop_nil (k : ℕ) : ldrop [] k = [] := rfl
theorem ldrop_cons_succ (b : ℚ) (β : List ℚ) (k : ℕ) : ldrop (b :: β) (k + 1) = ldrop β k := rfl



theorem bsum_nonneg (β : List ℚ) (h : Nonneg β) : 0 ≤ bsum β := by
  induction β with
  | nil => simp [bsum]
  | cons b β ih =>
    show 0 ≤ b + Tq * bsum β
    have hb : 0 ≤ b := h b (List.mem_cons_self)
    have hr : 0 ≤ bsum β := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have : (0 : ℚ) ≤ Tq := by norm_num [Tq]
    positivity

theorem EntryBnd.nonneg {P : TPoly} {β : List ℚ} (h : EntryBnd P β) : Nonneg β := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hsb _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · have := hsb 0 (by norm_num)
      have h0 : (0 : ℝ) ≤ _ := (abs_nonneg _).trans this
      exact_mod_cast h0
    · exact ih b hb'

theorem ldrop_nonneg (β : List ℚ) (h : Nonneg β) (k : ℕ) : Nonneg (ldrop β k) := by
  induction β generalizing k with
  | nil => simp [ldrop_nil, Nonneg]
  | cons b β ih =>
    cases k with
    | zero => rw [ldrop_zero]; exact h
    | succ k =>
      rw [ldrop_cons_succ]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) k





end CKLaneA3X



/-!
# CKLaneA3X.TMFun — functional Taylor-model operations (kernel-evaluable) with soundness

A `TMd` is `(P, r, n)`.  `Good f d` := `Encl f d.P d.r d.n ∧ 0 ≤ d.r`.
All remainders are rounded up to multiples of `2^-40` (`rup`) to keep rationals small.
-/

namespace CKLaneA3X







theorem le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _







theorem HB_nonneg (β γ : List ℚ) (hβ : Nonneg β) (hγ : Nonneg γ) (n : ℕ) : 0 ≤ HB β γ n := by
  induction β generalizing n with
  | nil => show (0 : ℚ) ≤ 0; exact le_refl _
  | cons b β ih =>
    have hb : 0 ≤ b := hβ b List.mem_cons_self
    have hβ' : Nonneg β := fun x hx => hβ x (List.mem_cons_of_mem _ hx)
    cases n with
    | zero =>
      show 0 ≤ bsum (b :: β) * bsum γ
      exact mul_nonneg (bsum_nonneg _ hβ) (bsum_nonneg _ hγ)
    | succ n =>
      show 0 ≤ b * bsum (ldrop γ (n + 1)) + HB β γ n
      exact add_nonneg (mul_nonneg hb (bsum_nonneg _ (ldrop_nonneg _ hγ _))) (ih hβ' n)





theorem Tq_nonneg : (0 : ℚ) ≤ Tq := by norm_num [Tq]

theorem _root_.solution {f g : ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) (va vb n : ℕ)
    (hza : zeroPrefix a.P va = true) (hzb : zeroPrefix b.P vb = true)
    (hva : va ≤ a.n) (hn1 : n ≤ va + b.n) (hn2 : n ≤ vb + a.n) :
    Good (fun t ρ => f t ρ * g t ρ) (TMd.mul a b va vb n) := by
  have hβ := entryBounds_spec a.P
  have hγ := entryBounds_spec b.P
  refine ⟨?_, ?_⟩
  · exact Encl.mul ha.1 hβ hb.1 hγ hza hzb hva hn1 hn2 ha.2 hb.2 rfl (le_rup _)
  · refine le_trans ?_ (le_rup _)
    unfold mulRem
    have h1 := HB_nonneg _ _ hβ.nonneg hγ.nonneg n
    have h2 := bsum_nonneg _ (ldrop_nonneg _ hβ.nonneg va)
    have h3 := bsum_nonneg _ (ldrop_nonneg _ hγ.nonneg vb)
    have ha2 := ha.2
    have hb2 := hb.2
    have hT := Tq_nonneg
    positivity

















/-! ## Horner evaluation of a rational polynomial at a TM -/












/-! ## magnitude of a TM-enclosed function -/



end CKLaneA3X
