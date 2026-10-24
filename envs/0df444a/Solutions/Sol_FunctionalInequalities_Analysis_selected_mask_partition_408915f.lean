-- Prove2me | solution 1 for FunctionalInequalities.Analysis.selected_mask_partition_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:47:22.18012+00:00
-- url     : https://prove2.me/submissions/633154b6-f50c-4e97-994f-fa8c99bbdd8c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The mask selector returns the empty list exactly for the all-`false` mask. -/
theorem FunctionalInequalities.Analysis.selected_eq_nil_iff {m : ℕ} (h : Fin m → E) (q : Fin m → Bool) :
    selected h q = [] ↔ ∀ i, q i = false := by
    induction m with
    | zero =>
        simp [selected]
    | succ m ih =>
        cases hq0 : q 0 with
        | false =>
            simp [selected, hq0, ih (Fin.tail h) (Fin.tail q),
              Fin.forall_fin_succ, Fin.tail]
        | true =>
            simp [selected, hq0, Fin.forall_fin_succ]
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Boolean-mask partition facts for the actual ordered `selected` lists (BKL arXiv:2610.05474v1, (72)–(74),
singleton and middle allocations): lengths add up to `m`, the two selections together are a permutation of the
slots, an indicator of one slot selects exactly that slot, and a selection of length `1` comes from such an
indicator. Repeated slot values and `m = 0` are included.
-/
theorem solution {E : Type*} {m : ℕ}
    (h : Fin m → E) (q : Fin m → Bool) :
    (FunctionalInequalities.Analysis.selected h q).length + (FunctionalInequalities.Analysis.selected h (fun i => !(q i))).length = m ∧
    (FunctionalInequalities.Analysis.selected h q ++ FunctionalInequalities.Analysis.selected h (fun i => !(q i))).Perm (List.ofFn h) ∧
    (∀ i : Fin m, FunctionalInequalities.Analysis.selected h (fun j => decide (j = i)) = [h i]) ∧
    ((FunctionalInequalities.Analysis.selected h q).length = 1 → ∃ i : Fin m, q = fun j => decide (j = i)) := by
    induction m with
    | zero =>
        simp [FunctionalInequalities.Analysis.selected]
    | succ m ih =>
        obtain ⟨hlen, hperm, hsingle, hone⟩ :=
          ih (Fin.tail h) (Fin.tail q)
        have hnot :
            Fin.tail (fun i : Fin (m + 1) => !(q i)) =
              (fun i : Fin m => !(Fin.tail q i)) := by
          funext i
          rfl
        have htailh :
            List.ofFn (Fin.tail h) =
              List.ofFn (fun i : Fin m => h i.succ) := by
          apply congrArg (fun f : Fin m → E => List.ofFn f)
          funext i
          rfl
        refine ⟨?_, ?_, ?_, ?_⟩
        · cases hq0 : q 0 with
          | false =>
              simp [FunctionalInequalities.Analysis.selected, hq0, hnot] at hlen ⊢
              omega
          | true =>
              simp [FunctionalInequalities.Analysis.selected, hq0, hnot] at hlen ⊢
              omega
        · cases hq0 : q 0 with
          | false =>
              have move (l r : List E) (a : E) :
                  (l ++ a :: r).Perm (a :: (l ++ r)) := by
                induction l with
                | nil =>
                    exact List.Perm.refl _
                | cons b l ihl =>
                    exact (List.Perm.cons b ihl).trans
                      (List.Perm.swap _ _ _)
              have hp :=
                (move
                  (FunctionalInequalities.Analysis.selected (Fin.tail h) (Fin.tail q))
                  (FunctionalInequalities.Analysis.selected (Fin.tail h) (fun i => !(Fin.tail q i)))
                  (h 0)).trans (hperm.cons (h 0))
              rw [htailh] at hp
              simpa [FunctionalInequalities.Analysis.selected, hq0, hnot, List.ofFn_succ] using hp
          | true =>
              have hp := hperm.cons (h 0)
              rw [htailh] at hp
              simpa [FunctionalInequalities.Analysis.selected, hq0, hnot, List.ofFn_succ] using hp
        · intro i
          refine Fin.cases ?_ (fun k => ?_) i
          · have hnil :
                FunctionalInequalities.Analysis.selected (Fin.tail h)
                    (Fin.tail
                      (fun j : Fin (m + 1) =>
                        decide (j = (0 : Fin (m + 1))))) = [] := by
              apply
                (FunctionalInequalities.Analysis.selected_eq_nil_iff
                  (Fin.tail h)
                  (Fin.tail
                    (fun j : Fin (m + 1) =>
                      decide (j = (0 : Fin (m + 1)))))).2
              intro j
              have hn : (j.succ : Fin (m + 1)) ≠ 0 :=
                Fin.succ_ne_zero j
              change decide (j.succ = (0 : Fin (m + 1))) = false
              simp [hn]
            simp [FunctionalInequalities.Analysis.selected, hnil]
          · have hzero :
                (fun j : Fin (m + 1) => decide (j = k.succ)) 0 = false := by
              have hn : (0 : Fin (m + 1)) ≠ k.succ :=
                (Fin.succ_ne_zero k).symm
              simp [hn]
            have hmask :
                Fin.tail (fun j : Fin (m + 1) => decide (j = k.succ)) =
                  (fun j : Fin m => decide (j = k)) := by
              funext j
              simp only [Fin.tail, Fin.succ_inj]
            have hs := hsingle k
            change FunctionalInequalities.Analysis.selected (Fin.tail h) (fun j => decide (j = k)) =
              [h k.succ] at hs
            simpa [FunctionalInequalities.Analysis.selected, hzero, hmask] using hs
        · intro hlength
          cases hq0 : q 0 with
          | false =>
              have ht :
                  (FunctionalInequalities.Analysis.selected (Fin.tail h) (Fin.tail q)).length = 1 := by
                simpa [FunctionalInequalities.Analysis.selected, hq0] using hlength
              obtain ⟨i, hi⟩ := hone ht
              have hn : (0 : Fin (m + 1)) ≠ i.succ :=
                (Fin.succ_ne_zero i).symm
              refine ⟨i.succ, ?_⟩
              funext j
              refine Fin.cases ?_ (fun k => ?_) j
              · simp [hq0, hn]
              · have hk :
                    q k.succ = decide (k = i) := by
                  simpa [Fin.tail] using congrFun hi k
                simpa only [Fin.succ_inj] using hk
          | true =>
              have ht :
                  (FunctionalInequalities.Analysis.selected (Fin.tail h) (Fin.tail q)).length = 0 := by
                simpa [FunctionalInequalities.Analysis.selected, hq0] using hlength
              have hall :=
                (FunctionalInequalities.Analysis.selected_eq_nil_iff (Fin.tail h) (Fin.tail q)).mp
                  (List.length_eq_zero_iff.mp ht)
              refine ⟨0, ?_⟩
              funext j
              refine Fin.cases ?_ (fun k => ?_) j
              · simp [hq0]
              · have hk : q k.succ = false := by
                  simpa [Fin.tail] using hall k
                have hs : (k.succ : Fin (m + 1)) ≠ 0 :=
                  Fin.succ_ne_zero k
                simp [hk, hs]
