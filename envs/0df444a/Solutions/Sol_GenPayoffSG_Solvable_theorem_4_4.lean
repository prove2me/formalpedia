-- Prove2me | solution 1 for GenPayoffSG.Solvable.theorem_4_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:33:31.134873+00:00
-- url     : https://prove2.me/submissions/96d13df0-a558-48fe-8da9-f07a2aee1a25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_GenPayoffSG_Solvable_OneShot
import Theorems.Thm_GenPayoffSG_Solvable_theorem_3_1
import Theorems.Thm_AGT_nash_existence

open MeasureTheory ProbabilityTheory GenPayoffSG.Solvable

namespace GPSGThm44

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

lemma toReal_update (x : ∀ j, PMF (A j)) (i : I) (y : PMF (A i)) :
    (fun j b => (Function.update x i y j b).toReal) =
      Function.update (fun j b => (x j b).toReal) i (fun b => (y b).toReal) := by
  funext j b
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma oneShotPayoff_eq_expected (G : Game I S A) (D : I → HistFun I S A) {n : ℕ}
    (h : Hist I S A n) (x : ∀ j, PMF (A j)) (i : I) :
    oneShotPayoff G (D i) h x =
      AGT.expectedPayoff (fun j a => oneShotPayoffPure G (D j) h a)
        (fun j b => (x j b).toReal) i := by
  unfold oneShotPayoff AGT.expectedPayoff AGT.profileProb
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma oneShotPayoff_bdd (G : Game I S A) (Di : HistFun I S A) {n : ℕ}
    (h : Hist I S A n) (x : ∀ j, PMF (A j)) :
    |oneShotPayoff G Di h x| ≤ ∑ a : ∀ j, A j, |oneShotPayoffPure G Di h a| := by
  unfold oneShotPayoff
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  have h1 : |∏ j, (x j (a j)).toReal| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun j _ => ?_
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one (x j) (a j))
  calc |oneShotPayoffPure G Di h a| * |∏ j, (x j (a j)).toReal|
      ≤ |oneShotPayoffPure G Di h a| * 1 := by gcongr
    _ = _ := mul_one _

lemma minmax_le_of_eq (G : Game I S A) (D : I → HistFun I S A) {n : ℕ}
    (h : Hist I S A n) (x : ∀ j, PMF (A j)) (hx : IsOneShotEquilibrium G D h x) (i : I) :
    oneShotMinmax G i (D i) h ≤ oneShotPayoff G (D i) h x := by
  set M := ∑ a : ∀ j, A j, |oneShotPayoffPure G (D i) h a|
  have hb : ∀ z, |oneShotPayoff G (D i) h z| ≤ M := fun z => oneShotPayoff_bdd G (D i) h z
  have hle : ∀ y : PMF (A i), oneShotPayoff G (D i) h (Function.update x i y) ≤
      oneShotPayoff G (D i) h x := by
    intro y
    rw [oneShotPayoff_eq_expected G D h _ i, oneShotPayoff_eq_expected G D h _ i,
      toReal_update]
    refine hx.2 i _ ⟨fun b => ENNReal.toReal_nonneg, ?_⟩
    rw [← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top y b)]
    have := PMF.tsum_coe y
    rw [tsum_fintype] at this
    simp [this]
  unfold oneShotMinmax
  have hbdd : BddBelow (Set.range fun z : (∀ j, PMF (A j)) =>
      ⨆ y : PMF (A i), oneShotPayoff G (D i) h (Function.update z i y)) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨z, rfl⟩
    have h0 := hb (Function.update z i (PMF.pure (Classical.arbitrary (A i))))
    have hbu : BddAbove (Set.range fun y : PMF (A i) =>
        oneShotPayoff G (D i) h (Function.update z i y)) :=
      ⟨M, by rintro _ ⟨y, rfl⟩; exact (le_abs_self _).trans (hb _)⟩
    exact (neg_le_of_abs_le h0).trans (le_ciSup hbu _)
  refine (ciInf_le hbdd x).trans ?_
  exact ciSup_le hle

end GPSGThm44

open GPSGThm44

theorem solution {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
  (G : Game I S A) (ε : ℝ) (hε : 0 < ε) :
    (∀ D : I → HistFun I S A, (∀ i, IsMartinFunction G ε i (D i)) →
      ∀ x : (n : ℕ) → Hist I S A n → ∀ j, PMF (A j),
        (∀ n (h : Hist I S A n), Feasible G h → IsOneShotEquilibrium G D h (x n h)) →
        IsMinmaxAcceptable G ε (fun j n h => x n h j)) ∧
    ∃ σ : Profile G, IsMinmaxAcceptable G ε σ := by
  have part1 : ∀ D : I → HistFun I S A, (∀ i, IsMartinFunction G ε i (D i)) →
      ∀ x : (n : ℕ) → Hist I S A n → ∀ j, PMF (A j),
        (∀ n (h : Hist I S A n), Feasible G h → IsOneShotEquilibrium G D h (x n h)) →
        IsMinmaxAcceptable G ε (fun j n h => x n h j) := by
    intro D hD x hx i n h hh
    obtain ⟨_, h1, h2, h3⟩ := hD i
    have key := h3 n h hh (fun j n h => x n h j)
      (fun m h'' hh'' _ => minmax_le_of_eq G D h'' (x m h'') (hx m h'' hh'') i)
      n h hh ⟨le_rfl, fun k hk => rfl⟩
    linarith [(h1 n h hh).1, h2 n h hh]
  refine ⟨part1, ?_⟩
  choose D hD using fun i => theorem_3_1 G ε hε i
  have hN : ∀ n (h : Hist I S A n), ∃ x : ∀ j, PMF (A j), IsOneShotEquilibrium G D h x := by
    intro n h
    obtain ⟨σ, hσ⟩ := AGT.nash_existence A (fun j a => oneShotPayoffPure G (D j) h a)
    have hsum : ∀ j, ∑ b, ENNReal.ofReal (σ j b) = 1 := by
      intro j
      rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => (hσ.1 j).1 b), (hσ.1 j).2,
        ENNReal.ofReal_one]
    let x : ∀ j, PMF (A j) := fun j => PMF.ofFintype (fun b => ENNReal.ofReal (σ j b)) (hsum j)
    have hxσ : (fun j b => (x j b).toReal) = σ := by
      funext j b
      simp [x, PMF.ofFintype_apply, ENNReal.toReal_ofReal ((hσ.1 j).1 b)]
    refine ⟨x, ?_⟩
    unfold IsOneShotEquilibrium
    rw [hxσ]
    exact hσ
  choose x hx using hN
  exact ⟨_, part1 D hD x (fun n h _ => hx n h)⟩
