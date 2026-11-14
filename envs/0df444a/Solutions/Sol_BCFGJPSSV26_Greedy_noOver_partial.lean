-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.noOver_partial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:57:39.014326+00:00
-- url     : https://prove2.me/submissions/bc679a45-c5d9-43f4-b15a-475a3c130669

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid
import all Definitions.Def_BCFGJPSSV26_Greedy_Valid
public import Theorems.Thm_BCFGJPSSV26_Greedy_noOver_raise

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

/-- **No overbidding** ([BCFGJPSSV26a, Lemmas E.6 and D.9]): at the
start of sequence `p = Hp.length` after `η`-valid sequences `Hp`, for every set of atoms added. -/
theorem noOver_partial (hP : P.Good n) (hd1 : ∀ j i, 1 ≤ d j i) {f η : ℚ} (hf : 0 ≤ f)
    {Hp : List (List (Atom m))} (hv : EtaValid P d f η Hp) (S : List (Atom m)) :
    NoOver P d f (P.θseq Hp.length) (profL P.K d (Hp.flatten ++ S)) := by
  have hd0 : ∀ j i, 0 ≤ d j i := fun j i ↦ zero_le_one.trans (hd1 j i)
  induction Hp using List.reverseRecOn generalizing S with
  | nil =>
    have h1 : P.θseq ([] : List (List (Atom m))).length = 1 := by
      simp [Par.θseq, Par.θ]
    rw [h1]
    exact noOver_start hd1 hf _
  | append_singleton Hp H ih =>
    have hv' : EtaValid P d f η Hp := fun p hp ↦ by
      have := hv p (by rw [List.length_append]; omega)
      rwa [List.take_append_of_le_length hp.le, List.getElem_append_left hp] at this
    have hH : ValidSeq P d f η Hp.length Hp.flatten H := by
      have := hv Hp.length (by simp)
      simpa using this
    rw [List.length_append, List.length_singleton, List.flatten_append, List.flatten_singleton,
      List.append_assoc]
    rcases Nat.mod_two_eq_zero_or_one Hp.length with he | ho
    · -- after a sequence of type 1, the time is the same
      have : P.θseq (Hp.length + 1) = P.θseq Hp.length := by
        unfold Par.θseq
        congr 1
        omega
      rw [this]
      exact ih hv' (H ++ S)
    · -- after a maximal sequence of type 2, the time is raised
      have hθ : P.θseq (Hp.length + 1) = P.θplus (P.θseq Hp.length) := by
        unfold Par.θseq Par.θplus
        rw [← Par.θ_succ]
        congr 1
        omega
      rw [hθ]
      have hmax : ∀ i, ¬ Open2 P d f 0 (P.θseq Hp.length) (profL P.K d (Hp.flatten ++ H)) i := by
        have ht : typ1 Hp.length = false := by simp [typ1, ho]
        have := hH.2
        unfold Maximal at this
        simpa [ht, OpenT] using this
      have h2 := noOver_raise hP hd0 (θseq_pos P _) (ih hv' H) hmax
      refine h2.mono hP fun j ↦ ?_
      rw [← List.append_assoc]
      exact profL_anti _ _ (pairs_mono (List.subset_append_left _ _)) j

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.noOver_partial := @BCFGJPSSV26.Greedy.noOver_partial
