-- Prove2me | solution 1 for DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:40.350708+00:00
-- url     : https://prove2.me/submissions/c2d8351d-8746-4763-99bc-498dcc198352

module
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Theorems.Thm_DeciSigma1_Logic_BooleanSentence_all_iff_not_ex_not
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_realizable_iff_not_disjEntailsIn
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D : Type} {I : Interpretation T D} (F : Flattening I)
variable [∀ m, DecidableEq (T (Fin m))] {C : D → Prop}
omit [(m : ℕ) → DecidableEq (T (Fin m))]
namespace DeciSigma1.Logic
namespace BooleanSentence
theorem _root_.solution {C C' : D → Prop} (hC : I.TermClosed C)
    (hC' : I.TermClosed C')
    (h : ∀ {W : Type} [Fintype W] [DecidableEq W] {k : ℕ} (Γ : List (F.Lit W))
      (q : Fin k → W × W), F.DisjEntailsIn C Γ q ↔ F.DisjEntailsIn C' Γ q)
    (φ : BooleanSentence T) : φ.HoldsIn I C ↔ φ.HoldsIn I C' := by
  classical
  have hs (s : Sigma1 T) : s.HoldsIn I C ↔ s.HoldsIn I C' := by
    rw [s.holdsIn_iff_exists_realizable, s.holdsIn_iff_exists_realizable]
    refine exists_congr fun c => and_congr_right fun _ => ?_
    exact (c.realizable_iff_not_disjEntailsIn F hC).trans
      ((not_congr (h _ _)).trans (c.realizable_iff_not_disjEntailsIn F hC').symm)
  induction φ with
  | ex s => exact hs s
  | all s => simp only [BooleanSentence.all_iff_not_ex_not, hs]
  | not φ ih => exact not_congr ih
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ => exact or_congr ihφ ihψ
end BooleanSentence
end DeciSigma1.Logic
