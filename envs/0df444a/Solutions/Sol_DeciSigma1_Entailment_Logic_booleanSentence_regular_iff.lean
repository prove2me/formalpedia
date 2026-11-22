-- Prove2me | solution 1 for DeciSigma1.Entailment.Logic.booleanSentence_regular_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:19:22.528853+00:00
-- url     : https://prove2.me/submissions/4fa62284-5a05-4916-ac58-8081244e85ff

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Logic
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_regular_iff
public import Theorems.Thm_DeciSigma1_Logic_BooleanSentence_holdsIn_iff_of_disjEntailsIn_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment DeciSigma1.Entailment.Logic
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n : ℕ} {V W : Type}
variable [Fintype V] [DecidableEq V]
namespace DeciSigma1.Entailment.Logic
theorem _root_.solution (φ : BooleanSentence n) :
    φ.HoldsIn IsRegularTree ↔ φ.HoldsIn (fun _ => True) :=
  DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff (flattening n)
    bfTermClosed_reg.eval bfTermClosed_all.eval
    (fun Γ q => show (flattening n).DisjEntailsIn IsRegularTree Γ q ↔
      (flattening n).DisjEntailsIn (fun _ => True) Γ q from disjEntailsIn_regular_iff Γ q) φ
end DeciSigma1.Entailment.Logic
