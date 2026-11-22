-- Prove2me | solution 1 for DeciSigma1.Full.Logic.booleanSentence_regular_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:18:34.621083+00:00
-- url     : https://prove2.me/submissions/5185c51b-0015-4401-a9d6-cefadcd61a2c

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_regular_iff
public import Theorems.Thm_DeciSigma1_Logic_BooleanSentence_holdsIn_iff_of_disjEntailsIn_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Semantics DeciSigma1.Full.Models
variable {n : ℕ} {V W : Type}
variable (c : Fin n → Bool)
namespace DeciSigma1.Full.Logic
theorem _root_.solution (φ : BooleanSentence n) :
    φ.HoldsIn RegularTop c ↔ φ.HoldsIn (fun _ => True) c :=
  DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff (flattening c)
    (termClosed_reg.eval c) (termClosed_all.eval c)
    (fun Γ q => show (flattening c).DisjEntailsIn RegularTop Γ q ↔
      (flattening c).DisjEntailsIn (fun _ => True) Γ q from Reduction.disjEntails_regular_iff) φ
end DeciSigma1.Full.Logic
