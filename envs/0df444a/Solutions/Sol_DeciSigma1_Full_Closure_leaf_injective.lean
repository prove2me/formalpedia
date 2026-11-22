-- Prove2me | solution 1 for DeciSigma1.Full.Closure.leaf_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:42:12.347349+00:00
-- url     : https://prove2.me/submissions/79c144e1-0037-4bfb-b47d-8ace3e79ce18

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Theorems.Thm_DeciSigma1_Full_Closure_treeLe_iff_leaf
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_antisymm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Full.Closure
theorem _root_.solution (c : Fin n → Bool) :
    Function.Injective (fun t : Tree n => (leaf c t false, leaf c t true)) := by
  intro t u h
  have hp := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  apply treeLe_antisymm
  · exact (treeLe_iff_leaf c t u).mpr ⟨hp.subset, hm.symm.subset⟩
  · exact (treeLe_iff_leaf c u t).mpr ⟨hp.symm.subset, hm.subset⟩
end DeciSigma1.Full.Closure
