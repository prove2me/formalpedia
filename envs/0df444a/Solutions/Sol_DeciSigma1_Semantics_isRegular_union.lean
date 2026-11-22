-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegular_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:23.229467+00:00
-- url     : https://prove2.me/submissions/95e543d4-97f6-49c9-a388-26fda4e2afde

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (A ∪ B) := by
  apply (ha.image2 (· ∪ ·) hb).subset
  rintro _ ⟨u,rfl⟩
  exact ⟨residual A u, ⟨u,rfl⟩, residual B u, ⟨u,rfl⟩, rfl⟩
end DeciSigma1.Semantics
