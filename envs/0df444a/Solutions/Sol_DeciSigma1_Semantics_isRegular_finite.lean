-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegular_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:08.621641+00:00
-- url     : https://prove2.me/submissions/658f1896-14ed-4ded-a7bc-b94ef6449833

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
theorem _root_.solution {L : Language n} (hf : L.Finite) : IsRegular L := by
  let R : Language n := ⋃ w ∈ L, {v | v.IsSuffix w}
  have hR : R.Finite := hf.biUnion fun w _ => by
    apply (List.finite_length_le (Fin n) w.length).subset
    exact fun _ hv => hv.length_le
  apply (hR.powerset).subset
  rintro _ ⟨u,rfl⟩ v hv
  exact Set.mem_iUnion.mpr ⟨u ++ v, Set.mem_iUnion.mpr ⟨hv, u, rfl⟩⟩
end DeciSigma1.Semantics
