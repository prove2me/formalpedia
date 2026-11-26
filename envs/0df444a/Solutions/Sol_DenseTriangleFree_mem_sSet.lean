-- Prove2me | solution 1 for DenseTriangleFree.mem_sSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:05.393275+00:00
-- url     : https://prove2.me/submissions/b68b9b56-aebe-429b-93e4-784da6560c30

module
public import Mathlib
public import Definitions.Def_JinLib_Heavy
public import Definitions.Def_JinLib_Pairs

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace DenseTriangleFree
theorem _root_.solution {a : V} {U : Fin 5 → V} {i : Fin 5} :
    i ∈ sSet G a U ↔ ∃ t, G.Adj a t ∧ G.Adj (U (i - 1)) t ∧ G.Adj (U (i + 1)) t := by
  classical
  simp [sSet]
end DenseTriangleFree
