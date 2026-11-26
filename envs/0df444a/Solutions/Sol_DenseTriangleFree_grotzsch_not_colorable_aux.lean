-- Prove2me | solution 1 for DenseTriangleFree.grotzsch_not_colorable_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:58.469012+00:00
-- url     : https://prove2.me/submissions/ec31d6bc-9ae3-4551-a2ad-8ba17bfd78dd

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000
namespace DenseTriangleFree
theorem _root_.solution : ∀ c0 c1 : Fin 3, c0 ≠ c1 → ∀ c2 : Fin 3, c1 ≠ c2 →
    ∀ c3 : Fin 3, c2 ≠ c3 → ∀ c4 : Fin 3, c3 ≠ c4 → c4 ≠ c0 →
    ∀ c5 : Fin 3, c5 ≠ c1 → c5 ≠ c4 → ∀ c6 : Fin 3, c6 ≠ c2 → c6 ≠ c0 →
    ∀ c7 : Fin 3, c7 ≠ c3 → c7 ≠ c1 → ∀ c8 : Fin 3, c8 ≠ c4 → c8 ≠ c2 →
    ∀ c9 : Fin 3, c9 ≠ c0 → c9 ≠ c3 →
    ∀ c10 : Fin 3, c10 ≠ c5 → c10 ≠ c6 → c10 ≠ c7 → c10 ≠ c8 → c10 ≠ c9 → False := by
  decide +kernel
end DenseTriangleFree
