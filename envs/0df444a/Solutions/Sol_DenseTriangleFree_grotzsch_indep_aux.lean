-- Prove2me | solution 1 for DenseTriangleFree.grotzsch_indep_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:02.930861+00:00
-- url     : https://prove2.me/submissions/10a85570-49f9-4aba-86aa-28948a00fafb

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
set_option maxRecDepth 100000
namespace DenseTriangleFree
theorem _root_.solution : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    grotzschIndepB ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = true →
      grotzschWtB ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] ≤ 10 := by
  decide +kernel
end DenseTriangleFree
