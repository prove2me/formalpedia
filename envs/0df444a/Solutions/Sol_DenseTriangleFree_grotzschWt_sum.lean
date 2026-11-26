-- Prove2me | solution 1 for DenseTriangleFree.grotzschWt_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:03.938631+00:00
-- url     : https://prove2.me/submissions/240eec00-0c8c-4169-aa36-cdf9d1296eb0

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution : ∑ i, grotzschWt i = 29 := by decide
end DenseTriangleFree
