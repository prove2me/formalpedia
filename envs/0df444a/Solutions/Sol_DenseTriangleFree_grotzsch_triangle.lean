-- Prove2me | solution 1 for DenseTriangleFree.grotzsch_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:00.82683+00:00
-- url     : https://prove2.me/submissions/d5b13304-d1b8-4b18-90a0-ef50635759a3

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
namespace DenseTriangleFree
theorem _root_.solution (a b c : Fin 11) (hab : grotzsch.Adj a b) (hbc : grotzsch.Adj b c)
    (hac : grotzsch.Adj a c) : False := by
  revert a b c
  decide
end DenseTriangleFree
