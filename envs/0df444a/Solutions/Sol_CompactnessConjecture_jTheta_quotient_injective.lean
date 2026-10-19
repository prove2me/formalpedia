-- Prove2me | solution 1 for CompactnessConjecture.jTheta_quotient_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/d7a499f8-b3cc-4506-b8c6-8e4265e6b4f6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : JVertex → JVertex} (hf : JAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 2 =>
      f (jThetaVertex copy v)) := by
  intro u v heq
  have htemplate : jThetaVertex copy u = jThetaVertex copy v :=
    hf.2.2 copy (jThetaVertex_mem copy u)
      (jThetaVertex_mem copy v) heq
  exact (jThetaCopy copy).injective htemplate
end CompactnessConjecture
