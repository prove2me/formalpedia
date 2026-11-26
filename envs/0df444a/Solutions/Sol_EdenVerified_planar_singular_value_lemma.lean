-- Prove2me | solution 1 for EdenVerified.planar_singular_value_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:30.293096+00:00
-- url     : https://prove2.me/submissions/05dc6ffd-53aa-4072-ab94-e8f78f928410

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_fderiv_planarEvolution_integrals


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (Ω : ℝ) (p : PlanarSpace)
    (t : ℝ) (ht : 0 < t) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} :=
  singularValues_fderiv_planarEvolution_integrals Ω ht.le p
end EdenVerified
