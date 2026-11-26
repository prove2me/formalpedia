-- Prove2me | solution 1 for EdenVerified.D07_ordered_positive_singular_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:55.049387+00:00
-- url     : https://prove2.me/submissions/e0f19955-c55b-4f88-8ecb-9287545fad30

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_evolution_bijective
import Theorems.Thm_Eden_singularValues_evolution_pos
import Theorems.Thm_Eden_singularValues_fderiv_evolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Function.Bijective (fderiv ℝ (evolution c t) p) ∧
    Antitone (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (∀ i : Fin 5, 0 < (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) ∧
    (Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (derivativeFactors c t p)) := by
  refine ⟨fderiv_evolution_bijective c ht p, ?_, singularValues_evolution_pos c ht p,
    singularValues_fderiv_evolution c ht p⟩
  exact fun i j hij => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues_antitone hij
end EdenVerified
