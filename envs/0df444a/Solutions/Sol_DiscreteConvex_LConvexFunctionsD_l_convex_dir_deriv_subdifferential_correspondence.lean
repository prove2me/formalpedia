-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.l_convex_dir_deriv_subdifferential_correspondence
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:20:37.930988+00:00
-- url     : https://prove2.me/submissions/df98794d-c9ff-44f3-8d47-b0b269b940b6

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LovaszExtension
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_BasePolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DirDeriv
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SubDifferentialRZ

open Classical
open scoped Pointwise

namespace DisDDS
open DiscreteConvex.LConvexFunctionsD

noncomputable def g0 : (Unit → ℤ) → WithTop ℝ := fun n => ((-((n () : ℝ)) ^ 2 : ℝ) : WithTop ℝ)

lemma sbf : SBF g0 := by
  intro p q
  simp only [g0, Pi.sup_apply, Pi.inf_apply]
  rcases le_total (p ()) (q ()) with h | h
  · rw [sup_of_le_right h, inf_of_le_left h, add_comm]
  · rw [sup_of_le_left h, inf_of_le_right h]

lemma dom : (0 : Unit → ℤ) ∈ DomZ g0 := by simp [DomZ, g0]

lemma sub_empty : ¬ (SubDifferentialRZ g0 0).Nonempty := by
  rintro ⟨x, hx⟩
  have h1 := hx (fun _ => 1)
  have h2 := hx (fun _ => -1)
  simp only [g0, Fintype.sum_unique, Pi.zero_apply] at h1 h2
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ge_iff_le, WithTop.coe_le_coe] at h1 h2
  push_cast at h1 h2
  linarith

end DisDDS

open DiscreteConvex.LConvexFunctionsD in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ g : (V → ℝ) → WithTop ℝ, (SBFR g ∧ TRFR g) → ∀ p ∈ DomR g,
      SubmodularSetFunction (fun X => DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0)) ∧
      SubDifferentialR g p =
        BasePolyhedron (fun X => DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0)) ∧
      MConvexPolyhedronR (SubDifferentialR g p) ∧
      (∀ d : V → ℝ, DirDeriv g p d =
        LovaszExtension (fun X => DirDeriv g p (fun v => if v ∈ X then (1 : ℝ) else 0)) d) ∧
      (SubDifferentialR g p).Nonempty) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, SBF g → ∀ p ∈ DomZ g,
      SubmodularSetFunction (fun X => g (fun v => p v + IndicatorVec X v) - g p) ∧
      SubDifferentialRZ g p =
        BasePolyhedron (fun X => g (fun v => p v + IndicatorVec X v) - g p) ∧
      MConvexPolyhedron (SubDifferentialRZ g p) ∧
      (∀ d : V → ℝ, DirDeriv (fun q => ConvexClosureVal g q) (fun v => (p v : ℝ)) d =
        LovaszExtension (fun X => g (fun v => p v + IndicatorVec X v) - g p) d) ∧
      (SubDifferentialRZ g p).Nonempty)) := by
  intro h
  exact DisDDS.sub_empty ((h.2 DisDDS.g0 DisDDS.sbf 0 DisDDS.dom).2.2.2.2)
