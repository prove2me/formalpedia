-- Prove2me | solution 1 for CompactnessConjecture.symplectic_triangle_points_collinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/df2f40ed-09d9-445e-9ee8-2641423bd13e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_sup_finrank
import Theorems.Thm_CompactnessConjecture_symplectic_isotropic_finrank_le_two

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {p q r : SymplecticPoint K} (hpq : p ≠ q)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    r.1 ≤ Lpq.1 := by
  let T : Submodule K (SymplecticVector K) :=
    (p.1 ⊔ q.1) ⊔ r.1
  have hiso : ∀ u ∈ T, ∀ v ∈ T,
      standardSymplecticForm K u v = 0 := by
    intro u hu v hv
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    obtain ⟨de, hde, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hde
    have had := Lpq.2.2 a (hpLpq ha) d (hpLpq hd)
    have hae := Lpq.2.2 a (hpLpq ha) e (hqLpq he)
    have haf := Lpr.2.2 a (hpLpr ha) f (hrLpr hf)
    have hbd := Lpq.2.2 b (hqLpq hb) d (hpLpq hd)
    have hbe := Lpq.2.2 b (hqLpq hb) e (hqLpq he)
    have hbf := Lqr.2.2 b (hqLqr hb) f (hrLqr hf)
    have hcd := Lpr.2.2 c (hrLpr hc) d (hpLpr hd)
    have hce := Lqr.2.2 c (hrLqr hc) e (hqLqr he)
    have hcf := Lpr.2.2 c (hrLpr hc) f (hrLpr hf)
    simp [standardSymplecticForm_add_left,
      standardSymplecticForm_add_right,
      had, hae, haf, hbd, hbe, hbf, hcd, hce, hcf]
  have hbound : Module.finrank K T ≤ 2 :=
    symplectic_isotropic_finrank_le_two K T hiso
  have hspan : p.1 ⊔ q.1 = T :=
    Submodule.eq_of_le_of_finrank_le le_sup_left
      (by simpa [symplecticPoint_sup_finrank K hpq] using hbound)
  exact (show r.1 ≤ T from le_sup_right).trans
    (hspan.symm ▸ sup_le hpLpq hqLpq)
end CompactnessConjecture
