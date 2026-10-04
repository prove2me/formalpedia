-- Prove2me | solution 1 for BookProof.BddBelowFiberSumEsa.dsOp_semibounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:35:03.477377+00:00
-- url     : https://prove2.me/submissions/2cd8221b-92c7-4327-af42-9733bdeb1119

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterWallEsaSemibounded

set_option autoImplicit false

open BookProof.DirectSumEsa BookProof.WallEsaSemibounded BookProof.BddBelowFiberSumEsa in
theorem solution {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}
    (H : ∀ i, D i →ₗ[ℂ] G i) {c : ℝ} (h : ∀ i, SemiboundedBelowOn (D i) (H i) c) :
    SemiboundedBelowOn (dsCore D) (dsOp H) c := by
  classical
  intro v
  obtain ⟨hfin, hD⟩ := v.2
  set S := hfin.toFinset with hS
  have hx0 : ∀ i ∉ S, ((v : lp G 2) : ∀ i, G i) i = 0 := fun i hi => by
    by_contra hne
    exact hi (hfin.mem_toFinset.mpr hne)
  have h1 : (inner ℂ (dsOp H v) (v : lp G 2) : ℂ)
      = ∑ i ∈ S, inner ℂ ((H i) ⟨((v : lp G 2) : ∀ i, G i) i, hD i⟩ : G i)
          (((v : lp G 2) : ∀ i, G i) i) := by
    rw [lp.inner_eq_tsum, tsum_eq_sum]
    · rfl
    · intro i hi
      simp [hx0 i hi]
  have h2' : (inner ℂ (v : lp G 2) (v : lp G 2) : ℂ)
      = ∑ i ∈ S, inner ℂ (((v : lp G 2) : ∀ i, G i) i) (((v : lp G 2) : ∀ i, G i) i) := by
    rw [lp.inner_eq_tsum, tsum_eq_sum]
    intro i hi
    simp [hx0 i hi]
  have h2 : ‖(v : lp G 2)‖ ^ 2 = ∑ i ∈ S, ‖((v : lp G 2) : ∀ i, G i) i‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, h2', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← @norm_sq_eq_re_inner ℂ]
  rw [h1, h2, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact h i ⟨((v : lp G 2) : ∀ i, G i) i, hD i⟩
