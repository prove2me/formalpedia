-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.qexcw_iff_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:38:09.119197+00:00
-- url     : https://prove2.me/submissions/278777eb-c85b-49cd-b08e-abc702005e90

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw

set_option autoImplicit false

open DiscreteConvex.MConvexFunctionsE Classical Pointwise in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    QEXCw B ↔ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B := by
  constructor
  · intro h x hx
    suffices H : ∀ n : ℕ, ∀ y ∈ B, (∑ w, (x w - y w).natAbs) = n → x ≠ y →
        ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
          (fun w => x w - CharVec u w + CharVec v w) ∈ B by
      intro y hy hxy
      exact H _ y hy rfl hxy
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro y hy hn hxy
    obtain ⟨u, hu, v, hv, h1 | h2⟩ := h x hx y hy hxy
    · exact ⟨u, hu, v, hv, h1⟩
    · have hu' : y u < x u := by simpa [SuppPos] using hu
      have hv' : x v < y v := by simpa [SuppNeg] using hv
      have huv : u ≠ v := by
        rintro rfl
        omega
      by_cases hxy' : x = fun w => y w + CharVec u w - CharVec v w
      · refine ⟨u, hu, v, hv, ?_⟩
        convert hy using 1
        funext w
        rw [hxy']
        ring
      · have hlt : (∑ w, (x w - (fun w => y w + CharVec u w - CharVec v w) w).natAbs) < n := by
          rw [← hn]
          apply Finset.sum_lt_sum
          · intro w _
            simp only [CharVec]
            by_cases hwu : w = u
            · subst hwu
              simp [huv]
              omega
            · by_cases hwv : w = v
              · subst hwv
                simp [hwu]
                omega
              · simp [hwu, hwv]
          · refine ⟨u, Finset.mem_univ _, ?_⟩
            simp [CharVec, huv]
            omega
        obtain ⟨u', hu2, v', hv2, h'⟩ := ih _ hlt _ h2 rfl hxy'
        refine ⟨u', ?_, v', ?_, h'⟩
        · have hu3 : y u' + CharVec u u' - CharVec v u' < x u' := (Finset.mem_filter.mp hu2).2
          unfold CharVec at hu3
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          split_ifs at hu3 <;> subst_vars <;> omega
        · have hv3 : x v' < y v' + CharVec u v' - CharVec v v' := (Finset.mem_filter.mp hv2).2
          unfold CharVec at hv3
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          split_ifs at hv3 <;> subst_vars <;> omega
  · intro h x hx y hy hxy
    obtain ⟨u, hu, v, hv, h1⟩ := h x hx y hy hxy
    exact ⟨u, hu, v, hv, Or.inl h1⟩
