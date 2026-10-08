-- Prove2me | solution 1 for BarvinokCount.ShortFormula.isPrimitive_iff_coneIndex_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:50:23.359609+00:00
-- url     : https://prove2.me/submissions/c079e8b0-32f5-4d65-82a6-80b6ab90cd76

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_coneIndex

namespace BarvinokCount.ShortFormula.Aux

open BarvinokCount.ShortFormula

theorem castVec_sub_sum {d k : ℕ} (u : Fin k → Fin d → ℤ) (z : Fin d → ℤ) (m : Fin k → ℤ) :
    castVec (z - ∑ i, m i • u i) = castVec z - ∑ i, (m i : ℝ) • castVec (u i) := by
  funext l
  simp [castVec, Finset.sum_apply, smul_eq_mul]

theorem castVec_sum {d k : ℕ} (u : Fin k → Fin d → ℤ) (m : Fin k → ℤ) :
    castVec (∑ i, m i • u i) = ∑ i, (m i : ℝ) • castVec (u i) := by
  funext l
  simp [castVec, Finset.sum_apply, smul_eq_mul]

theorem castVec_inj {d : ℕ} (z w : Fin d → ℤ) (h : castVec z = castVec w) : z = w := by
  funext l
  have := congrFun h l
  simpa [castVec] using this

theorem box_iff {d k : ℕ} (u : Fin k → Fin d → ℤ) (hu : IsSimpleGens u) :
    IsPrimitiveGens u ↔ ∀ z : Fin d → ℤ, castVec z ∈ halfOpenBox u → z = 0 := by
  constructor
  · rintro ⟨-, hp⟩ z ⟨α, hα, hz⟩
    have hspan : castVec z ∈ Submodule.span ℝ (Set.range fun i => castVec (u i)) := by
      rw [hz]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨m, hm⟩ := hp z hspan
    have hzc := castVec_sum u m
    rw [← hm, hz] at hzc
    have key := (Fintype.linearIndependent_iff.mp hu) (fun i => α i - (m i : ℝ)) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [hzc, sub_self])
    have hm0 : ∀ i, m i = 0 := by
      intro i
      have h1 : α i = (m i : ℝ) := sub_eq_zero.mp (key i)
      have h2 := hα i
      rw [h1] at h2
      have a : (0 : ℤ) ≤ m i := by exact_mod_cast h2.1
      have b : m i < 1 := by exact_mod_cast h2.2
      omega
    rw [hm]
    simp [hm0]
  · intro hbox
    refine ⟨hu, fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp hz
    refine ⟨fun i => ⌊c i⌋, ?_⟩
    have hw : castVec (z - ∑ i, ⌊c i⌋ • u i) ∈ halfOpenBox u := by
      refine ⟨fun i => Int.fract (c i), fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
      rw [castVec_sub_sum, ← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul]
      rfl
    have := hbox _ hw
    exact sub_eq_zero.mp this

end BarvinokCount.ShortFormula.Aux

open BarvinokCount.ShortFormula in
theorem solution {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) :
    IsPrimitiveGens u ↔ coneIndex u = 1 := by
  rw [BarvinokCount.ShortFormula.Aux.box_iff u hu, coneIndex, Nat.card_eq_one_iff_unique]
  have h0 : castVec (0 : Fin d → ℤ) ∈ halfOpenBox u :=
    ⟨fun _ => 0, fun _ => ⟨le_refl _, zero_lt_one⟩, by funext l; simp [castVec]⟩
  constructor
  · intro h
    refine ⟨⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩, ⟨⟨0, h0⟩⟩⟩
  · rintro ⟨hs, -⟩ z hz
    have := hs.elim ⟨z, hz⟩ ⟨0, h0⟩
    exact congrArg Subtype.val this
