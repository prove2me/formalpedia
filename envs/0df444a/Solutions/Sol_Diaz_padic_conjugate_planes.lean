-- Prove2me | solution 1 for Diaz.padic_conjugate_planes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:12:05.489321+00:00
-- url     : https://prove2.me/submissions/ce4d5028-dbaf-4d0b-a53f-0ddb267c8efa

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {F : Type*} [Field F] (A : Subfield F) (V : Set F)
    (hVadd : ∀ y ∈ V, ∀ z ∈ V, y + z ∈ V)
    (hVmul : ∀ c ∈ A, ∀ y ∈ V, c * y ∈ V)
    (hone : (1 : F) ∈ V)
    {u v : F} (hu : u ∈ V) (hv : v ∈ V) (hq : u * v ∈ A) (hvA : v ∉ A)
    {x a b : F} (ha : a ∈ A) (hb : b ∈ A) (hx : x = a + b * u)
    (hbound : ∀ y₁ y₂ y₃ : F, y₁ ∈ V → x * y₁ ∈ V → y₂ ∈ V → x * y₂ ∈ V →
      y₃ ∈ V → x * y₃ ∈ V →
      ∃ c₁ ∈ A, ∃ c₂ ∈ A, ∃ c₃ ∈ A,
        ¬ (c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0) ∧ c₁ * y₁ + c₂ * y₂ + c₃ * y₃ = 0) :
    ∀ y : F, (y ∈ V ∧ x * y ∈ V) ↔ ∃ C ∈ A, ∃ D ∈ A, y = C + D * v := by
  have hxone : x * 1 ∈ V := by
    rw [hx, mul_one]
    exact hVadd a (by simpa using hVmul a ha 1 hone) (b * u) (hVmul b hb u hu)
  have hxv : x * v ∈ V := by
    have he : x * v = a * v + (b * (u * v)) := by rw [hx]; ring
    rw [he]
    exact hVadd (a * v) (hVmul a ha v hv) (b * (u * v))
      (by simpa using hVmul (b * (u * v)) (A.mul_mem hb hq) 1 hone)
  intro y
  constructor
  · rintro ⟨hy, hxy⟩
    obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hnz, hrel⟩ :=
      hbound 1 v y hone hxone hv hxv hy hxy
    have hc₃0 : c₃ ≠ 0 := by
      intro h
      subst h
      have h2 : c₁ + c₂ * v = 0 := by linear_combination hrel
      have hc₂0 : c₂ = 0 := by
        by_contra hc
        apply hvA
        have : v = -c₁ / c₂ := by rw [eq_div_iff hc]; linear_combination h2
        rw [this]
        exact div_mem (neg_mem hc₁) hc₂
      subst hc₂0
      have : c₁ = 0 := by linear_combination h2
      exact hnz ⟨this, rfl, rfl⟩
    refine ⟨-c₁ / c₃, div_mem (neg_mem hc₁) hc₃, -c₂ / c₃, div_mem (neg_mem hc₂) hc₃, ?_⟩
    have hyv : y = (-c₁ + -c₂ * v) / c₃ := by
      rw [eq_div_iff hc₃0]; linear_combination hrel
    rw [hyv]; ring
  · rintro ⟨C, hC, D, hD, rfl⟩
    constructor
    · exact hVadd C (by simpa using hVmul C hC 1 hone) (D * v) (hVmul D hD v hv)
    · have he : x * (C + D * v)
          = (a * C + b * D * (u * v)) * 1 + ((b * C) * u + (a * D) * v) := by
        rw [hx]; ring
      rw [he]
      refine hVadd _ (hVmul _ (A.add_mem (A.mul_mem ha hC)
        (A.mul_mem (A.mul_mem hb hD) hq)) 1 hone) _ ?_
      exact hVadd _ (hVmul _ (A.mul_mem hb hC) u hu) _ (hVmul _ (A.mul_mem ha hD) v hv)
