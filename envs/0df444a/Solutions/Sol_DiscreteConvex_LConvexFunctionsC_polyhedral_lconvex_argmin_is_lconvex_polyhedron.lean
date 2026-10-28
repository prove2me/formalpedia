-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_argmin_is_lconvex_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:26:17.102986+00:00
-- url     : https://prove2.me/submissions/fa92e5c2-c110-4851-b6dc-f893807ff740

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR

open DiscreteConvex.LConvexFunctionsC

namespace LArgAux

theorem add_coe_le_iff (a : WithTop ℝ) (S μ : ℝ) : a + (S : WithTop ℝ) ≤ μ ↔ a ≤ ((μ - S : ℝ) : WithTop ℝ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

theorem le_of_add_le (a b : WithTop ℝ) (μ : ℝ) (h : a + b ≤ (μ : WithTop ℝ) + μ) (hb : (μ : WithTop ℝ) ≤ b) :
    a ≤ μ := by
  have h2 : a + (μ : WithTop ℝ) ≤ (μ : WithTop ℝ) + μ := le_trans (add_le_add le_rfl hb) h
  exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).1 h2

end LArgAux

open LArgAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ)
    (hg : SBFR g ∧ TRFR g) (hpoly : IsPolyhedralConvex g) (x : V → ℝ)
    (hne : (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty) :
    LConvexPolyhedronR (ArgMinR (LinearWeightR g (fun v => - x v))) := by
  classical
  set G := LinearWeightR g (fun v => - x v) with hGdef
  have hG : ∀ p, G p = g p + ((∑ v, x v * p v : ℝ) : WithTop ℝ) := by
    intro p
    simp only [hGdef, LinearWeightR, neg_mul, Finset.sum_neg_distrib, neg_neg]
  obtain ⟨p0, hp0⟩ := hne
  by_cases hm : G p0 = ⊤
  · have huniv : ArgMinR G = Set.univ := by
      ext p
      simp only [ArgMinR, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro q
      have := hp0 q
      rw [hm, top_le_iff] at this
      rw [this]; exact le_top
    rw [huniv]
    refine ⟨⟨0, Fin.elim0, Fin.elim0, by ext; simp⟩, ?_, ⟨0, ?_⟩⟩
    · intro p q; simp
    · intro p α; simp
  obtain ⟨μ, hμ⟩ := WithTop.ne_top_iff_exists.1 hm
  have hmem : ∀ p, p ∈ ArgMinR G ↔ G p ≤ μ := by
    intro p
    constructor
    · intro hp; rw [hμ]; exact hp p0
    · intro hp q; exact le_trans hp (hμ ▸ hp0 q)
  have hlow : ∀ q, (μ : WithTop ℝ) ≤ G q := fun q => hμ ▸ hp0 q
  obtain ⟨r, hr⟩ := hg.2
  -- translation behaviour of G
  have hGtr : ∀ p α, G (fun v => p v + α) = G p + ((α * (r + ∑ v, x v) : ℝ) : WithTop ℝ) := by
    intro p α
    rw [hG, hG, hr, ← WithTop.coe_mul, add_assoc, add_assoc, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 2
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  have hs : r + ∑ v, x v = 0 := by
    have h1 := hlow (fun v => p0 v + 1)
    have h2 := hlow (fun v => p0 v + (-1))
    rw [hGtr, ← hμ, ← WithTop.coe_add, WithTop.coe_le_coe] at h1 h2
    linarith
  have htr : ∀ p α, G (fun v => p v + α) = G p := by
    intro p α; rw [hGtr, hs, mul_zero, WithTop.coe_zero, add_zero]
  -- submodularity of G
  have hGsb : ∀ p q, G (p ⊔ q) + G (p ⊓ q) ≤ G p + G q := by
    intro p q
    have h := hg.1 p q
    have hlin : (∑ v, x v * (p ⊔ q) v) + (∑ v, x v * (p ⊓ q) v) = (∑ v, x v * p v) + ∑ v, x v * q v := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro v _
      simp only [Pi.sup_apply, Pi.inf_apply]
      rw [← mul_add, ← mul_add, max_add_min]
    rw [hG, hG, hG, hG, add_add_add_comm, add_add_add_comm (g p), ← WithTop.coe_add, ← WithTop.coe_add,
      hlin]
    exact add_le_add_left h _
  refine ⟨?_, ?_, ⟨0, ?_⟩⟩
  · -- polyhedron
    obtain ⟨n, a, b, hab⟩ := hpoly
    refine ⟨n, fun i v => a i (some v) - a i none * x v, fun i => b i - a i none * μ, ?_⟩
    ext p
    rw [hmem, hG, add_coe_le_iff]
    let P : Option V → ℝ := fun o => Option.elim o (μ - ∑ v, x v * p v) p
    have hP : g p ≤ ((μ - ∑ v, x v * p v : ℝ) : WithTop ℝ) ↔ P ∈ {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)} := by
      simp [P]
    rw [hP, hab]
    simp only [Set.mem_setOf_eq, Fintype.sum_option, P, Option.elim]
    apply forall_congr'; intro i
    have e : ∑ v, (a i (some v) - a i none * x v) * p v
        = ∑ v, a i (some v) * p v - a i none * ∑ v, x v * p v := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro v _; ring
    rw [e]
    constructor <;> intro h <;> linarith
  · intro p q
    by_cases hp : p ∈ ArgMinR G
    · by_cases hq : q ∈ ArgMinR G
      · have hpq : G (p ⊔ q) + G (p ⊓ q) ≤ (μ : WithTop ℝ) + μ :=
          le_trans (hGsb p q) (add_le_add ((hmem p).1 hp) ((hmem q).1 hq))
        have h1 : p ⊔ q ∈ ArgMinR G := (hmem _).2 (le_of_add_le _ _ μ hpq (hlow _))
        have h2 : p ⊓ q ∈ ArgMinR G := (hmem _).2 (le_of_add_le _ _ μ (by rwa [add_comm]) (hlow _))
        simp [hp, hq, h1, h2]
      · simp [hq]
    · simp [hp]
  · intro p α
    have : (fun v => p v + α) ∈ ArgMinR G ↔ p ∈ ArgMinR G := by
      rw [hmem, hmem, htr]
    simp [this]
