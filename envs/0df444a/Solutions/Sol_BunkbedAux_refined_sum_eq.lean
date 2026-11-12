-- Prove2me | solution 1 for BunkbedAux.refined_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:19:15.88381+00:00
-- url     : https://prove2.me/submissions/c2103fe5-fbe0-4f86-8a12-58716735e834

import Definitions.Def_BunkbedWZRefined
open Bunkbed.Hyper Bunkbed.Hyper.WZExt Finset

private lemma wz_sum {M : Type*} [AddCommMonoid M] (f : WZ → M) :
    ∑ s : WZ, f s = f .abc + f .ab_c + f .ac_b + f .a_bc + f .a_b_c := by
  show Finset.sum {WZ.abc, WZ.ab_c, WZ.ac_b, WZ.a_bc, WZ.a_b_c} f = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

private lemma fibre_sum (P : WZ → ℚ) (a b : WZ) :
    ∑ q ∈ univ.filter (fun q : WZExt => legal q = true ∧ toPair q = (a, b)), wt P q
      = P a * P b := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [wz_sum, Fin.sum_univ_four]
  cases a <;> cases b <;> simp [wt, toPair, legal] <;> ring

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (P : WZ → ℚ)
    (g : (ι → WZ × WZ) → ℚ) :
    ∑ Ψ ∈ univ.filter (fun Ψ : ι → WZExt => ∀ i, legal (Ψ i) = true),
        (∏ i, wt P (Ψ i)) * g (fun i => toPair (Ψ i))
      = ∑ φ : ι → WZ × WZ, (∏ i, P (φ i).1 * P (φ i).2) * g φ := by
  have hmaps : ∀ Ψ ∈ univ.filter (fun Ψ : ι → WZExt => ∀ i, legal (Ψ i) = true),
      (fun i => toPair (Ψ i)) ∈ (univ : Finset (ι → WZ × WZ)) := fun Ψ _ => mem_univ _
  have key := Finset.sum_fiberwise_of_maps_to hmaps
      (fun Ψ : ι → WZExt => (∏ i, wt P (Ψ i)) * g (fun i => toPair (Ψ i)))
  rw [← key]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  have hset : (univ.filter (fun Ψ : ι → WZExt => ∀ i, legal (Ψ i) = true)).filter
        (fun Ψ => (fun i => toPair (Ψ i)) = φ)
      = Fintype.piFinset
          (fun i => univ.filter (fun q : WZExt => legal q = true ∧ toPair q = φ i)) := by
    ext Ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
    exact ⟨fun ⟨hl, hp⟩ i => ⟨hl i, hp i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [hset]
  have hconst : ∀ Ψ ∈ Fintype.piFinset
      (fun i => univ.filter (fun q : WZExt => legal q = true ∧ toPair q = φ i)),
      (∏ i, wt P (Ψ i)) * g (fun i => toPair (Ψ i)) = (∏ i, wt P (Ψ i)) * g φ := by
    intro Ψ hΨ
    have harg : (fun i => toPair (Ψ i)) = φ := by
      funext i
      exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hΨ i)).2.2
    rw [harg]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, ← Finset.prod_univ_sum]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => fibre_sum P (φ i).1 (φ i).2)
