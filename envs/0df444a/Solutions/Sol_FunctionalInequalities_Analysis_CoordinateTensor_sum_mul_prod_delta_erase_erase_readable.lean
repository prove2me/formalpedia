-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:56.294714+00:00
-- url     : https://prove2.me/submissions/92e80ffe-62df-418b-b8e0-8525ef5a76a3

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf3B1SecondOrderHelpers
variable {n r : ℕ}
/-- **Delta collapse on all slots but two**: for `s ≠ t`,
`Σ_{J'} f(J') Π_{s' ∉ {s,t}} δ_{J_{s'} J'_{s'}} = Σ_{k,l} f(J[s ↦ k][t ↦ l])`. -/
theorem solution (J : Fin r → Fin n) {s t : Fin r} (hst : s ≠ t)
    (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' *
        ∏ s' ∈ (Finset.univ.erase s).erase t, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by
  classical
  let p : (Fin r → Fin n) → Prop :=
    fun J' => ∀ u ∈ (Finset.univ.erase s).erase t, J u = J' u
  let q : (Fin n × Fin n) → (Fin r → Fin n) :=
    fun kl => Function.update (Function.update J s kl.1) t kl.2
  have hprod (J' : Fin r → Fin n) :
      (∏ u ∈ (Finset.univ.erase s).erase t,
          (if J u = J' u then (1 : ℝ) else 0)) =
        if p J' then 1 else 0 := by
    by_cases hp : p J'
    · simp only [p, if_pos hp]
      apply Finset.prod_eq_one
      intro u hu
      exact if_pos (hp u hu)
    · rw [if_neg hp]
      obtain ⟨u, hu, hne⟩ :
          ∃ u, u ∈ (Finset.univ.erase s).erase t ∧ J u ≠ J' u := by
        by_contra h
        apply hp
        intro u hu
        by_contra h'
        exact h ⟨u, hu, h'⟩
      exact Finset.prod_eq_zero hu (if_neg hne)
  have hfilter : Finset.univ.filter p = Finset.univ.image q := by
    ext J'
    constructor
    · intro hJ'
      have hp : p J' := (Finset.mem_filter.mp hJ').2
      have heq : q (J' s, J' t) = J' := by
        funext u
        by_cases hus : u = s
        · subst u
          change Function.update (Function.update J s (J' s)) t (J' t) s = J' s
          rw [Function.update_of_ne hst, Function.update_self]
        · by_cases hut : u = t
          · subst u
            change Function.update (Function.update J s (J' s)) t (J' t) t = J' t
            rw [Function.update_self]
          · have hu : u ∈ (Finset.univ.erase s).erase t := by
              simp [hus, hut]
            change Function.update (Function.update J s (J' s)) t (J' t) u = J' u
            rw [Function.update_of_ne hut, Function.update_of_ne hus]
            exact hp u hu
      exact Finset.mem_image.mpr ⟨(J' s, J' t), Finset.mem_univ _, heq⟩
    · intro hJ'
      obtain ⟨kl, -, rfl⟩ := Finset.mem_image.mp hJ'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro u hu
        have hut : u ≠ t := (Finset.mem_erase.mp hu).1
        have hus : u ≠ s :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
        change J u = Function.update (Function.update J s kl.1) t kl.2 u
        rw [Function.update_of_ne hut, Function.update_of_ne hus]
  have hq : Function.Injective q := by
    intro kl kl' hkl
    have hs' := congrFun hkl s
    have ht' := congrFun hkl t
    have hk : kl.1 = kl'.1 := by
      simpa only [q, Function.update_of_ne hst, Function.update_self] using hs'
    have hl : kl.2 = kl'.2 := by
      simpa only [q, Function.update_self] using ht'
    exact Prod.ext hk hl
  calc
    ∑ J' : Fin r → Fin n, f J' *
        ∏ u ∈ (Finset.univ.erase s).erase t,
          (if J u = J' u then (1 : ℝ) else 0) =
        ∑ J', if p J' then f J' else 0 := by
      apply Finset.sum_congr rfl
      intro J' _
      rw [hprod]
      by_cases hp : p J' <;> simp [hp]
    _ = ∑ J' ∈ Finset.univ.filter p, f J' := by
      rw [← Finset.sum_filter]
    _ = ∑ J' ∈ Finset.univ.image q, f J' := by
      rw [hfilter]
    _ = ∑ kl : Fin n × Fin n, f (q kl) := by
      rw [Finset.sum_image]
      intro kl _ kl' _ hEq
      exact hq hEq
    _ = ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by
      simpa only [q] using
        (Fintype.sum_prod_type
          (fun kl : Fin n × Fin n =>
            f (Function.update (Function.update J s kl.1) t kl.2)))
