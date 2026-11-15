-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-15T05:49:44.732608+00:00
-- url     : https://prove2.me/submissions/b2b16bf4-a08c-464b-a39e-ede9af54bd4b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_7_step

open Complex ComplexConjugate

/-! # DALAG Prop. 12.7

Write `n = dim_K V`. The claim, for every `d`, every `K`-subspace `V ⊂ K^d` meeting `k^d` only in `0` and every
`k`-free family `v₁, …, v_ℓ` in `V ∩ E^d`, is `2ℓ ≤ n(n + 1)`; it is proved by strong induction on `d`. For
`ℓ = 0` there is nothing to prove. Otherwise the inductive step gives `r ≤ n`, `r < d`, `ℓ₁ = ℓ − r`, a
`K`-subspace `V₁ ⊂ K^r` meeting `k^r` only in `0`, and a `k`-free family `w₁, …, w_{ℓ₁}` in `V₁ ∩ E^r`. The
induction hypothesis for `r` gives `2ℓ₁ ≤ n₁(n₁ + 1)` with `n₁ = dim_K V₁`. If `r ≥ 1`, then `V₁ ≠ K^r` (the
first unit vector is a non-zero vector of `k^r`), so `n₁ ≤ r − 1`; if `r = 0`, then `n₁ = 0`. Either way
`2ℓ = 2r + 2ℓ₁ ≤ r(r + 1) ≤ n(n + 1)`. Hence every finite `k`-free subset of `W = V ∩ E^d` has at most
`n(n + 1)/2` elements, so `W` has rank at most `n(n + 1)/2` over `k`: it is finite-dimensional, of dimension at
most `n(n + 1)/2`. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hE : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    {d : ℕ} (V : Submodule K (Fin d → K))
    (hV : ∀ v ∈ V, (∀ i, ∃ c : k, v i = algebraMap k K c) → v = 0) :
    FiniteDimensional k ↥(V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E)) ∧
    Module.finrank k ↥(V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E)) ≤
      Module.finrank K ↥V * (Module.finrank K ↥V + 1) / 2 := by
  classical
  -- the claim, by strong induction on d
  have C : ∀ d : ℕ, ∀ (V : Submodule K (Fin d → K)),
      (∀ v ∈ V, (∀ i, ∃ c : k, v i = algebraMap k K c) → v = 0) →
      ∀ (ℓ : ℕ) (v : Fin ℓ → Fin d → K), LinearIndependent k v → (∀ j, v j ∈ V) →
        (∀ j i, v j i ∈ E) → 2 * ℓ ≤ Module.finrank K ↥V * (Module.finrank K ↥V + 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro V hV ℓ v hv hvV hvE
      rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
      · simp [hℓ]
      obtain ⟨r, ℓ₁, V₁, w, hrℓ, hrn, hrd, hV₁, hw, hwV, hwE⟩ :=
        dalag_prop_12_7_step E hE V hV v hv hvV hvE hℓ
      have h1 := IH r hrd V₁ hV₁ ℓ₁ w hw hwV hwE
      have h2 : Module.finrank K ↥V₁ + 1 ≤ r ∨ (r = 0 ∧ Module.finrank K ↥V₁ = 0) := by
        rcases Nat.eq_zero_or_pos r with h0 | hr
        · subst h0
          right
          refine ⟨rfl, ?_⟩
          have := Submodule.finrank_le V₁
          rw [Module.finrank_fin_fun] at this
          omega
        · left
          have hne : V₁ ≠ ⊤ := by
            intro htop
            have hmem : (Pi.single (⟨0, hr⟩ : Fin r) (1 : K) : Fin r → K) ∈ V₁ := htop ▸ Submodule.mem_top
            have h0 := hV₁ _ hmem (fun i => by
              by_cases hi : i = ⟨0, hr⟩
              · exact ⟨1, by subst hi; simp⟩
              · exact ⟨0, by simp [hi]⟩)
            have := congrFun h0 ⟨0, hr⟩
            simp at this
          have hlt := Submodule.finrank_lt hne
          rw [Module.finrank_fin_fun] at hlt
          omega
      rcases h2 with h2 | ⟨h0, h2⟩
      · nlinarith
      · subst h0; rw [h2] at h1; omega
  -- the bound for finite free families of W
  set W := V.restrictScalars k ⊓ Submodule.pi Set.univ (fun _ : Fin d => E) with hW
  set n := Module.finrank K ↥V
  have H : ∀ s : Finset ↥W, LinearIndependent k (fun i : s => (i : ↥W)) → s.card ≤ n * (n + 1) / 2 := by
    intro s hs
    let f : Fin s.card → Fin d → K := fun i => ((s.equivFin.symm i : s) : ↥W).1
    have hf : LinearIndependent k f := by
      have h1 : LinearIndependent k (fun i : Fin s.card => ((s.equivFin.symm i : s) : ↥W)) :=
        hs.comp _ s.equivFin.symm.injective
      exact h1.map' W.subtype (Submodule.ker_subtype W)
    have hfW : ∀ i, f i ∈ W := fun i => ((s.equivFin.symm i : s) : ↥W).2
    have hfV : ∀ j, f j ∈ V := fun j => (Submodule.mem_inf.mp (hfW j)).1
    have hfE : ∀ j i, f j i ∈ E := fun j i => (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hfW j)).2) i
      (Set.mem_univ _)
    have h2 := C d V hV s.card f hf hfV hfE
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    linarith
  have hr : Module.rank k ↥W ≤ (n * (n + 1) / 2 : ℕ) := rank_le H
  have hfin : FiniteDimensional k ↥W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hr (Cardinal.natCast_lt_aleph0 (n := n * (n + 1) / 2)))
  exact ⟨hfin, Module.finrank_le_of_rank_le hr⟩
