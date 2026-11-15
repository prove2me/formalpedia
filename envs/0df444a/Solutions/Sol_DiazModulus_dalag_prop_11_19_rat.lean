-- Prove2me | solution 1 for DiazModulus.dalag_prop_11_19_rat
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-15T05:45:39.693538+00:00
-- url     : https://prove2.me/submissions/f48473cc-c985-4576-a2a6-0091b985c3d1

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rat_theorem_four

open Complex ComplexConjugate

/-! # DALAG Proposition 11.19 for `(ℚ, ℚ + ℒ)` at a ℚ-rational subspace of minimal ratio

Let `U ≤ ℂ^d` have dimension `n < d`, let `T ≠ ℂ^d` be a ℚ-rational subspace that minimises
`(n − dim(U ∩ T))/(d − dim T)` among the ℚ-rational proper subspaces, and put
`W = U ∩ (ℚ + ℒ)^d`, a ℚ-vector space, `d′ = d − dim T ≥ 1` and `n′ = n − dim(U ∩ T)`.
The last claim `n′d ≤ nd′` is the minimality tested at the zero subspace; together with `n < d`
it gives `n′ < d′`.

A ℚ-free family `q₁, …, q_k` in the quotient `W/(W ∩ T)` lifts to vectors `w₁, …, w_k ∈ W`. They
lie in `U`, have coordinates in `ℚ + ℒ` and are ℚ-free, and their ℚ-span meets `T` only in `0`:
a combination lying in `T` maps to the same combination of the `qᵢ`, which is then zero.
Roy's Theorem 4 over ℚ at `T`, applied to the `wᵢ`, gives `k·d′ ≤ n′(d′ + k)`, hence `k ≤ n′d′`
since `d′ − n′ ≥ 1`. So the quotient has ℚ-rank at most `n′d′` and is finite-dimensional, and the
same inequality for a ℚ-basis of it, of size `ℓ′`, is the claim `ℓ′d′ ≤ n′(d′ + ℓ′)`. -/

open DiazModulus in
theorem solution {d : ℕ} (U : Submodule ℂ (Fin d → ℂ)) (hUd : Module.finrank ℂ ↥U < d)
    (T : Submodule ℂ (Fin d → ℂ))
    (hTrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T) (hTtop : T ≠ ⊤)
    (hmin : ∀ T' : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T' ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T' → T' ≠ ⊤ →
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * (d - Module.finrank ℂ ↥T') ≤
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T')) * (d - Module.finrank ℂ ↥T)) :
    let W : Submodule ℚ (Fin d → ℂ) := U.restrictScalars ℚ ⊓
      Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg))
    FiniteDimensional ℚ (↥W ⧸ (T.restrictScalars ℚ).comap W.subtype) ∧
    Module.finrank ℚ (↥W ⧸ (T.restrictScalars ℚ).comap W.subtype) * (d - Module.finrank ℂ ↥T) ≤
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) *
        ((d - Module.finrank ℂ ↥T) + Module.finrank ℚ (↥W ⧸ (T.restrictScalars ℚ).comap W.subtype)) ∧
    (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * d ≤
      Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥T) := by
  intro W
  set N := (T.restrictScalars ℚ).comap W.subtype with hN
  set Q := ↥W ⧸ N
  -- a free family in the quotient lifts to a free family in `W` whose span meets `T` in `0`
  have lift : ∀ (k : ℕ) (q : Fin k → Q), LinearIndependent ℚ q →
      ∃ z : Fin k → Fin d → ℂ, (∀ i, z i ∈ U) ∧
        (∀ i j, z i j ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg)) ∧ LinearIndependent ℚ z ∧
        Module.finrank ℚ ↥(Submodule.span ℚ (Set.range z) ⊓ T.restrictScalars ℚ) = 0 := by
    intro k q hq
    choose w hw using fun i => Submodule.Quotient.mk_surjective N (q i)
    have hwq : N.mkQ ∘ w = q := funext fun i => hw i
    have hwind : LinearIndependent ℚ w := LinearIndependent.of_comp N.mkQ (hwq ▸ hq)
    refine ⟨fun i => ((w i : ↥W) : Fin d → ℂ), fun i => (w i).2.1,
      fun i j => (w i).2.2 j (Set.mem_univ j), hwind.map' W.subtype (Submodule.ker_subtype W), ?_⟩
    have hbot : Submodule.span ℚ (Set.range fun i => ((w i : ↥W) : Fin d → ℂ)) ⊓
        T.restrictScalars ℚ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxs, hxT⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun ℚ |>.mp hxs
      have hmem : (∑ i, c i • w i) ∈ N := by
        show W.subtype (∑ i, c i • w i) ∈ T.restrictScalars ℚ
        simpa [map_sum, map_smul] using hxT
      have h0 : ∑ i, c i • q i = 0 := by
        have h1 : N.mkQ (∑ i, c i • w i) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hmem
        rw [map_sum] at h1
        simp only [map_smul] at h1
        rw [← hwq]
        exact h1
      have hc := Fintype.linearIndependent_iff.mp hq c h0
      simp [hc]
    rw [hbot, finrank_bot]
  -- Roy's Theorem 4 on every lift
  have key : ∀ (k : ℕ) (q : Fin k → Q), LinearIndependent ℚ q →
      k * (d - Module.finrank ℂ ↥T) ≤
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * ((d - Module.finrank ℂ ↥T) + k) := by
    intro k q hq
    obtain ⟨z, hzU, hz, hzind, h0⟩ := lift k q hq
    have h := (DiazModulus.roy_rat_theorem_four U z hzU hz hzind T hTrat hTtop hmin).1
    rwa [h0, Nat.sub_zero] at h
  -- the last claim: minimality at `⊥`
  have hB : (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * d ≤
      Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥T) := by
    have hbot : (⊥ : Submodule ℂ (Fin d → ℂ)) ≠ ⊤ := by
      intro h
      have := congrArg (fun T : Submodule ℂ (Fin d → ℂ) => Module.finrank ℂ ↥T) h
      simp only [finrank_bot, finrank_top, Module.finrank_fin_fun] at this
      omega
    have hrat : Submodule.span ℂ {v : Fin d → ℂ | v ∈ (⊥ : Submodule ℂ (Fin d → ℂ)) ∧
        ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = ⊥ := by
      rw [Submodule.span_eq_bot]
      exact fun v hv => (Submodule.mem_bot ℂ).mp hv.1
    have := hmin ⊥ hrat hbot
    rwa [inf_bot_eq, finrank_bot, Nat.sub_zero, Nat.sub_zero] at this
  -- `d′ > 0`
  have hd' : 0 < d - Module.finrank ℂ ↥T := by
    have hle : Module.finrank ℂ ↥T ≤ d :=
      (Submodule.finrank_le T).trans_eq (Module.finrank_fin_fun ℂ)
    by_contra h
    exact hTtop (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega))
  -- finiteness of the quotient
  have hfin : FiniteDimensional ℚ Q := by
    have hbound : ∀ (k : ℕ) (q : Fin k → Q), LinearIndependent ℚ q →
        k ≤ (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * (d - Module.finrank ℂ ↥T) := by
      intro k q hq
      have h := key k q hq
      set n' := Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)
      set D := d - Module.finrank ℂ ↥T
      have h1 : n' < D := by
        by_contra hc
        have hc' : D ≤ n' := not_lt.mp hc
        nlinarith [Nat.mul_le_mul_right d hc', Nat.mul_lt_mul_of_pos_left hUd hd']
      nlinarith
    have hrank : Module.rank ℚ Q ≤
        (((Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * (d - Module.finrank ℂ ↥T) : ℕ) : Cardinal) := by
      apply rank_le
      intro s hs
      exact hbound s.card (fun k => ((s.equivFin.symm k : ↥s) : Q)) (hs.comp _ s.equivFin.symm.injective)
    have : Module.Free ℚ Q := Module.Free.of_divisionRing _ _
    exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  refine ⟨hfin, ?_, hB⟩
  exact key _ (Module.finBasis ℚ Q) (Module.finBasis ℚ Q).linearIndependent
