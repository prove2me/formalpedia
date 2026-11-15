-- Prove2me | solution 1 for DiazModulus.roy_theorem_five_dmin
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:42:59.261396+00:00
-- url     : https://prove2.me/submissions/7692f10e-fb6c-4660-b827-4c6409a3a889

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_hull_transport
import Theorems.Thm_DiazModulus_roy_theorem_five

open Complex ComplexConjugate Module

/-! # Roy's Theorem 5 for a space of minimal rational hull dimension

Let `V ≤ ℂ^d` contain no nonzero algebraic vector, and let `S₀ ⊇ V` be rational of least dimension among the
rational subspaces containing `V`. Write `W = V ∩ ℒ̃^d`, a `Q̄`-subspace. First, for any `Q̄`-free family `z` of
`ℓ` vectors of `W`, transporting `(V, z)` to the coordinates of `S₀` gives a configuration in `ℂ^{dim S₀}` with
full rational hull and the same dimension, and Roy's Theorem 5 there gives a decomposition `D` of
`(dim V, dim S₀)` with `ℓ ≤ Σ nᵢdᵢ/(dᵢ − nᵢ)`. Each term is at most `nᵢ · dim S₀`, since `dᵢ ≤ dim S₀` and
`dᵢ − nᵢ ≥ 1`, so every finite free family in `W` has at most `dim V · dim S₀` elements. Hence `W` has finite
rank, so it is finite-dimensional over `Q̄`. Applying the family form to a `Q̄`-basis of `W` gives the
decomposition bounding `dim_Q̄ W`. -/

namespace RC2_T5D
open DiazModulus

/-- Each term `nᵢdᵢ/(dᵢ − nᵢ)` is at most `nᵢ s` when `dᵢ ≤ s`. -/
theorem value_le (s : ℕ) : ∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ s) →
    (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum ≤
      (((D.map Prod.fst).sum : ℕ) : ℚ) * s
  | [], _ => by simp
  | p :: D, h => by
    have hp := h p (List.mem_cons_self ..)
    have ih := value_le s D (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons]
    push_cast
    have hpos : (1 : ℚ) ≤ (p.2 : ℚ) - p.1 := by
      have : (p.1 : ℚ) + 1 ≤ p.2 := by exact_mod_cast hp.2.1
      linarith
    have hpart : (p.1 : ℚ) * p.2 / ((p.2 : ℚ) - p.1) ≤ p.1 * s := by
      rw [div_le_iff₀ (by linarith)]
      have hb' : (p.2 : ℚ) ≤ s := by exact_mod_cast hp.2.2
      have ha : (0 : ℚ) ≤ p.1 := by positivity
      have h1 : (p.1 : ℚ) * p.2 ≤ p.1 * s := mul_le_mul_of_nonneg_left hb' ha
      have h2 : (p.1 : ℚ) * s * 1 ≤ p.1 * s * ((p.2 : ℚ) - p.1) :=
        mul_le_mul_of_nonneg_left hpos (by positivity)
      linarith
    push_cast at ih
    linarith


end RC2_T5D

open DiazModulus RC2_T5D in
theorem solution {d : ℕ} (V S₀ : Submodule ℂ (Fin d → ℂ))
    (hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0)
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, v i ∈ Qbar} = S₀) (hVS₀ : V ≤ S₀)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → V ≤ T →
        Module.finrank ℂ ↥S₀ ≤ Module.finrank ℂ ↥T) :
    FiniteDimensional (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥V ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S₀ ∧
      (Module.finrank (↥Qbar)
          ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) : ℚ) ≤
        (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  set W := V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde) with hWdef
  -- (a) family form
  have fam : ∀ {ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ), (∀ i, z i ∈ W) → LinearIndependent (↥Qbar) z →
      ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
        (D.map Prod.fst).sum = Module.finrank ℂ ↥V ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S₀ ∧
        (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
    intro ℓ z hzW hzind
    obtain ⟨U', z', hdim, hQ, hhull, hzU, hz, hind⟩ :=
      DiazModulus.roy_hull_transport S₀ V hS₀ rfl hVS₀ hVQ hmin z (fun i => (hzW i).1) (fun i j => (hzW i).2 j (Set.mem_univ _)) hzind
    obtain ⟨-, D, hp, hn, hd, hl⟩ := DiazModulus.roy_theorem_five U' hQ hhull z' hzU hz hind
    exact ⟨D, hp, hn.trans hdim, hd, hl⟩
  -- (b) uniform bound, (c) finiteness
  have hrank : Module.rank (↥Qbar) ↥W ≤ ((Module.finrank ℂ ↥V * Module.finrank ℂ ↥S₀ : ℕ) : Cardinal) := by
    apply rank_le
    intro s hs
    let z : Fin s.card → Fin d → ℂ := fun k => (((s.equivFin.symm k : ↥s) : ↥W) : Fin d → ℂ)
    have hzind : LinearIndependent (↥Qbar) z :=
      (hs.comp _ s.equivFin.symm.injective).map' W.subtype (Submodule.ker_subtype W)
    obtain ⟨D, hp, hn, hd, hl⟩ := fam z (fun k => ((s.equivFin.symm k : ↥s) : ↥W).2) hzind
    have hb := value_le (Module.finrank ℂ ↥S₀) D (fun p hpD => ⟨(hp p hpD).1, (hp p hpD).2,
      hd ▸ List.le_sum_of_mem (List.mem_map_of_mem hpD)⟩)
    rw [hn] at hb
    have : ((s.card : ℕ) : ℚ) ≤ ((Module.finrank ℂ ↥V * Module.finrank ℂ ↥S₀ : ℕ) : ℚ) := by
      push_cast; exact le_trans (by simpa using hl) hb
    exact_mod_cast this
  have hfree : Module.Free (↥Qbar) ↥W := Module.Free.of_divisionRing _ _
  have hfin : FiniteDimensional (↥Qbar) ↥W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  refine ⟨hfin, ?_⟩
  -- (d) a basis
  let b := Module.finBasis (↥Qbar) ↥W
  exact fam (fun k => ((b k : ↥W) : Fin d → ℂ)) (fun k => (b k).2)
    (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
