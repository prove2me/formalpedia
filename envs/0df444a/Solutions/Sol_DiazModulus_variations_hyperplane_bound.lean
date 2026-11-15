-- Prove2me | solution 1 for DiazModulus.variations_hyperplane_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:40:15.085581+00:00
-- url     : https://prove2.me/submissions/3fdf1823-2155-4155-9fb8-f495b00e456e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_theorem_five_dmin

open Complex ComplexConjugate

/-! # Waldschmidt, *Variations* Th. 3.1: a hyperplane meets `ℒ̃^d` in dimension at most `d(d − 1)`

Let `V ≤ ℂ^d` be a hyperplane (`dim V + 1 = d`) meeting `Q̄^d` only in `0`. If `d = 1`, then `V = 0`; the
decomposition form of Roy's theorem with the minimal rational subspace `S₀ = 0` gives finite dimensionality and a
decomposition of `(0, 0)`, which is empty, so the dimension is `0`. If `d ≥ 2`, the rational hull of `V` is `ℂ^d`:
a rational `T ≠ ℂ^d` containing `V` has dimension `d − 1 = dim V`, so `T = V`, and a rational nonzero `V` would
contain a nonzero algebraic vector. So `S₀ = ℂ^d` is a rational subspace of minimal dimension containing `V`, and
the decomposition form of Roy's theorem (DALAG Cor. 11.15 for `(Q̄, ℒ̃)`) gives `V ∩ ℒ̃^d` finite-dimensional over
`Q̄`, with dimension at most `Σ nᵢdᵢ/(dᵢ − nᵢ)` for a decomposition `(d − 1, d) = Σ (nᵢ, dᵢ)`, `0 < nᵢ < dᵢ`.
Since `Σ (dᵢ − nᵢ) = 1` and every summand is at least `1`, the decomposition has exactly one part, `(d − 1, d)`,
and the bound is `(d − 1)d / 1 = d(d − 1)`. -/

namespace RC2_HB
open DiazModulus

/-- In a decomposition, `Σ snd ≥ Σ fst + length`. -/
theorem decomp_len (D : List (ℕ × ℕ)) (h : ∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) :
    (D.map Prod.fst).sum + D.length ≤ (D.map Prod.snd).sum := by
  induction D with
  | nil => simp
  | cons p D ih =>
    have hp := (h p (List.mem_cons_self ..)).2
    have := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- `ℂ^d` is rational. -/
theorem isRat_top (d : ℕ) :
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ (⊤ : Submodule ℂ (Fin d → ℂ)) ∧ ∀ i, v i ∈ Qbar} = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v
  have hv := (Pi.basisFun ℂ (Fin d)).mem_span v
  refine Submodule.span_mono ?_ hv
  rintro _ ⟨i, rfl⟩
  refine ⟨trivial, fun j => ?_⟩
  rw [Pi.basisFun_apply]
  by_cases h : j = i
  · subst h; simp [Qbar.one_mem]
  · simp [h, Qbar.zero_mem]

end RC2_HB

open DiazModulus RC2_HB Module in
theorem solution {d : ℕ} (V : Submodule ℂ (Fin d → ℂ))
    (hV : Module.finrank ℂ ↥V + 1 = d) (hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0) :
    FiniteDimensional (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ∧
      Module.finrank (↥Qbar)
          ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ≤
        d * (d - 1) := by
  -- every rational `T ≥ V` is `ℂ^d`, unless `d = 1`
  have hrat : ∀ {T : Submodule ℂ (Fin d → ℂ)},
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → V ≤ T → T = ⊤ ∨ d = 1 := by
    intro T hT hVT
    by_contra hc
    push Not at hc
    obtain ⟨hTtop, hd1⟩ := hc
    have hlt : Module.finrank ℂ ↥T < d := by
      have := Submodule.finrank_lt hTtop; simpa using this
    have hle : Module.finrank ℂ ↥V ≤ Module.finrank ℂ ↥T := Submodule.finrank_mono hVT
    have hVT' : V = T := Submodule.eq_of_le_of_finrank_eq hVT (by omega)
    subst hVT'
    have hne : V ≠ ⊥ := by
      intro hb; rw [hb] at hV; simp at hV; omega
    apply hne
    rw [← hT, Submodule.span_eq_bot]
    intro v hv
    exact hVQ v hv.1 hv.2
  rcases (show d = 1 ∨ 2 ≤ d by omega) with hd | hd
  · -- `d = 1`: `V = 0`, minimal rational subspace `⊥`
    subst hd
    have hV0 : V = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hbot : Submodule.span ℂ {v : Fin 1 → ℂ | v ∈ (⊥ : Submodule ℂ (Fin 1 → ℂ)) ∧ ∀ i, v i ∈ Qbar} = ⊥ :=
      le_antisymm (Submodule.span_le.mpr fun v hv => hv.1) bot_le
    obtain ⟨hfin, D, hDp, -, hDd, hDl⟩ :=
      DiazModulus.roy_theorem_five_dmin V ⊥ hVQ hbot (by rw [hV0]) (fun T _ _ => by simp)
    refine ⟨hfin, ?_⟩
    have hD : D = [] := by
      have := decomp_len D hDp
      rw [hDd] at this
      simp at this
      exact this.2
    subst hD
    simp only [List.map_nil, List.sum_nil] at hDl
    have := Nat.cast_nonpos.mp hDl
    omega
  · -- `d ≥ 2`: minimal rational subspace `⊤`
    obtain ⟨hfin, D, hDp, hDn, hDd, hDl⟩ :=
      DiazModulus.roy_theorem_five_dmin V ⊤ hVQ (isRat_top d) le_top (fun T hT hVT => by
        rcases hrat hT hVT with h | h
        · rw [h]
        · omega)
    refine ⟨hfin, ?_⟩
    simp only [finrank_top, Module.finrank_fin_fun] at hDd
    -- the only decomposition of `(d - 1, d)` is `[(d - 1, d)]`
    have hlen := decomp_len D hDp
    rw [hDn, hDd] at hlen
    have hlen1 : D.length ≤ 1 := by omega
    rcases D with _ | ⟨p, _ | ⟨q, D⟩⟩
    · simp at hDn; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hDn hDd hDl
      have hp1 : (p.1 : ℚ) = (d : ℚ) - 1 := by
        have : p.1 + 1 = d := by omega
        have : ((p.1 + 1 : ℕ) : ℚ) = d := by exact_mod_cast this
        push_cast at this; linarith
      have hp2 : (p.2 : ℚ) = d := by exact_mod_cast hDd
      rw [hp1, hp2, show (d : ℚ) - ((d : ℚ) - 1) = 1 by ring, div_one] at hDl
      have : ((d * (d - 1) : ℕ) : ℚ) = (d : ℚ) * ((d : ℚ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      exact_mod_cast (show (Module.finrank (↥Qbar)
          ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) : ℚ) ≤
          ((d * (d - 1) : ℕ) : ℚ) by rw [this]; linarith)
    · simp at hlen1
