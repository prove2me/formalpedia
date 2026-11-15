-- Prove2me | solution 1 for DiazModulus.dalag_cor_11_15_rat
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T17:31:23.670202+00:00
-- url     : https://prove2.me/submissions/a348bb39-677d-4248-a9e7-0ff8ebbbfb39

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rat_theorem_five
import Theorems.Thm_DiazModulus_dalag_psi_floor_roy_phi

open Complex ComplexConjugate

/-! # DALAG Cor. 11.15 for (ℚ, ℚ + ℒ) in the printed Ψ form

Let `V ≤ ℂ^d` contain no nonzero rational vector, `n = dim V`, and let `S₀ ⊇ V` be rational of least dimension
`s₀` among the rational subspaces containing `V`. (i) `n ≤ s₀`, and `n = s₀ > 0` would make `V = S₀` a nonzero
rational subspace, which contains a nonzero rational vector. (ii) For every `ℚ`-free family of `ℓ` vectors of
`W = V ∩ (ℚ + ℒ)^d`, Roy's Theorem 5 over `ℚ` gives a rational `S ⊇ V` and a decomposition `D` of
`(n, dim S)` with `ℓ ≤ Σ nᵢdᵢ/(dᵢ − nᵢ)`; each term is at most `nᵢ·d` (`dᵢ ≤ d`, `dᵢ − nᵢ ≥ 1`), so `ℓ ≤ nd`,
and `W` has finite rank, hence is finite-dimensional. (iii) Apply this to a `ℚ`-basis of `W`. If `n = 0`, `D`
is empty and `dim W = 0`. If `n > 0`, `D` is non-empty, so `n < dim S`, and `s₀ ≤ dim S` by minimality. The
integer part of Roy's maximum at `(n, dim S)` is `Ψ(n, dim S)`, so `dim W ≤ Ψ(n, dim S)`; finally `Ψ(n, ·)` is
non-increasing on `(n, ∞)` (values `n(n+1)`, `n(n−1)+2`, `n(n−1)+1` for `n ≥ 2`, and `2`, `1` for `n = 1`),
and `n < s₀ ≤ dim S` gives `Ψ(n, dim S) ≤ Ψ(n, s₀)`. -/

namespace RC5_C1115Q
open DiazModulus

/-- A non-empty decomposition has `Σ fst < Σ snd`. -/
theorem sums_lt (D : List (ℕ × ℕ)) (hD : ∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) (hne : D ≠ []) :
    (D.map Prod.fst).sum < (D.map Prod.snd).sum := by
  induction D with
  | nil => exact absurd rfl hne
  | cons p D ih =>
    have hp := hD p List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    by_cases hD' : D = []
    · subst hD'; simp only [List.map_nil, List.sum_nil, add_zero]; exact hp.2
    · have := ih (fun q hq => hD q (List.mem_cons_of_mem _ hq)) hD'; omega

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

/-- DALAG's table `Ψ(n, ·)` is non-increasing on `(n, ∞)`. -/
theorem psi_anti (Ψ : ℕ → ℕ → ℕ) (hΨ : ∀ a b, Ψ a b =
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0)
    {n s₀ s : ℕ} (hn : 0 < n) (h1 : n < s₀) (h2 : s₀ ≤ s) : Ψ n s ≤ Ψ n s₀ := by
  have e : n * (n + 1) = n * (n - 1) + 2 * n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [hΨ, hΨ]
  split_ifs <;> omega

end RC5_C1115Q

open DiazModulus RC5_C1115Q in
theorem solution {d : ℕ} (V S₀ : Submodule ℂ (Fin d → ℂ))
    (hVQ : ∀ v ∈ V, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0)
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S₀)
    (hVS₀ : V ≤ S₀)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T → V ≤ T →
        Module.finrank ℂ ↥S₀ ≤ Module.finrank ℂ ↥T) :
    let Ψ : ℕ → ℕ → ℕ := fun a b =>
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0
    (0 < Module.finrank ℂ ↥V → Module.finrank ℂ ↥V < Module.finrank ℂ ↥S₀) ∧
    FiniteDimensional ℚ ↥(V.restrictScalars ℚ ⊓
        Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg))) ∧
    Module.finrank ℚ ↥(V.restrictScalars ℚ ⊓
        Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg))) ≤
      Ψ (Module.finrank ℂ ↥V) (Module.finrank ℂ ↥S₀) := by
  intro Ψ
  set W := V.restrictScalars ℚ ⊓
    Submodule.pi Set.univ (fun _ : Fin d => Submodule.span ℚ (insert (1 : ℂ) LogAlg)) with hWdef
  -- (i) `0 < n → n < s₀`
  have hi : 0 < Module.finrank ℂ ↥V → Module.finrank ℂ ↥V < Module.finrank ℂ ↥S₀ := by
    intro hpos
    refine lt_of_le_of_ne (Submodule.finrank_mono hVS₀) (fun heq => ?_)
    have hVeq : V = S₀ := Submodule.eq_of_le_of_finrank_eq hVS₀ heq
    have hne : V ≠ ⊥ := fun h => by rw [h, finrank_bot] at hpos; exact lt_irrefl _ hpos
    by_cases hc : ∀ v ∈ S₀, (∀ i, ∃ q : ℚ, v i = (q : ℂ)) → v = 0
    · exact hne (by rw [hVeq, ← hS₀]; exact Submodule.span_eq_bot.mpr (fun v hv => hc v hv.1 hv.2))
    · push Not at hc
      obtain ⟨v, hvS, hvQ, hv0⟩ := hc
      exact hv0 (hVQ v (by rw [hVeq]; exact hvS) hvQ)
  -- the family form of Roy's Theorem 5 inside `W`
  have fam : ∀ {ℓ : ℕ} (z : Fin ℓ → Fin d → ℂ), (∀ i, z i ∈ W) → LinearIndependent ℚ z →
      ∃ (S : Submodule ℂ (Fin d → ℂ)) (D : List (ℕ × ℕ)),
        Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S ∧ V ≤ S ∧
        (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
        (D.map Prod.fst).sum = Module.finrank ℂ ↥V ∧ (D.map Prod.snd).sum = Module.finrank ℂ ↥S ∧
        (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum :=
    fun z hzW hzind => DiazModulus.roy_rat_theorem_five V hVQ z (fun i => (hzW i).1)
      (fun i j => (hzW i).2 j (Set.mem_univ _)) hzind
  -- (ii) every free family has at most `n·d` members, so `W` is finite-dimensional
  have hrank : Module.rank ℚ ↥W ≤ ((Module.finrank ℂ ↥V * d : ℕ) : Cardinal) := by
    apply rank_le
    intro s hs
    let z : Fin s.card → Fin d → ℂ := fun k => (((s.equivFin.symm k : ↥s) : ↥W) : Fin d → ℂ)
    have hzind : LinearIndependent ℚ z :=
      (hs.comp _ s.equivFin.symm.injective).map' W.subtype (Submodule.ker_subtype W)
    obtain ⟨S, D, -, -, hp, hn, hd, hl⟩ := fam z (fun k => ((s.equivFin.symm k : ↥s) : ↥W).2) hzind
    have hSd : Module.finrank ℂ ↥S ≤ d := (Submodule.finrank_le S).trans_eq (Module.finrank_fin_fun ℂ)
    have hb := value_le d D (fun p hpD => ⟨(hp p hpD).1, (hp p hpD).2,
      le_trans (hd ▸ List.le_sum_of_mem (List.mem_map_of_mem hpD)) hSd⟩)
    rw [hn] at hb
    have : ((s.card : ℕ) : ℚ) ≤ ((Module.finrank ℂ ↥V * d : ℕ) : ℚ) := by
      push_cast; exact le_trans (by simpa using hl) hb
    exact_mod_cast this
  have hfin : FiniteDimensional ℚ ↥W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  refine ⟨hi, hfin, ?_⟩
  -- (iii) a basis of `W`, and the table `Ψ`
  let b := Module.finBasis ℚ ↥W
  obtain ⟨S, D, hSr, hVS, hp, hn, hd, hl⟩ := fam (fun k => ((b k : ↥W) : Fin d → ℂ)) (fun k => (b k).2)
    (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
  by_cases hn0 : Module.finrank ℂ ↥V = 0
  · have hD0 : D = [] := by
      cases D with
      | nil => rfl
      | cons p D' =>
        exfalso
        have := (hp p List.mem_cons_self).1
        simp only [List.map_cons, List.sum_cons] at hn
        omega
    subst hD0
    simp only [List.map_nil, List.sum_nil] at hl
    have : Module.finrank ℚ ↥W = 0 := by exact_mod_cast le_antisymm hl (Nat.cast_nonneg _)
    rw [this]
    exact Nat.zero_le _
  · have hpos : 0 < Module.finrank ℂ ↥V := Nat.pos_of_ne_zero hn0
    have hne : D ≠ [] := by
      rintro rfl
      simp only [List.map_nil, List.sum_nil] at hn
      omega
    have hnS : Module.finrank ℂ ↥V < Module.finrank ℂ ↥S := by
      rw [← hn, ← hd]; exact sums_lt D hp hne
    have hfl := (DiazModulus.dalag_psi_floor_roy_phi hpos hnS).1 D hp hn hd
    have h' : (Module.finrank ℚ ↥W : ℚ) < (Ψ (Module.finrank ℂ ↥V) (Module.finrank ℂ ↥S) : ℚ) + 1 :=
      lt_of_le_of_lt hl hfl
    have h'' : Module.finrank ℚ ↥W < Ψ (Module.finrank ℂ ↥V) (Module.finrank ℂ ↥S) + 1 := by
      exact_mod_cast h'
    have hmono := psi_anti Ψ (fun _ _ => rfl) hpos (hi hpos) (hmin S hSr hVS)
    omega
