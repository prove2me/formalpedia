-- Prove2me | solution 1 for DiazModulus.roy_theorem_five
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:45:07.031206+00:00
-- url     : https://prove2.me/submissions/6f429a5b-56ad-4833-a169-7e70331c856f

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_theorem_four_exists
import Theorems.Thm_DiazModulus_roy_hull_transport

open Complex ComplexConjugate Module

/-! # Roy's Theorem 5, decomposition form

Let `U ≤ ℂ^d` contain no nonzero algebraic vector and have rational hull `ℂ^d`, and let `z` be `ℓ` vectors of `U`,
`Q̄`-free, with coordinates in `ℒ̃`. Then `0 < dim U < d` (if `U = 0` the zero subspace would be a rational hull;
if `U = ℂ^d` it would contain a unit vector), and we find a decomposition `D` of `(dim U, d)` into pairs
`0 < nᵢ < dᵢ` with `ℓ ≤ Σ nᵢdᵢ/(dᵢ − nᵢ)`, by strong induction on `d`. For `d = 0`, `ℓ = 0` and `D` is empty.
For `d ≥ 1` choose a rational `S ≠ ℂ^d` minimising `(n − n_S)/(d − d_S)`; Roy's Theorem 4 gives
`ℓ'd' ≤ n'(d' + ℓ')` and `n'd ≤ nd'` with `n' = n − n_S`, `d' = d − d_S`, `ℓ' = ℓ − dim(Z ∩ S)`. Since the hull is
`ℂ^d`, `U ⊄ S`, so `n' ≥ 1`; from `n < d` and `n'd ≤ nd'`, `n' < d'`; hence `ℓ' ≤ n'd'/(d' − n')`. Minimality of
the ratio shows that every rational subspace containing `U ∩ S` has dimension at least `d_S`, so the
configuration `(U ∩ S, a Q̄-basis of Z ∩ S)` transports to `ℂ^{d_S}` with full hull; the induction hypothesis
gives a decomposition of `(n_S, d_S)` bounding `dim(Z ∩ S)`, and we prepend `(n', d')`. -/

namespace RC2_T5
open DiazModulus

/-- The dimension bounds `0 < dim U < d`. -/
theorem dims_pos_lt {d : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (hUQ : ∀ v ∈ U, (∀ i, v i ∈ Qbar) → v = 0)
    (hhull : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ≤ T → T = ⊤) :
    0 < d → 0 < Module.finrank ℂ ↥U ∧ Module.finrank ℂ ↥U < d := by
  intro hd
  constructor
  · by_contra h0
    push Not at h0
    have hU0 : U = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hbot : Submodule.span ℂ {v : Fin d → ℂ | v ∈ (⊥ : Submodule ℂ (Fin d → ℂ)) ∧ ∀ i, v i ∈ Qbar} = ⊥ :=
      le_antisymm (Submodule.span_le.mpr fun v hv => hv.1) bot_le
    have htop := hhull ⊥ hbot (by rw [hU0])
    have := congrArg (fun T : Submodule ℂ (Fin d → ℂ) => Module.finrank ℂ ↥T) htop
    simp at this
    omega
  · by_contra hn
    push Not at hn
    have hUtop : U = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_le U
      simp only [Module.finrank_fin_fun] at this ⊢
      omega
    have h := hUQ (Pi.single ⟨0, hd⟩ 1) (by rw [hUtop]; trivial) (by
      intro i
      by_cases h : i = ⟨0, hd⟩
      · subst h; simp [Qbar.one_mem]
      · simp [h, Qbar.zero_mem])
    have := congrFun h ⟨0, hd⟩
    simp at this

/-- The decomposition clause, by strong induction on `d`. -/
theorem decomp_main :
    ∀ (d : ℕ) {ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ)),
    (∀ v ∈ U, (∀ i, v i ∈ Qbar) → v = 0) →
    (∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ≤ T → T = ⊤) →
    ∀ (z : Fin ℓ → Fin d → ℂ), (∀ i, z i ∈ U) → (∀ i j, z i j ∈ LogAlgTilde) →
    LinearIndependent (↥Qbar) z →
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥U ∧ (D.map Prod.snd).sum = d ∧
      (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro ℓ U hUQ hhull z hzU hz hzind
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0
    have hℓ : ℓ = 0 := by
      by_contra hℓ
      exact hzind.ne_zero ⟨0, by omega⟩ (Subsingleton.elim _ _)
    have hU : Module.finrank ℂ ↥U = 0 := by
      have := Submodule.finrank_le U
      simpa using this
    subst hℓ
    exact ⟨[], by simp, by simp [hU], by simp, by simp⟩
  · -- d ≥ 1
    obtain ⟨S, hSrat, hStop, hmin, hA, hB⟩ := DiazModulus.roy_theorem_four_exists hd U z hzU hz hzind
    have hP := dims_pos_lt U hUQ hhull hd
    -- names
    generalize hW : Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar) = W at hA
    have hnS : Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥U := Submodule.finrank_mono inf_le_left
    have hdSlt : Module.finrank ℂ ↥S < d := by
      have := Submodule.finrank_lt hStop
      simpa using this
    have : FiniteDimensional (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z)) :=
      FiniteDimensional.span_of_finite _ (Set.finite_range z)
    have hWle : W ≤ Submodule.span (↥Qbar) (Set.range z) := hW ▸ inf_le_left
    have : FiniteDimensional (↥Qbar) ↥W := Submodule.finiteDimensional_of_le hWle
    have hℓS : Module.finrank (↥Qbar) ↥W ≤ ℓ := by
      have := Submodule.finrank_mono hWle
      rw [finrank_span_eq_card hzind] at this
      simpa using this
    -- step 3
    have h3 : 1 ≤ Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S) := by
      by_contra h
      push Not at h
      have heq : Module.finrank ℂ ↥(U ⊓ S) = Module.finrank ℂ ↥U := by omega
      have hUS : U ⊓ S = U := Submodule.eq_of_le_of_finrank_eq inf_le_left heq
      exact hStop (hhull S hSrat (by rw [← hUS]; exact inf_le_right))
    -- step 4
    have h4 : Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S) < d - Module.finrank ℂ ↥S := by
      by_contra h
      push Not at h
      have hd' : 1 ≤ d - Module.finrank ℂ ↥S := by omega
      have e1 : (d - Module.finrank ℂ ↥S) * d ≤
          (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * d := Nat.mul_le_mul_right d h
      have e2 : Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥S) < d * (d - Module.finrank ℂ ↥S) :=
        Nat.mul_lt_mul_of_pos_right hP.2 hd'
      nlinarith
    -- step 6
    have h6 : ∀ T : Submodule ℂ (Fin d → ℂ),
        Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ⊓ S ≤ T →
          Module.finrank ℂ ↥S ≤ Module.finrank ℂ ↥T := by
      intro T hT hST
      by_cases hTtop : T = ⊤
      · subst hTtop
        simp only [finrank_top, Module.finrank_fin_fun]
        omega
      · have hm := hmin T hT hTtop
        have hnT : Module.finrank ℂ ↥(U ⊓ S) ≤ Module.finrank ℂ ↥(U ⊓ T) :=
          Submodule.finrank_mono (le_inf inf_le_left hST)
        have hnTn : Module.finrank ℂ ↥(U ⊓ T) ≤ Module.finrank ℂ ↥U := Submodule.finrank_mono inf_le_left
        have hdT : Module.finrank ℂ ↥T ≤ d := by
          have := Submodule.finrank_le T; simpa using this
        have hdS : Module.finrank ℂ ↥S ≤ d := hdSlt.le
        have k1 : (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ T)) * (d - Module.finrank ℂ ↥S) ≤
            (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * (d - Module.finrank ℂ ↥S) :=
          Nat.mul_le_mul_right _ (by omega)
        have k2 := le_trans hm k1
        have k3 : d - Module.finrank ℂ ↥T ≤ d - Module.finrank ℂ ↥S :=
          Nat.le_of_mul_le_mul_left k2 (by omega)
        omega
    -- step 7: a Q̄-basis of Z ∩ S
    let b := Module.finBasis (↥Qbar) ↥W
    let z' : Fin (Module.finrank (↥Qbar) ↥W) → Fin d → ℂ := fun k => ((b k : ↥W) : Fin d → ℂ)
    have hz'ind : LinearIndependent (↥Qbar) z' :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hspanU : Submodule.span (↥Qbar) (Set.range z) ≤ U.restrictScalars (↥Qbar) := by
      rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hzU i
    have hspanL : Submodule.span (↥Qbar) (Set.range z) ≤
        Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde) := by
      rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; intro j _; exact hz i j
    have hz'mem : ∀ k, z' k ∈ W := fun k => (b k).2
    have hz'U : ∀ k, z' k ∈ U ⊓ S := by
      intro k
      have hk := hz'mem k
      rw [← hW] at hk
      exact ⟨hspanU hk.1, hk.2⟩
    have hz' : ∀ k j, z' k j ∈ LogAlgTilde := by
      intro k j
      have hk := hz'mem k
      rw [← hW] at hk
      exact hspanL hk.1 j (Set.mem_univ _)
    obtain ⟨U', zs, hU'dim, hU'Q, hU'hull, hzsU, hzs, hzsind⟩ :=
      DiazModulus.roy_hull_transport S (U ⊓ S) hSrat rfl inf_le_right (fun v hv => hUQ v hv.1) h6 z' hz'U hz' hz'ind
    obtain ⟨D', hD'parts, hD'n, hD'd, hD'ℓ⟩ := ih _ hdSlt U' hU'Q hU'hull zs hzsU hzs hzsind
    refine ⟨(Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S), d - Module.finrank ℂ ↥S) :: D', ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by omega, h4⟩
      · exact hD'parts p hp
    · simp only [List.map_cons, List.sum_cons, hD'n, hU'dim]
      omega
    · simp only [List.map_cons, List.sum_cons, hD'd]
      omega
    · simp only [List.map_cons, List.sum_cons]
      -- step 5 in ℚ
      set a := Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S) with ha
      set e := d - Module.finrank ℂ ↥S with he
      set m := ℓ - Module.finrank (↥Qbar) ↥W with hm
      have hpos : (0 : ℚ) < (e : ℚ) - a := by
        have : (a : ℚ) < e := by exact_mod_cast h4
        linarith
      have h5 : (m : ℚ) ≤ (a : ℚ) * e / ((e : ℚ) - a) := by
        rw [le_div_iff₀ hpos]
        have : ((m * e : ℕ) : ℚ) ≤ ((a * (e + m) : ℕ) : ℚ) := by exact_mod_cast hA
        push_cast at this
        nlinarith
      have hsplit : (ℓ : ℚ) = (m : ℚ) + (Module.finrank (↥Qbar) ↥W : ℚ) := by
        rw [hm, Nat.cast_sub hℓS]; ring
      rw [hsplit]
      exact add_le_add h5 hD'ℓ

end RC2_T5

open DiazModulus RC2_T5 in
theorem solution {d ℓ : ℕ} (U : Submodule ℂ (Fin d → ℂ))
    (hUQ : ∀ v ∈ U, (∀ i, v i ∈ Qbar) → v = 0)
    (hhull : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ≤ T → T = ⊤)
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    (0 < d → 0 < Module.finrank ℂ ↥U ∧ Module.finrank ℂ ↥U < d) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
      (D.map Prod.fst).sum = Module.finrank ℂ ↥U ∧ (D.map Prod.snd).sum = d ∧
      (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  exact ⟨dims_pos_lt U hUQ hhull, decomp_main d U hUQ hhull z hzU hz hzind⟩
