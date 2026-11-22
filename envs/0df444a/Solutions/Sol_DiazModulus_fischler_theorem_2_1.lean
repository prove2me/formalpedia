-- Prove2me | solution 1 for DiazModulus.fischler_theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T09:01:59.266453+00:00
-- url     : https://prove2.me/submissions/275662eb-648d-4b3e-9a21-3ba466c710d8

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_theorem_four
import Theorems.Thm_DiazModulus_roy_theorem_four_exists
import Theorems.Thm_DiazModulus_multiplicityEstimateElem
import Theorems.Thm_DiazModulus_rational_preimage_finrank
import Theorems.Thm_DiazModulus_rational_proper_annihilator

open Complex ComplexConjugate

/-! # Fischler's Theorem 2.1 (Roy's Theorem 4 in Fischler's form)

Let `z₁, …, z_l` be the columns of `M` and `U` its column space, of dimension `r = rk M`. The columns have entries
in `ℒ̃` and are `Q̄`-free (no algebraic vector is killed by `M`), and `(d + l) r < d l` forces `d, l ≥ 1`. Roy's
Theorem 4 gives a rational `T ≠ ℂᵈ` minimising `(r − dim(U ∩ T))/(d − dim T)`, with
`ℓ_T d_T ≤ r_T (d_T + ℓ_T)` and `r_T d ≤ r d_T`. The second inequality is strict: in case of equality the zero
subspace is a minimiser too, and Roy's theorem at `0` gives `l d ≤ r (d + l)`, against the hypothesis. Put
`r₁ = r_T`. The rational subspace `S` spanned by algebraic preimages of `span_Q̄(z) ∩ T` satisfies `M S ⊆ T` and
`dim S = dim_Q̄ (span_Q̄(z) ∩ T)`, so `l − dim S = ℓ_T` and the first inequality is Fischler's
`r₁ ≥ l₁d₁/(l₁ + d₁)`. Finally `U ⊆ T` is impossible: a non-zero algebraic form vanishing on `T` would kill
every column of `M`, against the hypothesis on the rows. This gives `r₁ ≥ 1` and, as `S = ℂˡ` would give
`U ⊆ T`, also `l₁ ≥ 1`; `d₁ ≥ 1` as `T ≠ ℂᵈ`. -/

namespace RC10_G1

/-- The cancellation behind the strict inequality: if `a D = r e` with `e > 0` and `a f ≤ g e`,
then `r f ≤ g D`. -/
theorem cancel_aux {a D e f g r : ℕ} (he : 0 < e) (heq : a * D = r * e) (h : a * f ≤ g * e) :
    r * f ≤ g * D := by
  refine Nat.le_of_mul_le_mul_left ?_ he
  calc e * (r * f) = (a * D) * f := by rw [heq]; ring
    _ = D * (a * f) := by ring
    _ ≤ D * (g * e) := Nat.mul_le_mul_left _ h
    _ = e * (g * D) := by ring

end RC10_G1

open DiazModulus RC10_G1 in
theorem solution {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hker : ∀ b : Fin l → ℂ, (∀ j, b j ∈ Qbar) → M.mulVec b = 0 → b = 0)
    (him : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → Matrix.vecMul φ M = 0 → φ = 0)
    (hr : (d + l) * M.rank < d * l) :
    ∃ (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ)) (r₁ : ℕ),
      Submodule.span ℂ {v : Fin l → ℂ | v ∈ S ∧ ∀ j, v j ∈ Qbar} = S ∧
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T ∧
      1 ≤ l - Module.finrank ℂ ↥S ∧ 1 ≤ d - Module.finrank ℂ ↥T ∧
      (∀ s ∈ S, M.mulVec s ∈ T) ∧ 1 ≤ r₁ ∧
      r₁ * d < M.rank * (d - Module.finrank ℂ ↥T) ∧
      (l - Module.finrank ℂ ↥S) * (d - Module.finrank ℂ ↥T) ≤
        r₁ * ((l - Module.finrank ℂ ↥S) + (d - Module.finrank ℂ ↥T)) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
  set U : Submodule ℂ (Fin d → ℂ) := LinearMap.range M.mulVecLin with hU
  have hrank : M.rank = Module.finrank ℂ U := rfl
  rw [hrank] at hr ⊢
  -- the columns lie in `U`, have entries in `ℒ̃`, and are `Q̄`-free
  have hzU : ∀ j, (fun i => M i j) ∈ U := fun j => ⟨Pi.single j 1, by ext i; simp⟩
  have hzind : LinearIndependent (↥Qbar) (fun j i => M i j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 := hker (fun j => (g j : ℂ)) (fun j => (g j).2) (by
      rw [← hg]
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Subfield.smul_def, mul_comm])
    exact Subtype.ext (by simpa using congr_fun h0 j)
  -- Roy's minimiser `T` and the rational preimage `S`
  obtain ⟨T, hTrat, hTtop, hmin, hA, hB⟩ :=
    DiazModulus.roy_theorem_four_exists hd U (fun j i => M i j) hzU (fun j i => hM i j) hzind
  obtain ⟨S, hSrat, hST, hSfin⟩ := DiazModulus.rational_preimage_finrank M hker T
  -- `U ⊆ T` is impossible
  have hUT : ¬ U ≤ T := by
    intro hle
    obtain ⟨φ, hφQ, hφ0, hφT⟩ := DiazModulus.rational_proper_annihilator T hTrat hTtop
    apply hφ0
    apply him φ hφQ
    funext j
    exact hφT _ (hle (hzU j))
  have hrT : Module.finrank ℂ ↥(U ⊓ T) < Module.finrank ℂ U := by
    refine lt_of_le_of_ne (Submodule.finrank_mono inf_le_left) fun h => hUT ?_
    exact inf_eq_left.1 (Submodule.eq_of_le_of_finrank_eq inf_le_left h)
  have hTd : Module.finrank ℂ T < d := by
    simpa using Submodule.finrank_lt hTtop
  have hSl : Module.finrank ℂ S < l := by
    refine lt_of_le_of_ne (by simpa using Submodule.finrank_le S) fun h => hUT ?_
    have hS : S = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h)
    rintro _ ⟨v, rfl⟩
    exact hST v (hS ▸ Submodule.mem_top)
  -- the inequality `r_T d ≤ r d_T` is strict, by Roy's theorem at the zero subspace
  have hstrict : (Module.finrank ℂ U - Module.finrank ℂ ↥(U ⊓ T)) * d <
      Module.finrank ℂ U * (d - Module.finrank ℂ T) := by
    refine lt_of_le_of_ne hB fun heq => ?_
    have hbot : Submodule.span ℂ
        {v : Fin d → ℂ | v ∈ (⊥ : Submodule ℂ (Fin d → ℂ)) ∧ ∀ i, v i ∈ Qbar} = ⊥ :=
      Submodule.span_eq_bot.2 fun v hv => (Submodule.mem_bot ℂ).1 hv.1
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hmin0 : ∀ S' : Submodule ℂ (Fin d → ℂ),
        Submodule.span ℂ {v : Fin d → ℂ | v ∈ S' ∧ ∀ i, v i ∈ Qbar} = S' → S' ≠ ⊤ →
        (Module.finrank ℂ U - Module.finrank ℂ ↥(U ⊓ ⊥)) * (d - Module.finrank ℂ S') ≤
          (Module.finrank ℂ U - Module.finrank ℂ ↥(U ⊓ S')) *
            (d - Module.finrank ℂ ↥(⊥ : Submodule ℂ (Fin d → ℂ))) := by
      intro S' hS'rat hS'top
      rw [inf_bot_eq, finrank_bot, tsub_zero, tsub_zero]
      exact cancel_aux (Nat.sub_pos_of_lt hTd) heq (hmin S' hS'rat hS'top)
    have h0 := (DiazModulus.roy_theorem_four DiazModulus.multiplicityEstimateElem U (fun j i => M i j)
      hzU (fun j i => hM i j) hzind ⊥ hbot bot_ne_top hmin0).1
    rw [Submodule.restrictScalars_bot, inf_bot_eq, inf_bot_eq, finrank_bot, finrank_bot] at h0
    simp only [tsub_zero] at h0
    nlinarith
  refine ⟨S, T, Module.finrank ℂ U - Module.finrank ℂ ↥(U ⊓ T), hSrat, hTrat, by omega, by omega, hST,
    by omega, hstrict, ?_⟩
  rw [hSfin, Nat.add_comm (l - _)]
  exact hA
