-- Prove2me | solution 1 for DetANN.rademacher_moments
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T03:03:34.209133+00:00
-- url     : https://prove2.me/submissions/fc27bb03-651f-4c41-bab5-c0fc5d4c8697

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_SignChoice

open DetANN

namespace DetANNSignAux

/-! ### Coefficient algebra -/

lemma coeff_egf_mul (α : ℕ → ℝ) (G : PowerSeries ℝ) (m : ℕ) :
    (m.factorial : ℝ) * PowerSeries.coeff m (egf α * G) =
      ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * α k * (((m - k).factorial : ℝ) * PowerSeries.coeff (m - k) G) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [egf, PowerSeries.coeff_mk]
  have hc : (m.choose k : ℝ) * k.factorial * (m - k).factorial = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  rw [← hc]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((m - k).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### Averages -/

lemma avgOver_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    avgOver f = avgOver (f ∘ e) := by
  unfold avgOver
  rw [Fintype.card_congr e, Function.comp_def, e.sum_comp f]

lemma avgOver_prod_mul {α β : Type*} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    avgOver (fun p : α × β => f p.1 * g p.2) = avgOver f * avgOver g := by
  unfold avgOver
  rw [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, mul_inv]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma avgOver_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    avgOver (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avgOver (f i) := by
  unfold avgOver
  rw [Finset.sum_comm, Finset.mul_sum]

lemma avgOver_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avgOver (fun a => c * f a) = c * avgOver f := by
  unfold avgOver
  rw [← Finset.mul_sum]; ring

lemma avgOver_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avgOver (fun _ : α => c) = c := by
  unfold avgOver
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-! ### Item 2b: moments of a sum of independent terms -/

theorem moments_sum_indep {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    ∀ (L : ℕ) (X : Fin L → Ω → ℝ) (p : ℕ),
      avgOver (fun ω : Fin L → Ω => (∑ ℓ, X ℓ (ω ℓ)) ^ p) =
        (p.factorial : ℝ) * PowerSeries.coeff p (∏ ℓ, egf fun k => avgOver fun s => X ℓ s ^ k)
  | 0, X, p => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, PowerSeries.coeff_one]
    rw [avgOver_const]
    rcases p with _ | p <;> simp
  | L + 1, X, p => by
    rw [avgOver_equiv (Fin.consEquiv fun _ => Ω)]
    have hpt : ((fun ω : Fin (L + 1) → Ω => (∑ ℓ, X ℓ (ω ℓ)) ^ p) ∘ Fin.consEquiv fun _ => Ω) =
        fun q : Ω × (Fin L → Ω) => ∑ k ∈ Finset.range (p + 1), (p.choose k : ℝ) *
          (X 0 q.1 ^ k * (∑ ℓ : Fin L, X ℓ.succ (q.2 ℓ)) ^ (p - k)) := by
      funext q
      simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero,
        Fin.cons_succ, add_pow]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hpt, avgOver_sum, Fin.prod_univ_succ, coeff_egf_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hm := avgOver_prod_mul (fun a => X 0 a ^ k)
      (fun ω' : Fin L → Ω => (∑ ℓ : Fin L, X ℓ.succ (ω' ℓ)) ^ (p - k))
    rw [avgOver_const_mul, hm, moments_sum_indep L (fun ℓ => X ℓ.succ) (p - k)]
    ring

/-! ### Item 2a: moments of a Rademacher sum -/

lemma avg_sign_pow (a : ℝ) (k : ℕ) :
    avgOver (fun b : Bool => (a * signOf b) ^ k) = if Even k then a ^ k else 0 := by
  unfold avgOver
  simp only [Fintype.card_bool, Fintype.sum_bool, signOf, if_true, Bool.false_eq_true, if_false,
    mul_one, mul_neg]
  split_ifs with hk
  · rw [hk.neg_pow]; ring
  · rw [(Nat.not_even_iff_odd.mp hk).neg_pow]; ring

theorem rademacher_moment (n : ℕ) (c : ℝ) (a : Fin n → ℝ) (m : ℕ) :
    avgOver (fun s : Fin n → Bool => (c + ∑ r, a r * signOf (s r)) ^ m) =
      (m.factorial : ℝ) * PowerSeries.coeff m (expSeries c * ∏ r, coshSeries (a r)) := by
  have hpt : (fun s : Fin n → Bool => (c + ∑ r, a r * signOf (s r)) ^ m) =
      fun s => ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * c ^ k *
        (∑ r, a r * signOf (s r)) ^ (m - k) := by
    funext s
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hpt, avgOver_sum, expSeries, coeff_egf_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [avgOver_const_mul, moments_sum_indep n (fun r b => a r * signOf b) (m - k)]
  congr 3
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [coshSeries]
  congr 1
  funext k
  exact avg_sign_pow (a r) k

end DetANNSignAux

open DetANNSignAux in
theorem solution :
    (∀ (n : ℕ) (c : ℝ) (a : Fin n → ℝ) (m : ℕ),
      avgOver (fun s : Fin n → Bool => (c + ∑ r, a r * signOf (s r)) ^ m) =
        (m.factorial : ℝ) * PowerSeries.coeff m (expSeries c * ∏ r, coshSeries (a r))) ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (L : ℕ) (X : Fin L → Ω → ℝ) (p : ℕ),
      avgOver (fun ω : Fin L → Ω => (∑ ℓ, X ℓ (ω ℓ)) ^ p) =
        (p.factorial : ℝ) * PowerSeries.coeff p (∏ ℓ, egf fun k => avgOver fun s => X ℓ s ^ k) :=
  ⟨rademacher_moment, fun _ _ _ => moments_sum_indep⟩
