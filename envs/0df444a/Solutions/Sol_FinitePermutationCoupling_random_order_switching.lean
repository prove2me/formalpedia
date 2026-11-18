-- Prove2me | solution 1 for FinitePermutationCoupling.random_order_switching
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T19:38:39.005096+00:00
-- url     : https://prove2.me/submissions/d1aaa711-578e-4184-9a0d-c84bcfab59b2

import Definitions.Def_FinitePermutationCoupling_BlockModel
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

section

namespace FinitePermutationCoupling

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The correction kernel in the random-order swap construction. -/
def residualKernel (P : Matrix α α ℝ) : Matrix α α ℝ :=
  fun u v => 1 - ((Fintype.card α : ℝ) - 1) * P u v

/-- A uniform upper bound on the conditional matching probabilities makes the
correction kernel nonnegative; its row and column sums remain one. -/
theorem residualKernel_doubly_stochastic (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α)
    (hcap : ∀ u v, ((Fintype.card α : ℝ) - 1) * P u v ≤ 1) :
    residualKernel P ∈ doublyStochastic ℝ α := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun u v => sub_nonneg.mpr (hcap u v), ?_, ?_⟩
  · intro u
    simp only [residualKernel, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
      sum_row_of_mem_doublyStochastic hP]
    ring
  · intro v
    simp only [residualKernel, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
      sum_col_of_mem_doublyStochastic hP]
    ring

theorem residualKernel_doubly_stochastic_of_bound (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α) (hm : 2 ≤ Fintype.card α)
    (hcap : ∀ u v, P u v ≤ 1 / ((Fintype.card α : ℝ) - 1)) :
    residualKernel P ∈ doublyStochastic ℝ α := by
  apply residualKernel_doubly_stochastic P hP
  intro u v
  have hmR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hm
  have hm' : 0 < (Fintype.card α : ℝ) - 1 := by linarith
  have hp := (le_div_iff₀ hm').mp (hcap u v)
  simpa only [mul_comm] using hp

/-- Mixing the original conditional partner law with the correction kernel
with respective probabilities `1-1/m` and `1/m` gives an exactly uniform partner. -/
theorem residualKernel_uniform_mixture [Nonempty α] (P : Matrix α α ℝ) (u v : α) :
    (1 - 1 / (Fintype.card α : ℝ)) * P u v +
      (1 / (Fintype.card α : ℝ)) * residualKernel P u v =
      1 / (Fintype.card α : ℝ) := by
  have hm : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold residualKernel
  field_simp
  ring

/-- Exchange the values of the current relabelling at the two selected partners. -/
def correct (φ : Equiv.Perm α) (y z : α) : Equiv.Perm α :=
  (Equiv.swap y z).trans φ

theorem correct_at_left (φ : Equiv.Perm α) (y z : α) :
    correct φ y z y = φ z := by simp [correct]

theorem correct_off (φ : Equiv.Perm α) (y z v : α) (hy : v ≠ y) (hz : v ≠ z) :
    correct φ y z v = φ v := by
  simp only [correct, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hy hz]

/-- Swaps within the active residual set preserve every already settled value. -/
theorem correct_preserves_settled (φ : Equiv.Perm α) (V : Finset α)
    {y z v : α} (hy : y ∈ V) (hz : z ∈ V) (hv : v ∉ V) :
    correct φ y z v = φ v := by
  apply correct_off
  · intro h; exact hv (h.symm ▸ hy)
  · intro h; exact hv (h.symm ▸ hz)

/-- For a fixed reference bijection, the unnormalized correction mass that can
move any specified value is at most two: one row and one column of the kernel. -/
theorem correction_touch_mass_le_two (T : Matrix α α ℝ)
    (hT : T ∈ doublyStochastic ℝ α) (h : Equiv.Perm α) (v : α) :
    (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤ 2 := by
  have hn (u z : α) : 0 ≤ T u z := nonneg_of_mem_doublyStochastic hT
  have hpoint (u z : α) :
      (if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤
        (if h u = v then T u z else 0) + (if z = v then T u z else 0) := by
    by_cases hu : h u = v
    · simp only [if_pos hu]
      split_ifs <;> linarith [hn u z]
    · by_cases hz : z = v
      · simp only [if_neg hu, if_pos hz, zero_add]
        split_ifs <;> linarith [hn u z]
      · have hfix := Equiv.swap_apply_of_ne_of_ne (Ne.symm hu) (Ne.symm hz)
        simp only [hfix, ne_eq, not_true_eq_false, if_false, if_neg hu, if_neg hz, add_zero,
          le_refl]
  have hrow : (∑ u, ∑ z, if h u = v then T u z else 0) = 1 := by
    calc
      _ = ∑ u, if h u = v then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : h u = v
        · simp only [if_pos hu, sum_row_of_mem_doublyStochastic hT]
        · simp [hu]
      _ = ∑ u, if u = v then (1 : ℝ) else 0 := Fintype.sum_equiv h _ _ (fun _ => rfl)
      _ = 1 := by simp
  have hcol : (∑ u, ∑ z, if z = v then T u z else 0) = 1 := by
    simpa using sum_col_of_mem_doublyStochastic hT v
  calc
    _ ≤ ∑ u, ∑ z, ((if h u = v then T u z else 0) +
        (if z = v then T u z else 0)) := by
      apply Finset.sum_le_sum
      intro u _
      exact Finset.sum_le_sum (fun z _ => hpoint u z)
    _ = (∑ u, ∑ z, if h u = v then T u z else 0) +
        (∑ u, ∑ z, if z = v then T u z else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 := by rw [hrow, hcol]; norm_num

/-- The actual probability mass of moving `v` in the correction branch:
the branch has probability `1/m`, and the next residual input is uniform. -/
noncomputable def correctionMoveMass (T : Matrix α α ℝ) (h : Equiv.Perm α) (v : α) : ℝ :=
  (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) /
    (Fintype.card α : ℝ) ^ 2

theorem correctionMoveMass_le (T : Matrix α α ℝ)
    (hT : T ∈ doublyStochastic ℝ α) (h : Equiv.Perm α) (v : α) :
    correctionMoveMass T h v ≤ 2 / (Fintype.card α : ℝ) ^ 2 := by
  exact div_le_div_of_nonneg_right (correction_touch_mass_le_two T hT h v) (sq_nonneg _)

/-- A pointwise forward-disagreement bound conditional on the entire reference
permutation also bounds inverse disagreement, by querying its fixed preimage. -/
theorem inverse_disagreement_iff (g h : Equiv.Perm α) (v : α) :
    g.symm v ≠ h.symm v ↔ g (h.symm v) ≠ v := by
  constructor
  · intro hne he
    apply hne
    exact (congrArg g.symm he).symm.trans (g.symm_apply_apply (h.symm v))
  · intro hne he
    apply hne
    rw [← he, g.apply_symm_apply]

/-- A complete one-step correction kernel: it uniformizes the sampled partner
and has a pointwise `2/m²` correction-move bound for every fixed reference map. -/
theorem residual_correction_kernel_proof (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α) (hm : 2 ≤ Fintype.card α)
    (hcap : ∀ u v, P u v ≤ 1 / ((Fintype.card α : ℝ) - 1)) :
    ∃ T : Matrix α α ℝ,
      T ∈ doublyStochastic ℝ α ∧
      (∀ u v, (1 - 1 / (Fintype.card α : ℝ)) * P u v +
        (1 / (Fintype.card α : ℝ)) * T u v = 1 / (Fintype.card α : ℝ)) ∧
      ∀ (h : Equiv.Perm α) (v : α),
        (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) /
            (Fintype.card α : ℝ) ^ 2 ≤ 2 / (Fintype.card α : ℝ) ^ 2 := by
  have hT := residualKernel_doubly_stochastic_of_bound P hP hm hcap
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  exact ⟨residualKernel P, hT, residualKernel_uniform_mixture P,
    fun h v => correctionMoveMass_le _ hT h v⟩

/-- The local correction step, including singleton residual sets. The cap is
written without division so the same statement covers every nonempty set. -/
theorem correction_step_proof [Nonempty α] (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α)
    (hcap : ∀ u v, ((Fintype.card α : ℝ) - 1) * P u v ≤ 1) :
    ∃ T : Matrix α α ℝ,
      T ∈ doublyStochastic ℝ α ∧
      (∀ u v, (1 - 1 / (Fintype.card α : ℝ)) * P u v +
        (1 / (Fintype.card α : ℝ)) * T u v = 1 / (Fintype.card α : ℝ)) ∧
      ∀ (h : Equiv.Perm α) (v : α),
        (1 / (Fintype.card α : ℝ) ^ 2) *
            (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤
          2 / (Fintype.card α : ℝ) ^ 2 := by
  have hT := residualKernel_doubly_stochastic P hP hcap
  refine ⟨residualKernel P, hT, residualKernel_uniform_mixture P, ?_⟩
  intro h v
  simpa only [correctionMoveMass, div_eq_mul_inv, one_mul, mul_one, mul_comm]
    using correctionMoveMass_le _ hT h v

end FinitePermutationCoupling

end

section

namespace FinitePermutationCoupling

open scoped BigOperators

section RandomOrder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every fixed item has the same chance of lying in a prescribed set of ranks
under a uniformly chosen order. This is an exact finite counting identity. -/
theorem uniform_perm_survival (S : Finset α) (x : α) :
    (∑ σ : Equiv.Perm α,
      if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) =
        (S.card : ℝ) / (Fintype.card α : ℝ) := by
  classical
  let mass (y : α) : ℝ := ∑ σ : Equiv.Perm α, if σ y ∈ S then 1 else 0
  have hsame (y : α) : mass y = mass x := by
    apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap x y))
    intro σ
    simp [Equiv.Perm.mul_apply]
  have hone (σ : Equiv.Perm α) :
      (∑ y : α, if σ y ∈ S then (1 : ℝ) else 0) = S.card := by
    calc
      _ = ∑ y : α, if y ∈ S then (1 : ℝ) else 0 :=
        Fintype.sum_equiv σ _ _ (fun _ => rfl)
      _ = _ := by simp
  have htotal : (Fintype.card α : ℝ) * mass x =
      (Fintype.card (Equiv.Perm α) : ℝ) * S.card := by
    calc
      _ = ∑ y : α, mass y := by simp only [hsame, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      _ = ∑ σ : Equiv.Perm α, ∑ y : α, if σ y ∈ S then (1 : ℝ) else 0 :=
        Finset.sum_comm
      _ = _ := by simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have ha : (Fintype.card α : ℝ) ≠ 0 := by
    have : Nonempty α := ⟨x⟩
    exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmass : (∑ σ : Equiv.Perm α,
      if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) =
      mass x / (Fintype.card (Equiv.Perm α) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp
  rw [hmass]
  apply (div_eq_div_iff hp ha).mpr
  simpa only [mul_comm] using htotal

/-- Auxiliary process data can be correlated with the order. The uniform order
marginal alone determines the survival mass; independence is unnecessary. -/
theorem uniform_perm_survival_of_marginal {Ω : Type*} [Fintype Ω]
    (w : Equiv.Perm α → Ω → ℝ) (a : ℝ)
    (hrow : ∀ σ, (∑ ω, w σ ω) = a / (Fintype.card (Equiv.Perm α) : ℝ))
    (S : Finset α) (x : α) :
    (∑ σ : Equiv.Perm α, ∑ ω, if σ x ∈ S then w σ ω else 0) =
      ((S.card : ℝ) / (Fintype.card α : ℝ)) * a := by
  classical
  calc
    _ = ∑ σ : Equiv.Perm α,
        (if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) * a := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hh : σ x ∈ S <;> simp [hh, hrow, div_eq_mul_inv, mul_comm]
    _ = (∑ σ : Equiv.Perm α,
        if σ x ∈ S then 1 / (Fintype.card (Equiv.Perm α) : ℝ) else 0) * a :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [uniform_perm_survival]

/-- With `r` of `m` ranks still active, a fixed item survives with probability
exactly `r/m`, including the first and last stages. -/
theorem uniform_order_survival (m r : ℕ) (hr : r ≤ m) (x : Fin m) :
    (∑ σ : Equiv.Perm (Fin m),
      if (σ x).val < r then 1 / (Fintype.card (Equiv.Perm (Fin m)) : ℝ) else 0) =
        (r : ℝ) / (m : ℝ) := by
  have hh := uniform_perm_survival (Finset.univ.filter (fun y : Fin m => y.val < r)) x
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.card_filter_val_lt, min_eq_right hr, Fintype.card_fin] using hh

theorem uniform_order_survival_of_marginal {Ω : Type*} [Fintype Ω]
    (m r : ℕ) (hr : r ≤ m) (w : Equiv.Perm (Fin m) → Ω → ℝ) (a : ℝ)
    (hrow : ∀ σ, (∑ ω, w σ ω) = a / (Fintype.card (Equiv.Perm (Fin m)) : ℝ))
    (x : Fin m) :
    (∑ σ : Equiv.Perm (Fin m), ∑ ω, if (σ x).val < r then w σ ω else 0) =
      ((r : ℝ) / (m : ℝ)) * a := by
  have hh := uniform_perm_survival_of_marginal w a hrow
    (Finset.univ.filter (fun y : Fin m => y.val < r)) x
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.card_filter_val_lt, min_eq_right hr, Fintype.card_fin] using hh

end RandomOrder

section Weighted

variable {Ω : Type*} [Fintype Ω]

/-- A bound conditional on activity combines with the activity marginal by a
finite weighted sum; the total mass `a` need not be normalized to one. -/
theorem weighted_activity_error_le (μ err : Ω → ℝ) (active : Ω → Prop)
    [DecidablePred active] (m r a : ℝ) (hm : 0 < m) (hr : 0 < r)
    (hlocal : ∀ ω, err ω ≤ (2 / r ^ 2) * (if active ω then μ ω else 0))
    (hsurvive : (∑ ω, if active ω then μ ω else 0) ≤ (r / m) * a) :
    (∑ ω, err ω) ≤ (2 / (m * r)) * a := by
  calc
    _ ≤ ∑ ω, (2 / r ^ 2) * (if active ω then μ ω else 0) :=
      Finset.sum_le_sum (fun ω _ => hlocal ω)
    _ = (2 / r ^ 2) * (∑ ω, if active ω then μ ω else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 / r ^ 2) * ((r / m) * a) :=
      mul_le_mul_of_nonneg_left hsurvive (by positivity)
    _ = _ := by field_simp

/-- The edge-class lower bound turns the survival-scaled local correction
error into the stage bound used by the switching-chain certificate. -/
theorem survival_scaled_le_dyadic (n m r : ℕ) (hn : 1 ≤ n)
    (hm : 2 ^ (n - 1) ≤ m) (hr : 0 < r) :
    2 / ((m : ℝ) * r) ≤ 4 / ((2 : ℝ) ^ n * r) := by
  have hmpos : 0 < m := lt_of_lt_of_le (pow_pos (by norm_num) _) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hpow : (2 : ℝ) ^ n ≤ 2 * m := by
    have hh : (2 : ℝ) ^ (n - 1) ≤ m := by exact_mod_cast hm
    have hn' : n = (n - 1) + 1 := by omega
    rw [hn', pow_succ]
    nlinarith
  apply (div_le_div_iff₀ (mul_pos hmR hrR) (mul_pos (by positivity) hrR)).mpr
  nlinarith

theorem weighted_activity_error_le_dyadic (μ err : Ω → ℝ) (active : Ω → Prop)
    [DecidablePred active] (n m r : ℕ) (a : ℝ) (ha : 0 ≤ a) (hn : 1 ≤ n)
    (hm : 2 ^ (n - 1) ≤ m) (hr : 0 < r)
    (hlocal : ∀ ω, err ω ≤ (2 / (r : ℝ) ^ 2) * (if active ω then μ ω else 0))
    (hsurvive : (∑ ω, if active ω then μ ω else 0) ≤ ((r : ℝ) / m) * a) :
    (∑ ω, err ω) ≤ (4 / ((2 : ℝ) ^ n * r)) * a := by
  have hmpos : 0 < m := lt_of_lt_of_le (pow_pos (by norm_num) _) hm
  have hh := weighted_activity_error_le μ err active (m : ℝ) (r : ℝ) a
    (by exact_mod_cast hmpos) (by exact_mod_cast hr) hlocal hsurvive
  exact hh.trans (mul_le_mul_of_nonneg_right (survival_scaled_le_dyadic n m r hn hm hr) ha)

end Weighted

end FinitePermutationCoupling

end

section

namespace FinitePermutationCoupling

open Classical
open scoped BigOperators

variable {α κ : Type*} [Fintype α]

theorem block_swap_apply (block : α → κ) {z w : α} (hzw : block z = block w)
    (x : α) : block (Equiv.swap z w x) = block x := by
  by_cases hx : x = z
  · subst x; simpa using hzw.symm
  by_cases hx' : x = w
  · subst x; simpa using hzw
  rw [Equiv.swap_apply_of_ne_of_ne hx hx']

theorem exposed_block_image_mem (block : α → κ) (D : Finset α)
    (h π : Equiv.Perm α) {u : α} (hu : u ∉ D)
    (hπ : π ∈ exposedFiber (blockSupport block) D h) :
    π u ∈ blockFiber block u \ D.image h := by
  obtain ⟨hπb, hπD⟩ := Finset.mem_filter.mp hπ
  have hb := (Finset.mem_filter.mp hπb).2
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · simp only [blockFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb u
  · rintro him
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp him
    have hdu : d = u := π.injective ((hπD d hd).trans heq)
    exact hu (hdu ▸ hd)

theorem exposed_block_swap_mem (block : α → κ) (D : Finset α)
    (h π : Equiv.Perm α) {u z w : α}
    (hz : z ∈ blockFiber block u \ D.image h)
    (hw : w ∈ blockFiber block u \ D.image h)
    (hπ : π ∈ exposedFiber (blockSupport block) D h) :
    Equiv.swap z w * π ∈ exposedFiber (blockSupport block) D h := by
  obtain ⟨hzB, hzD⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨hwB, hwD⟩ := Finset.mem_sdiff.mp hw
  have hzC := (Finset.mem_filter.mp hzB).2
  have hwC := (Finset.mem_filter.mp hwB).2
  obtain ⟨hπb, hπD⟩ := Finset.mem_filter.mp hπ
  have hb := (Finset.mem_filter.mp hπb).2
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro x
    simpa only [Equiv.Perm.mul_apply, block_swap_apply block (hzC.trans hwC.symm)] using hb x
  · intro d hd
    simp only [Equiv.Perm.mul_apply, hπD d hd]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      apply hzD
      exact heq ▸ Finset.mem_image.mpr ⟨d, hd, rfl⟩
    · intro heq
      apply hwD
      exact heq ▸ Finset.mem_image.mpr ⟨d, hd, rfl⟩

theorem exposed_block_partner_card_eq (block : α → κ) (D : Finset α)
    (h : Equiv.Perm α) {u z w : α}
    (hz : z ∈ blockFiber block u \ D.image h)
    (hw : w ∈ blockFiber block u \ D.image h) :
    ((exposedFiber (blockSupport block) D h).filter fun π => π u = z).card =
      ((exposedFiber (blockSupport block) D h).filter fun π => π u = w).card := by
  apply Finset.card_bij (fun π _ => Equiv.swap z w * π)
  · intro π hπ
    obtain ⟨hπR, hπu⟩ := Finset.mem_filter.mp hπ
    apply Finset.mem_filter.mpr
    refine ⟨exposed_block_swap_mem block D h π hz hw hπR, ?_⟩
    simp [Equiv.Perm.mul_apply, hπu]
  · intro π _ ρ _ heq
    exact mul_left_cancel heq
  · intro ρ hρ
    obtain ⟨hρR, hρu⟩ := Finset.mem_filter.mp hρ
    refine ⟨Equiv.swap z w * ρ, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨exposed_block_swap_mem block D h ρ hz hw hρR, ?_⟩
      simp [Equiv.Perm.mul_apply, hρu]
    · ext x
      simp [Equiv.Perm.mul_apply]

theorem exposed_block_card_factor (block : α → κ) (D : Finset α)
    (h : Equiv.Perm α) {u z : α} (hu : u ∉ D)
    (hz : z ∈ blockFiber block u \ D.image h) :
    (exposedFiber (blockSupport block) D h).card =
      (blockFiber block u \ D.image h).card *
        ((exposedFiber (blockSupport block) D h).filter fun π => π u = z).card := by
  calc
    _ = ∑ w ∈ blockFiber block u \ D.image h,
        ((exposedFiber (blockSupport block) D h).filter fun π => π u = w).card :=
      Finset.card_eq_sum_card_fiberwise (fun π hπ => exposed_block_image_mem block D h π hu hπ)
    _ = _ := by
      rw [Finset.sum_congr rfl (fun w hw => exposed_block_partner_card_eq block D h hw hz)]
      simp

theorem exposed_block_partner_nonempty (block : α → κ) (D : Finset α)
    (h : Equiv.Perm α) {u z : α} (hu : u ∉ D)
    (hR : (exposedFiber (blockSupport block) D h).Nonempty)
    (hz : z ∈ blockFiber block u \ D.image h) :
    ((exposedFiber (blockSupport block) D h).filter fun π => π u = z).Nonempty := by
  obtain ⟨π, hπ⟩ := hR
  refine ⟨Equiv.swap (π u) z * π, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact exposed_block_swap_mem block D h π
      (exposed_block_image_mem block D h π hu hπ) hz hπ
  · simp [Equiv.Perm.mul_apply]

theorem exposed_block_density_extension (block : α → κ) (D : Finset α)
    (h : Equiv.Perm α) {u z : α} (hu : u ∉ D)
    (hR : (exposedFiber (blockSupport block) D h).Nonempty)
    (hz : z ∈ blockFiber block u \ D.image h) (π : Equiv.Perm α) :
    density (exposedFiber (blockSupport block) D h) π * (if π u = z then 1 else 0) =
      (1 / ((blockFiber block u \ D.image h).card : ℝ)) *
        density ((exposedFiber (blockSupport block) D h).filter fun ρ => ρ u = z) π := by
  have hcard := exposed_block_card_factor block D h hu hz
  have hcardR := Finset.card_pos.mpr hR
  have hcardZ := Finset.card_pos.mpr (exposed_block_partner_nonempty block D h hu hR hz)
  have hcardV := Finset.card_pos.mpr (show (blockFiber block u \ D.image h).Nonempty from ⟨z, hz⟩)
  by_cases hπ : π ∈ exposedFiber (blockSupport block) D h
  · by_cases hπu : π u = z
    · simp only [density, hπ, if_true, hπu, mul_one, Finset.mem_filter, and_self]
      rw [hcard, Nat.cast_mul]
      field_simp
    · simp [density, hπ, hπu]
  · simp [density, hπ]

end FinitePermutationCoupling

end

section

namespace FinitePermutationCoupling.RandomOrder

open Classical
open scoped BigOperators

variable {α κ : Type*} [Fintype α]

noncomputable def conditionalPartner (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h : Equiv.Perm α) (x y : α) : ℝ :=
  (((exposedFiber S D h).filter fun π => π x = y).card : ℝ) /
    (exposedFiber S D h).card

theorem exposed_self_mem (S : Finset (Equiv.Perm α)) (D : Finset α)
    {h : Equiv.Perm α} (hh : h ∈ S) : h ∈ exposedFiber S D h := by
  simp [exposedFiber, hh]

theorem exposed_subset_block (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α) :
    exposedFiber S D h ⊆ exposedFiber (blockSupport block) D h := by
  intro π hπ
  exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hπ).1, (Finset.mem_filter.mp hπ).2⟩

theorem residual_image_mem (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α) (u : α)
    {π : Equiv.Perm α} (hπ : π ∈ exposedFiber S D h)
    {x : α} (hx : x ∈ blockFiber block u \ D) :
    π x ∈ blockFiber block u \ D.image h := by
  obtain ⟨hxC, hxD⟩ := Finset.mem_sdiff.mp hx
  have hxu := (Finset.mem_filter.mp hxC).2
  have hh := exposed_block_image_mem block D h π hxD
    (exposed_subset_block block S hsub D h hπ)
  have hC : blockFiber block x = blockFiber block u := by
    ext y
    simp [blockFiber, hxu]
  rwa [hC] at hh

theorem residual_preimage_mem (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α) (u : α)
    {π : Equiv.Perm α} (hπ : π ∈ exposedFiber S D h)
    {y : α} (hy : y ∈ blockFiber block u \ D.image h) :
    π.symm y ∈ blockFiber block u \ D := by
  obtain ⟨hπS, hπD⟩ := Finset.mem_filter.mp hπ
  have hb := (Finset.mem_filter.mp (hsub hπS)).2
  obtain ⟨hyC, hyD⟩ := Finset.mem_sdiff.mp hy
  have hyu := (Finset.mem_filter.mp hyC).2
  apply Finset.mem_sdiff.mpr
  constructor
  · simp only [blockFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hb (π.symm y)
    rw [π.apply_symm_apply] at hh
    exact hh.symm.trans hyu
  · intro hd
    apply hyD
    refine Finset.mem_image.mpr ⟨π.symm y, hd, ?_⟩
    rw [← hπD _ hd, π.apply_symm_apply]

theorem residual_card_eq (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α)
    (hh : h ∈ S) (u : α) :
    (blockFiber block u \ D).card = (blockFiber block u \ D.image h).card := by
  have href := exposed_self_mem S D hh
  refine Finset.card_bij (fun x _ => h x) ?_ ?_ ?_
  · intro x hx
    exact residual_image_mem block S hsub D h u href hx
  · intro x _ y _ hxy
    exact h.injective hxy
  · intro y hy
    exact ⟨h.symm y, residual_preimage_mem block S hsub D h u href hy, h.apply_symm_apply y⟩

theorem conditionalPartner_nonneg (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h : Equiv.Perm α) (x y : α) : 0 ≤ conditionalPartner S D h x y := by
  unfold conditionalPartner
  positivity

theorem conditionalPartner_row (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α)
    (hh : h ∈ S) (u : α) {x : α} (hx : x ∈ blockFiber block u \ D) :
    (∑ y ∈ blockFiber block u \ D.image h, conditionalPartner S D h x y) = 1 := by
  have hQ : (0 : ℝ) < (exposedFiber S D h).card := by
    exact_mod_cast Finset.card_pos.mpr (show (exposedFiber S D h).Nonempty from
      ⟨h, exposed_self_mem S D hh⟩)
  have hc := Finset.card_eq_sum_card_fiberwise
    (fun π hπ => residual_image_mem block S hsub D h u hπ hx)
  simp only [conditionalPartner, ← Finset.sum_div]
  rw [← Nat.cast_sum, ← hc]
  exact div_self (ne_of_gt hQ)

theorem conditionalPartner_col (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α)
    (hh : h ∈ S) (u : α) {y : α} (hy : y ∈ blockFiber block u \ D.image h) :
    (∑ x ∈ blockFiber block u \ D, conditionalPartner S D h x y) = 1 := by
  have hQ : (0 : ℝ) < (exposedFiber S D h).card := by
    exact_mod_cast Finset.card_pos.mpr (show (exposedFiber S D h).Nonempty from
      ⟨h, exposed_self_mem S D hh⟩)
  have hc := Finset.card_eq_sum_card_fiberwise
    (fun π hπ => residual_preimage_mem block S hsub D h u hπ hy)
  have hcond (π : Equiv.Perm α) (x : α) : π x = y ↔ π.symm y = x := by
    constructor
    · intro he; rw [← he, π.symm_apply_apply]
    · intro he; rw [← he, π.apply_symm_apply]
  simp only [conditionalPartner, hcond, ← Finset.sum_div]
  rw [← Nat.cast_sum, ← hc]
  exact div_self (ne_of_gt hQ)

theorem conditionalPartner_cap (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hcap : PartnerCap block active S)
    (D : Finset α) (h : Equiv.Perm α) (hh : h ∈ S)
    (u : α) (hu : active (block u)) {x : α} (hx : x ∈ blockFiber block u \ D) (y : α) :
    (((blockFiber block u \ D).card : ℝ) - 1) * conditionalPartner S D h x y ≤ 1 := by
  obtain ⟨hxC, hxD⟩ := Finset.mem_sdiff.mp hx
  have hxu := (Finset.mem_filter.mp hxC).2
  have hC : blockFiber block x = blockFiber block u := by
    ext z
    simp [blockFiber, hxu]
  have hc := hcap D h x y (hxu.symm ▸ hu) hxD
  rw [hC] at hc
  have hU : 1 ≤ (blockFiber block u \ D).card := Finset.card_pos.mpr ⟨x, hx⟩
  have hQ : (0 : ℝ) < (exposedFiber S D h).card := by
    exact_mod_cast Finset.card_pos.mpr (show (exposedFiber S D h).Nonempty from
      ⟨h, exposed_self_mem S D hh⟩)
  have hcR : (((blockFiber block u \ D).card : ℝ) - 1) *
      (((exposedFiber S D h).filter fun π => π x = y).card : ℝ) ≤
        (exposedFiber S D h).card := by
    exact_mod_cast hc
  unfold conditionalPartner
  rw [← mul_div_assoc]
  exact (div_le_one hQ).mpr hcR

end FinitePermutationCoupling.RandomOrder

end

section

namespace FinitePermutationCoupling.RandomOrder

open Classical
open scoped BigOperators

section FiniteProcess

variable {State Event : Type*} [Fintype Event]

/-- Exact finite trace weights of a state-dependent transition kernel. -/
noncomputable def traceWeight (K : State → Event → ℝ) (next : State → Event → State) :
    (t : ℕ) → State → (Fin t → Event) → ℝ
  | 0, _, _ => 1
  | t + 1, s, e => K s (e 0) * traceWeight K next t (next s (e 0)) (Fin.tail e)

theorem traceWeight_nonneg (K : State → Event → ℝ) (next : State → Event → State)
    (hK : ∀ s e, 0 ≤ K s e) (t : ℕ) (s : State) (e : Fin t → Event) :
    0 ≤ traceWeight K next t s e := by
  induction t generalizing s with
  | zero => simp [traceWeight]
  | succ t ih => exact mul_nonneg (hK _ _) (ih _ _)

theorem traceWeight_sum (K : State → Event → ℝ) (next : State → Event → State)
    (hK : ∀ s, (∑ e, K s e) = 1) (t : ℕ) (s : State) :
    (∑ e : Fin t → Event, traceWeight K next t s e) = 1 := by
  induction t generalizing s with
  | zero => simp [traceWeight]
  | succ t ih =>
    calc
      _ = ∑ e : Event × (Fin t → Event),
          K s e.1 * traceWeight K next t (next s e.1) e.2 :=
        Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (t + 1) => Event)).symm _ _
          (fun _ => rfl)
      _ = ∑ e : Event, K s e * ∑ tail : Fin t → Event,
          traceWeight K next t (next s e) tail := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.mul_sum]
      _ = 1 := by simp only [ih, mul_one, hK]

theorem traceWeight_succ_sum (K : State → Event → ℝ) (next : State → Event → State)
    (t : ℕ) (s : State) (f : (Fin (t + 1) → Event) → ℝ) :
    (∑ e, traceWeight K next (t + 1) s e * f e) =
      ∑ a : Event, K s a * ∑ tail : Fin t → Event,
        traceWeight K next t (next s a) tail * f (Fin.cons a tail) := by
  calc
    _ = ∑ e : Event × (Fin t → Event),
        (K s e.1 * traceWeight K next t (next s e.1) e.2) *
          f (Fin.cons e.1 e.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (t + 1) => Event)).symm _ _
        (fun _ => by simp only [traceWeight, Fin.consEquiv, Equiv.coe_fn_symm_mk,
          Fin.cons_self_tail])
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [Finset.mul_sum, mul_assoc]

theorem traceWeight_deterministic [DecidableEq Event]
    (K : State → Event → ℝ) (next : State → Event → State)
    (s : State) (a : Event) (hK : ∀ e, K s e = if e = a then 1 else 0)
    (hnext : next s a = s) (t : ℕ) (e : Fin t → Event) :
    traceWeight K next t s e = if e = (fun _ => a) then 1 else 0 := by
  induction t with
  | zero => simp [traceWeight, Subsingleton.elim e (fun _ => a)]
  | succ t ih =>
    by_cases he : e 0 = a
    · simp only [traceWeight, hK, he, if_true, hnext, one_mul, ih]
      congr 1
      apply propext
      constructor
      · intro ht
        ext i
        exact Fin.cases he (fun j => congrFun ht j) i
      · intro ht
        exact congrArg Fin.tail ht
    · have hne : e ≠ (fun _ => a) := fun h => he (congrFun h 0)
      simp only [traceWeight, hK, if_neg he, zero_mul, if_neg hne]

end FiniteProcess

section SwitchingProcess

variable {α κ : Type*} [Fintype α]

noncomputable def remaining (block : α → κ) (active : κ → Prop) (D : Finset α) :
    Finset α := Finset.univ.filter fun x => active (block x) ∧ x ∉ D

noncomputable def nextClass (block : α → κ) (active : κ → Prop) (D : Finset α) :
    Option α :=
  if h : (remaining block active D).Nonempty then some h.choose else none

noncomputable def residualInputs (block : α → κ) (active : κ → Prop) (D : Finset α) :
    Finset α :=
  match nextClass block active D with
  | none => ∅
  | some x => blockFiber block x \ D

noncomputable def advance (D : Finset α) : Option (α × α) → Finset α
  | none => D
  | some (u, _) => insert u D

/-- The conditional original-partner law. This depends on the reference only
through its already exposed values on `D`. -/
noncomputable def partnerProb (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h : Equiv.Perm α) (u z : α) : ℝ :=
  (((exposedFiber S D h).filter fun π => π u = z).card : ℝ) /
    (exposedFiber S D h).card

/-- The source's random-order correction, including identity padding after all
active inputs have been exposed. The two coordinates are original input and
original output, so the previous correction choices do not occur in this law. -/
noncomputable def transition (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (h : Equiv.Perm α) (D : Finset α) :
    Option (α × α) → ℝ :=
  match nextClass block active D with
  | none => fun e => if e = none then 1 else 0
  | some x => fun e =>
    match e with
    | none => 0
    | some (u, z) =>
      let U := blockFiber block x \ D
      let V := blockFiber block x \ D.image h
      let r : ℝ := U.card
      if u ∈ U ∧ z ∈ V then
        (1 / r) * ((1 - 1 / r) * (if z = h u then 1 else 0) +
          (1 / r) * (1 - (r - 1) * partnerProb S D h u z))
      else 0

noncomputable def switchingTraceWeight (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (h : Equiv.Perm α) (D : Finset α) (t : ℕ)
    (e : Fin t → Option (α × α)) : ℝ :=
  traceWeight (transition block active S h) advance t D e

/-- Read a trace at residual-count threshold `i`. Events with residual count
larger than `i` have happened; the others have not. Disjoint blocks therefore
assemble into one common stage-indexed permutation path. -/
noncomputable def outputAt (block : α → κ) (active : κ → Prop) (h : Equiv.Perm α)
    (i : ℕ) : (t : ℕ) → Finset α → Equiv.Perm α →
      (Fin t → Option (α × α)) → Equiv.Perm α
  | 0, _, φ, _ => φ
  | t + 1, D, φ, e =>
      let φ' := match e 0 with
        | none => φ
        | some (u, z) =>
            if i < (residualInputs block active D).card then correct φ (h u) z else φ
      outputAt block active h i t (advance D (e 0)) φ' (Fin.tail e)

noncomputable def tracePath (block : α → κ) (active : κ → Prop)
    (h : Equiv.Perm α) (N : ℕ) (e : Fin (Fintype.card α) → Option (α × α)) :
    Fin (N + 1) → Equiv.Perm α :=
  fun i => h.trans (outputAt block active h i.val (Fintype.card α) ∅ (Equiv.refl α) e)

/-- The proposed coupling is the finite pushforward of the explicitly defined
trace law; no abstract existence principle is used to choose the paths. -/
noncomputable def coupling (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (N : ℕ) (h : Equiv.Perm α)
    (p : Fin (N + 1) → Equiv.Perm α) : ℝ :=
  density S h * ∑ e : Fin (Fintype.card α) → Option (α × α),
    if tracePath block active h N e = p then switchingTraceWeight block active S h ∅ _ e
    else 0

noncomputable def terminalWeight (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (h : Equiv.Perm α) (D : Finset α)
    (φ : Equiv.Perm α) (t : ℕ) (g : Equiv.Perm α) : ℝ :=
  ∑ e : Fin t → Option (α × α),
    if h.trans (outputAt block active h 0 t D φ e) = g then
      switchingTraceWeight block active S h D t e else 0

noncomputable def advanceRelabel (block : α → κ) (active : κ → Prop)
    (h : Equiv.Perm α) (D : Finset α) (φ : Equiv.Perm α) :
    Option (α × α) → Equiv.Perm α
  | none => φ
  | some (u, z) =>
      if 0 < (residualInputs block active D).card then correct φ (h u) z else φ

theorem terminalWeight_succ (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (h : Equiv.Perm α) (D : Finset α)
    (φ : Equiv.Perm α) (t : ℕ) (g : Equiv.Perm α) :
    terminalWeight block active S h D φ (t + 1) g =
      ∑ a, transition block active S h D a *
        terminalWeight block active S h (advance D a)
          (advanceRelabel block active h D φ a) t g := by
  calc
    _ = ∑ e : Fin (t + 1) → Option (α × α),
        traceWeight (transition block active S h) advance (t + 1) D e *
          (if h.trans (outputAt block active h 0 (t + 1) D φ e) = g then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp [switchingTraceWeight]
    _ = ∑ a, transition block active S h D a *
        ∑ tail : Fin t → Option (α × α),
          traceWeight (transition block active S h) advance t (advance D a) tail *
            (if h.trans (outputAt block active h 0 (t + 1) D φ (Fin.cons a tail)) = g
              then 1 else 0) := traceWeight_succ_sum _ _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply Finset.sum_congr rfl
      intro tail _
      cases a with
      | none =>
        simp only [outputAt, Fin.cons_zero, Fin.tail_cons, advanceRelabel,
          switchingTraceWeight, mul_ite, mul_one, mul_zero]
        congr 1 <;> exact Subsingleton.elim _ _
      | some p =>
        simp only [outputAt, Fin.cons_zero, Fin.tail_cons, advanceRelabel,
          switchingTraceWeight, mul_ite, mul_one, mul_zero]
        congr 1 <;> exact Subsingleton.elim _ _

theorem mem_remaining (block : α → κ) (active : κ → Prop) (D : Finset α) (x : α) :
    x ∈ remaining block active D ↔ active (block x) ∧ x ∉ D := by
  simp [remaining]

theorem reference_mem_exposed (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h : Equiv.Perm α) (hh : h ∈ S) : h ∈ exposedFiber S D h := by
  simp [exposedFiber, hh]

theorem exposedFiber_eq_of_mem (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h h' : Equiv.Perm α) (hh' : h' ∈ exposedFiber S D h) :
    exposedFiber S D h' = exposedFiber S D h := by
  have he := (Finset.mem_filter.mp hh').2
  ext π
  simp only [exposedFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hπ, hπD⟩
    exact ⟨hπ, fun x hx => (hπD x hx).trans (he x hx)⟩
  · rintro ⟨hπ, hπD⟩
    exact ⟨hπ, fun x hx => (hπD x hx).trans (he x hx).symm⟩

theorem exposedFiber_insert_eq (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h h' : Equiv.Perm α) (hh' : h' ∈ exposedFiber S D h) (u : α) :
    exposedFiber S (insert u D) h' =
      (exposedFiber S D h).filter (fun π => π u = h' u) := by
  rw [← exposedFiber_eq_of_mem S D h h' hh']
  ext π
  simp only [exposedFiber, Finset.mem_filter, Finset.forall_mem_insert]
  tauto

theorem partnerProb_eq_of_mem (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h h' : Equiv.Perm α) (hh' : h' ∈ exposedFiber S D h) (u z : α) :
    partnerProb S D h' u z = partnerProb S D h u z := by
  simp only [partnerProb, exposedFiber_eq_of_mem S D h h' hh']

theorem density_partner_factor (Q : Finset (Equiv.Perm α)) (u y : α)
    (h : Equiv.Perm α) :
    density Q h * (if h u = y then 1 else 0) =
      ((((Q.filter fun π => π u = y).card : ℝ) / Q.card) *
        density (Q.filter fun π => π u = y) h) := by
  by_cases hh : h ∈ Q
  · by_cases hy : h u = y
    · have hq : (Q.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr ⟨h, hh⟩
      have hqy : ((Q.filter fun π => π u = y).card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr ⟨h, Finset.mem_filter.mpr ⟨hh, hy⟩⟩
      simp only [density, hh, hy, if_true, mul_one, Finset.mem_filter, and_self]
      field_simp
    · simp [density, hh, hy]
  · simp [density, hh]

theorem density_partner_disintegration (Q : Finset (Equiv.Perm α)) (u : α)
    (f : Equiv.Perm α → ℝ) :
    (∑ h, density Q h * f h) =
      ∑ y : α, (((Q.filter fun π => π u = y).card : ℝ) / Q.card) *
        ∑ h, density (Q.filter fun π => π u = y) h * f h := by
  calc
    _ = ∑ h, ∑ y : α, (density Q h * (if h u = y then 1 else 0)) * f h := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, mul_one]
    _ = ∑ y : α, ∑ h,
        ((((Q.filter fun π => π u = y).card : ℝ) / Q.card) *
          density (Q.filter fun π => π u = y) h) * f h := by
      rw [Finset.sum_comm]
      simp only [density_partner_factor]
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

theorem density_partner_disintegration_mul (Q : Finset (Equiv.Perm α)) (u : α)
    (c : α → ℝ) (f : Equiv.Perm α → ℝ) :
    (∑ h, density Q h * (c (h u) * f h)) =
      ∑ y : α, ((((Q.filter fun π => π u = y).card : ℝ) / Q.card) * c y) *
        ∑ h, density (Q.filter fun π => π u = y) h * f h := by
  rw [density_partner_disintegration]
  apply Finset.sum_congr rfl
  intro y _
  have hf : (∑ h, density (Q.filter fun π => π u = y) h * (c (h u) * f h)) =
      c y * ∑ h, density (Q.filter fun π => π u = y) h * f h := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : h ∈ Q.filter (fun π => π u = y)
    · rw [(Finset.mem_filter.mp hh).2]
      ring
    · simp [density, hh]
  rw [hf]
  ring

theorem partner_density_sum (Q : Finset (Equiv.Perm α)) (hQ : Q.Nonempty) (u : α) :
    (∑ y : α, (((Q.filter fun π => π u = y).card : ℝ) / Q.card)) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have hc := Finset.card_eq_sum_card_fiberwise (fun π (_ : π ∈ Q) => Finset.mem_univ (π u))
  rw [← hc]
  exact div_self (by exact_mod_cast Finset.card_ne_zero.mpr hQ)

theorem density_correction_mixture (Q : Finset (Equiv.Perm α)) (hQ : Q.Nonempty)
    (u z : α) (r ν : ℝ) (hr : r ≠ 0) (f : Equiv.Perm α → ℝ)
    (havg : ∀ y : α,
      ((((Q.filter fun π => π u = y).card : ℝ) / Q.card) *
        ∑ h, density (Q.filter fun π => π u = y) h * f h) =
      (((Q.filter fun π => π u = y).card : ℝ) / Q.card) * ν) :
    (∑ h, density Q h *
      (((1 - 1 / r) * (if h u = z then 1 else 0) +
        (1 / r) * (1 - (r - 1) *
          (((Q.filter fun π => π u = z).card : ℝ) / Q.card))) * f h)) =
      ν / r := by
  let p (y : α) : ℝ := ((Q.filter fun π => π u = y).card : ℝ) / Q.card
  let c (y : α) : ℝ := (1 - 1 / r) * (if y = z then 1 else 0) +
    (1 / r) * (1 - (r - 1) * p z)
  have hp : (∑ y, p y) = 1 := partner_density_sum Q hQ u
  have hc : (∑ y, p y * c y) = 1 / r := by
    simp only [c, mul_add, Finset.sum_add_distrib]
    have h1 : (∑ y, p y * ((1 - 1 / r) * (if y = z then 1 else 0))) =
        (1 - 1 / r) * p z := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [h1, ← Finset.sum_mul, hp, one_mul]
    field_simp
    ring
  change (∑ h, density Q h * (c (h u) * f h)) = ν / r
  rw [density_partner_disintegration_mul]
  calc
    _ = ∑ y : α, (p y * c y) * ν := by
      apply Finset.sum_congr rfl
      intro y _
      change (p y * c y) * (∑ h, density (Q.filter fun π => π u = y) h * f h) = _
      calc
        _ = c y * (p y * ∑ h, density (Q.filter fun π => π u = y) h * f h) := by ring
        _ = c y * (p y * ν) := by rw [havg]
        _ = _ := by ring
    _ = (1 / r) * ν := by rw [← Finset.sum_mul, hc]
    _ = _ := by ring

theorem exposedFiber_eq_block_of_complete (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S) (D : Finset α)
    (h : Equiv.Perm α) (hh : h ∈ S) (hD : remaining block active D = ∅) :
    exposedFiber S D h = exposedFiber (blockSupport block) D h := by
  ext π
  simp only [exposedFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hπ, hπD⟩
    exact ⟨hsub hπ, hπD⟩
  · rintro ⟨hπ, hπD⟩
    refine ⟨?_, hπD⟩
    apply (hsat π hπ h (hsub hh) ?_).mpr hh
    intro x hx
    apply hπD x
    by_contra hxD
    have hm := (mem_remaining block active D x).mpr ⟨hx, hxD⟩
    simpa [hD] using hm

theorem density_image_equiv (Q : Finset (Equiv.Perm α))
    (e : Equiv.Perm α ≃ Equiv.Perm α) (g : Equiv.Perm α) :
    (∑ h, density Q h * (if e h = g then 1 else 0)) = density (Q.image e) g := by
  have he : g ∈ Q.image e ↔ e.symm g ∈ Q := by
    constructor
    · rintro hmem
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hmem
      simpa using hh
    · intro hh
      exact Finset.mem_image.mpr ⟨e.symm g, hh, e.apply_symm_apply g⟩
  have hc : (Q.image e).card = Q.card := Finset.card_image_iff.mpr e.injective.injOn
  calc
    _ = ∑ k, density Q (e.symm k) * (if k = g then 1 else 0) :=
      Fintype.sum_equiv e _ _ (fun h => by simp)
    _ = density Q (e.symm g) := by simp
    _ = _ := by simp only [density, he, hc]

theorem exposed_block_image_mul (block : α → κ) (D : Finset α)
    (h φ : Equiv.Perm α) (hφ : φ ∈ blockSupport block) :
    (exposedFiber (blockSupport block) D h).image (fun π => φ * π) =
      exposedFiber (blockSupport block) D (h.trans φ) := by
  have hφb := (Finset.mem_filter.mp hφ).2
  have hφi (x : α) : block (φ.symm x) = block x := by
    have hh := hφb (φ.symm x)
    simpa only [φ.apply_symm_apply] using hh.symm
  ext π
  constructor
  · intro hπ
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hπ
    obtain ⟨hρB, hρD⟩ := Finset.mem_filter.mp hρ
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun x => (hφb (ρ x)).trans ((Finset.mem_filter.mp hρB).2 x)⟩
    · intro d hd
      simp only [Equiv.Perm.mul_apply, Equiv.trans_apply, hρD d hd]
  · intro hπ
    obtain ⟨hπB, hπD⟩ := Finset.mem_filter.mp hπ
    apply Finset.mem_image.mpr
    refine ⟨φ⁻¹ * π, ?_, by simp [mul_assoc]⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun x => (hφi (π x)).trans ((Finset.mem_filter.mp hπB).2 x)⟩
    · intro d hd
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.trans_apply,
        φ.symm_apply_apply] using congrArg φ.symm (hπD d hd)

theorem corrected_exposed_insert (block : α → κ) (D : Finset α)
    (h h' φ : Equiv.Perm α) (hh' : h' ∈ exposedFiber (blockSupport block) D h)
    (u z : α) (hu : u ∉ D) (hz : z ∉ D.image h) :
    exposedFiber (blockSupport block) (insert u D) (h'.trans (correct φ (h' u) z)) =
      (exposedFiber (blockSupport block) D (h.trans φ)).filter
        (fun π => π u = φ z) := by
  have hD := (Finset.mem_filter.mp hh').2
  have he (d : α) (hd : d ∈ D) : correct φ (h' u) z (h' d) = φ (h d) := by
    rw [correct_off]
    · rw [hD d hd]
    · intro hh
      exact hu ((h'.injective hh) ▸ hd)
    · intro hh
      apply hz
      exact Finset.mem_image.mpr ⟨d, hd, (hD d hd).symm.trans hh⟩
  ext π
  constructor
  · intro hπ
    obtain ⟨hπB, hπD⟩ := Finset.mem_filter.mp hπ
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨hπB, fun d hd => (hπD d (Finset.mem_insert_of_mem hd)).trans (he d hd)⟩
    · simpa only [Equiv.trans_apply, correct_at_left] using hπD u (Finset.mem_insert_self _ _)
  · intro hπ
    obtain ⟨hπR, hπu⟩ := Finset.mem_filter.mp hπ
    obtain ⟨hπB, hπD⟩ := Finset.mem_filter.mp hπR
    apply Finset.mem_filter.mpr
    refine ⟨hπB, ?_⟩
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simpa only [Equiv.trans_apply, correct_at_left] using hπu
    · exact (hπD d hd).trans (he d hd).symm

theorem nextClass_some_mem (block : α → κ) (active : κ → Prop) (D : Finset α)
    {x : α} (hx : nextClass block active D = some x) :
    x ∈ remaining block active D := by
  unfold nextClass at hx
  split_ifs at hx with h
  cases Option.some.inj hx
  exact h.choose_spec

theorem nextClass_none (block : α → κ) (active : κ → Prop) (D : Finset α) :
    nextClass block active D = none ↔ remaining block active D = ∅ := by
  simp only [nextClass]
  split_ifs with h
  · simp [Finset.Nonempty.ne_empty h]
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

theorem residualInputs_subset_remaining (block : α → κ) (active : κ → Prop)
    (D : Finset α) : residualInputs block active D ⊆ remaining block active D := by
  intro u hu
  unfold residualInputs at hu
  cases hx : nextClass block active D with
  | none => simp [hx] at hu
  | some x =>
    rw [hx] at hu
    obtain ⟨huB, huD⟩ := Finset.mem_sdiff.mp hu
    have hxA := (mem_remaining block active D x).mp (nextClass_some_mem block active D hx)
    have hux := (Finset.mem_filter.mp huB).2
    exact (mem_remaining block active D u).mpr ⟨hux ▸ hxA.1, huD⟩

theorem remaining_insert (block : α → κ) (active : κ → Prop) (D : Finset α) (u : α) :
    remaining block active (insert u D) = (remaining block active D).erase u := by
  ext x
  simp only [mem_remaining, Finset.mem_insert, not_or, Finset.mem_erase]
  tauto

theorem correction_row (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α)
    (hh : h ∈ S) (c : α) {u : α} (hu : u ∈ blockFiber block c \ D) :
    (∑ z ∈ blockFiber block c \ D.image h,
      (1 - (((blockFiber block c \ D).card : ℝ) - 1) * partnerProb S D h u z)) = 1 := by
  have hrow := conditionalPartner_row block S hsub D h hh c hu
  change (∑ z ∈ blockFiber block c \ D.image h, partnerProb S D h u z) = 1 at hrow
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, hrow, mul_one]
  rw [← residual_card_eq block S hsub D h hh c]
  ring

theorem transition_nonneg (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hcap : PartnerCap block active S)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) (e : Option (α × α)) :
    0 ≤ transition block active S h D e := by
  unfold transition
  cases hc : nextClass block active D with
  | none => dsimp only; split_ifs <;> norm_num
  | some c =>
    have hcA := (mem_remaining block active D c).mp (nextClass_some_mem block active D hc)
    cases e with
    | none => exact le_rfl
    | some p =>
      dsimp only
      by_cases hp : p.1 ∈ blockFiber block c \ D ∧ p.2 ∈ blockFiber block c \ D.image h
      · rw [if_pos hp]
        have hr : (1 : ℝ) ≤ (blockFiber block c \ D).card := by
          exact_mod_cast (Finset.card_pos.mpr ⟨p.1, hp.1⟩)
        have hcap' := conditionalPartner_cap block active S hcap D h hh c hcA.1 hp.1 p.2
        change (((blockFiber block c \ D).card : ℝ) - 1) *
          partnerProb S D h p.1 p.2 ≤ 1 at hcap'
        have hrec : 0 ≤ 1 - 1 / ((blockFiber block c \ D).card : ℝ) := by
          apply sub_nonneg.mpr
          exact (div_le_one (by linarith)).mpr hr
        apply mul_nonneg (by positivity)
        apply add_nonneg
        · apply mul_nonneg hrec
          split_ifs <;> norm_num
        · exact mul_nonneg (by positivity) (sub_nonneg.mpr hcap')
      · rw [if_neg hp]

theorem transition_input_sum (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) (c : α)
    (hc : nextClass block active D = some c) (u : α) :
    (∑ z : α, transition block active S h D (some (u, z))) =
      if u ∈ blockFiber block c \ D then 1 / ((blockFiber block c \ D).card : ℝ) else 0 := by
  by_cases hu : u ∈ blockFiber block c \ D
  · simp only [transition, hc, hu, true_and, if_true, Finset.sum_ite_mem, Finset.univ_inter]
    have hy := residual_image_mem block S hsub D h c (exposed_self_mem S D hh) hu
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [correction_row block S hsub D h hh c hu]
    simp [hy]
  · simp [transition, hc, hu]

theorem transition_sum (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) :
    (∑ e, transition block active S h D e) = 1 := by
  cases hc : nextClass block active D with
  | none => simp [transition, hc]
  | some c =>
    have hcA := (mem_remaining block active D c).mp (nextClass_some_mem block active D hc)
    have hcU : c ∈ blockFiber block c \ D := by simp [blockFiber, hcA.2]
    have hr : (0 : ℝ) < (blockFiber block c \ D).card := by
      exact_mod_cast (Finset.card_pos.mpr ⟨c, hcU⟩)
    have hrow (u : α) (hu : u ∈ blockFiber block c \ D) :
        (∑ z ∈ blockFiber block c \ D.image h,
          (1 / ((blockFiber block c \ D).card : ℝ)) *
            ((1 - 1 / ((blockFiber block c \ D).card : ℝ)) *
              (if z = h u then 1 else 0) +
              (1 / ((blockFiber block c \ D).card : ℝ)) *
                (1 - (((blockFiber block c \ D).card : ℝ) - 1) *
                  partnerProb S D h u z))) = 1 / ((blockFiber block c \ D).card : ℝ) := by
      have hy := residual_image_mem block S hsub D h c (exposed_self_mem S D hh) hu
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [correction_row block S hsub D h hh c hu]
      simp [hy]
    simp only [transition, hc, Fintype.sum_option, Fintype.sum_prod_type, zero_add,
      ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem,
      Finset.univ_inter]
    rw [Finset.sum_congr rfl hrow]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_one_div_cancel (ne_of_gt hr)

theorem switchingTraceWeight_nonneg (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hcap : PartnerCap block active S)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) (t : ℕ)
    (e : Fin t → Option (α × α)) :
    0 ≤ switchingTraceWeight block active S h D t e :=
  traceWeight_nonneg _ _ (transition_nonneg block active S hcap h hh) _ _ _

theorem switchingTraceWeight_sum (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) (t : ℕ) :
    (∑ e, switchingTraceWeight block active S h D t e) = 1 :=
  traceWeight_sum _ _ (transition_sum block active S hsub h hh) _ _

theorem terminalWeight_nonneg (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hcap : PartnerCap block active S)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) (φ : Equiv.Perm α)
    (t : ℕ) (g : Equiv.Perm α) :
    0 ≤ terminalWeight block active S h D φ t g := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact switchingTraceWeight_nonneg block active S hcap h hh D t e
  · exact le_rfl

theorem terminalWeight_sum (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α) (φ : Equiv.Perm α) (t : ℕ) :
    (∑ g, terminalWeight block active S h D φ t g) = 1 := by
  unfold terminalWeight
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact switchingTraceWeight_sum block active S hsub h hh D t

theorem coupling_nonneg (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hcap : PartnerCap block active S)
    (N : ℕ) (h : Equiv.Perm α) (p : Fin (N + 1) → Equiv.Perm α) :
    0 ≤ coupling block active S N h p := by
  by_cases hh : h ∈ S
  · apply mul_nonneg (by unfold density; positivity)
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact switchingTraceWeight_nonneg block active S hcap h hh ∅ _ e
    · exact le_rfl
  · simp [coupling, density, hh]

theorem coupling_row (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (N : ℕ) (h : Equiv.Perm α) :
    (∑ p, coupling block active S N h p) = density S h := by
  by_cases hh : h ∈ S
  · simp only [coupling, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [switchingTraceWeight_sum block active S hsub h hh]
    exact mul_one _
  · simp [coupling, density, hh]

theorem residualInputs_card_le (block : α → κ) (active : κ → Prop) (D : Finset α)
    (N : ℕ) (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N) :
    (residualInputs block active D).card ≤ N := by
  unfold residualInputs
  cases hx : nextClass block active D with
  | none => simp
  | some x =>
    have hxA := (mem_remaining block active D x).mp (nextClass_some_mem block active D hx)
    exact (Finset.card_le_card Finset.sdiff_subset).trans (hsize x hxA.1)

theorem outputAt_eq_of_ge (block : α → κ) (active : κ → Prop) (h : Equiv.Perm α)
    (N i : ℕ) (hNi : N ≤ i)
    (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N)
    (t : ℕ) (D : Finset α) (φ : Equiv.Perm α) (e : Fin t → Option (α × α)) :
    outputAt block active h i t D φ e = φ := by
  induction t generalizing D φ with
  | zero => rfl
  | succ t ih =>
    have hh : ¬ i < (residualInputs block active D).card :=
      not_lt_of_ge ((residualInputs_card_le block active D N hsize).trans hNi)
    cases he : e 0 with
    | none => simpa only [outputAt, he] using ih (advance D none) φ (Fin.tail e)
    | some p =>
        simpa only [outputAt, he, if_neg hh] using
          ih (advance D (some p)) φ (Fin.tail e)

theorem tracePath_last (block : α → κ) (active : κ → Prop) (h : Equiv.Perm α)
    (N : ℕ) (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N)
    (e : Fin (Fintype.card α) → Option (α × α)) :
    tracePath block active h N e (Fin.last N) = h := by
  simp only [tracePath, Fin.val_last, outputAt_eq_of_ge block active h N N le_rfl hsize]
  exact Equiv.trans_refl h

theorem coupling_last (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N)
    (h : Equiv.Perm α) (p : Fin (N + 1) → Equiv.Perm α)
    (hp : coupling block active S N h p ≠ 0) : p (Fin.last N) = h := by
  by_contra hh
  have hne (e : Fin (Fintype.card α) → Option (α × α)) :
      tracePath block active h N e ≠ p := by
    intro he
    apply hh
    have hv := congrArg (fun q : Fin (N + 1) → Equiv.Perm α => q (Fin.last N)) he
    rw [tracePath_last block active h N hsize] at hv
    exact hv.symm
  simp only [coupling, if_neg (hne _), Finset.sum_const_zero, mul_zero, ne_eq, not_true_eq_false] at hp

theorem outputAt_none (block : α → κ) (active : κ → Prop) (h : Equiv.Perm α)
    (i t : ℕ) (D : Finset α) (φ : Equiv.Perm α) :
    outputAt block active h i t D φ (fun _ => none) = φ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change outputAt block active h i t D φ (fun _ => none) = φ
    exact ih

theorem terminalWeight_complete (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (h : Equiv.Perm α) (D : Finset α)
    (hD : remaining block active D = ∅) (φ : Equiv.Perm α) (t : ℕ) (g : Equiv.Perm α) :
    terminalWeight block active S h D φ t g = if h.trans φ = g then 1 else 0 := by
  have hc := (nextClass_none block active D).mpr hD
  have hw (e : Fin t → Option (α × α)) :
      switchingTraceWeight block active S h D t e =
        if e = (fun _ => none) then 1 else 0 :=
    traceWeight_deterministic _ _ D none (fun a => by simp [transition, hc]) rfl t e
  unfold terminalWeight
  calc
    _ = ∑ e : Fin t → Option (α × α),
        if e = (fun _ => none) then (if h.trans φ = g then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [hw]
      by_cases he : e = (fun _ => none)
      · subst e
        simp only [outputAt_none, if_true]
      · simp only [if_neg he, ite_self]
    _ = _ := by simp

theorem terminal_uniform_complete (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S) (D : Finset α)
    (h : Equiv.Perm α) (hh : h ∈ S) (hD : remaining block active D = ∅)
    (φ : Equiv.Perm α) (hφ : φ ∈ blockSupport block) (t : ℕ) (g : Equiv.Perm α) :
    (∑ π, density (exposedFiber S D h) π * terminalWeight block active S π D φ t g) =
      density (exposedFiber (blockSupport block) D (h.trans φ)) g := by
  simp only [terminalWeight_complete block active S _ D hD φ t g]
  rw [exposedFiber_eq_block_of_complete block active S hsub hsat D h hh hD]
  have hm := density_image_equiv (exposedFiber (blockSupport block) D h) (Equiv.mulLeft φ) g
  change (∑ π, density (exposedFiber (blockSupport block) D h) π *
      (if φ * π = g then 1 else 0)) =
    density ((exposedFiber (blockSupport block) D h).image (fun π => φ * π)) g at hm
  rw [exposed_block_image_mul block D h φ hφ] at hm
  exact hm

end SwitchingProcess

end FinitePermutationCoupling.RandomOrder

end

section

namespace FinitePermutationCoupling.RandomOrder

open Classical
open scoped BigOperators

variable {α κ : Type*} [Fintype α]

theorem block_trans_mem (block : α → κ) (h φ : Equiv.Perm α)
    (hh : h ∈ blockSupport block) (hφ : φ ∈ blockSupport block) :
    h.trans φ ∈ blockSupport block := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, fun x =>
    ((Finset.mem_filter.mp hφ).2 (h x)).trans ((Finset.mem_filter.mp hh).2 x)⟩

theorem correct_block_mem (block : α → κ) (φ : Equiv.Perm α)
    (hφ : φ ∈ blockSupport block) (y z : α) (hyz : block y = block z) :
    correct φ y z ∈ blockSupport block := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro x
  exact ((Finset.mem_filter.mp hφ).2 (Equiv.swap y z x)).trans
    (block_swap_apply block hyz x)

theorem corrected_residual_mem_iff (block : α → κ) (D : Finset α)
    (h φ : Equiv.Perm α) (hφ : φ ∈ blockSupport block) (u z : α) :
    φ z ∈ blockFiber block u \ D.image (h.trans φ) ↔
      z ∈ blockFiber block u \ D.image h := by
  have hb := (Finset.mem_filter.mp hφ).2
  constructor
  · intro hz
    obtain ⟨hzB, hzD⟩ := Finset.mem_sdiff.mp hz
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (hb z).symm.trans ((Finset.mem_filter.mp hzB).2)⟩
    · rintro hzm
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hzm
      exact hzD (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  · intro hz
    obtain ⟨hzB, hzD⟩ := Finset.mem_sdiff.mp hz
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (hb z).trans ((Finset.mem_filter.mp hzB).2)⟩
    · rintro hzm
      obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hzm
      exact hzD (Finset.mem_image.mpr ⟨d, hd, φ.injective heq⟩)

theorem corrected_extension_mixture (block : α → κ) (D : Finset α)
    (h φ : Equiv.Perm α) (hh : h ∈ blockSupport block) (hφ : φ ∈ blockSupport block)
    (u : α) (hu : u ∉ D) (g : Equiv.Perm α) :
    (∑ z ∈ blockFiber block u \ D.image h,
      (1 / ((blockFiber block u \ D).card : ℝ)) *
        density ((exposedFiber (blockSupport block) D (h.trans φ)).filter
          (fun π => π u = φ z)) g) =
      density (exposedFiber (blockSupport block) D (h.trans φ)) g := by
  let R := exposedFiber (blockSupport block) D (h.trans φ)
  have hR : R.Nonempty :=
    ⟨h.trans φ, exposed_self_mem _ D (block_trans_mem block h φ hh hφ)⟩
  have hcard := residual_card_eq block (blockSupport block) (by intro _ h; exact h)
    D (h.trans φ) (block_trans_mem block h φ hh hφ) u
  have hext (z : α) (hz : z ∈ blockFiber block u \ D.image h) :
      density R g * (if g u = φ z then 1 else 0) =
        (1 / ((blockFiber block u \ D).card : ℝ)) *
          density (R.filter fun π => π u = φ z) g := by
    have he := exposed_block_density_extension block D (h.trans φ) hu hR
      ((corrected_residual_mem_iff block D h φ hφ u z).mpr hz) g
    simpa only [← hcard] using he
  change (∑ z ∈ blockFiber block u \ D.image h,
    (1 / ((blockFiber block u \ D).card : ℝ)) *
      density (R.filter fun π => π u = φ z) g) = density R g
  rw [Finset.sum_congr rfl (fun z hz => (hext z hz).symm)]
  by_cases hg : g ∈ R
  · have hy := exposed_block_image_mem block D (h.trans φ) g hu hg
    have hz : φ.symm (g u) ∈ blockFiber block u \ D.image h := by
      apply (corrected_residual_mem_iff block D h φ hφ u _).mp
      simpa only [φ.apply_symm_apply] using hy
    have heq (z : α) : g u = φ z ↔ z = φ.symm (g u) := by
      constructor
      · intro he
        exact ((congrArg φ.symm he).trans (φ.symm_apply_apply z)).symm
      · intro he
        rw [he, φ.apply_symm_apply]
    simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hz, if_true]
  · simp [density, hg]

theorem terminal_tail_average (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (D : Finset α) (h φ : Equiv.Perm α) (u z : α) (hu : u ∉ D)
    (hz : z ∈ blockFiber block u \ D.image h) (t : ℕ) (g : Equiv.Perm α)
    (hIH : ∀ h' ∈ exposedFiber S D h,
      (∑ π, density (exposedFiber S (insert u D) h') π *
        terminalWeight block active S π (insert u D) (correct φ (h' u) z) t g) =
      density (exposedFiber (blockSupport block) (insert u D)
        (h'.trans (correct φ (h' u) z))) g) (y : α) :
    (((((exposedFiber S D h).filter fun π => π u = y).card : ℝ) /
      (exposedFiber S D h).card) *
        ∑ π, density ((exposedFiber S D h).filter fun π => π u = y) π *
          terminalWeight block active S π (insert u D) (correct φ (π u) z) t g) =
    (((((exposedFiber S D h).filter fun π => π u = y).card : ℝ) /
      (exposedFiber S D h).card) *
        density ((exposedFiber (blockSupport block) D (h.trans φ)).filter
          (fun π => π u = φ z)) g) := by
  let Qy := (exposedFiber S D h).filter (fun π => π u = y)
  by_cases hQy : Qy.Nonempty
  · obtain ⟨h', hh'⟩ := hQy
    obtain ⟨hh'Q, hh'y⟩ := Finset.mem_filter.mp hh'
    have hI := hIH h' hh'Q
    rw [exposedFiber_insert_eq S D h h' hh'Q u] at hI
    rw [corrected_exposed_insert block D h h' φ
      (exposed_subset_block block S hsub D h hh'Q) u z hu (Finset.mem_sdiff.mp hz).2] at hI
    rw [hh'y] at hI
    have htail :
        (∑ π, density Qy π * terminalWeight block active S π (insert u D)
          (correct φ (π u) z) t g) =
          density ((exposedFiber (blockSupport block) D (h.trans φ)).filter
            (fun π => π u = φ z)) g := by
      calc
        _ = ∑ π, density Qy π * terminalWeight block active S π (insert u D)
            (correct φ y z) t g := by
          apply Finset.sum_congr rfl
          intro π _
          by_cases hπ : π ∈ Qy
          · rw [(Finset.mem_filter.mp hπ).2]
          · simp [density, hπ]
        _ = _ := hI
    exact congrArg (fun a : ℝ => ((Qy.card : ℝ) / (exposedFiber S D h).card) * a) htail
  · have hzero : Qy = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQy
    change ((Qy.card : ℝ) / _) * _ = ((Qy.card : ℝ) / _) * _
    simp only [hzero, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul]

theorem exposed_image_eq (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h π : Equiv.Perm α) (hπ : π ∈ exposedFiber S D h) :
    D.image π = D.image h := by
  exact Finset.image_congr (Finset.mem_filter.mp hπ).2

theorem terminal_edge_average (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (D : Finset α) (h : Equiv.Perm α) (hh : h ∈ S) (φ : Equiv.Perm α)
    (c : α) (hc : nextClass block active D = some c)
    (u z : α) (hu : u ∈ blockFiber block c \ D)
    (hz : z ∈ blockFiber block c \ D.image h) (t : ℕ) (g : Equiv.Perm α)
    (hIH : ∀ h' ∈ exposedFiber S D h,
      (∑ π, density (exposedFiber S (insert u D) h') π *
        terminalWeight block active S π (insert u D) (correct φ (h' u) z) t g) =
      density (exposedFiber (blockSupport block) (insert u D)
        (h'.trans (correct φ (h' u) z))) g) :
    (∑ π, density (exposedFiber S D h) π *
      (transition block active S π D (some (u, z)) *
        terminalWeight block active S π (insert u D) (correct φ (π u) z) t g)) =
      (1 / ((blockFiber block c \ D).card : ℝ)) *
        (density ((exposedFiber (blockSupport block) D (h.trans φ)).filter
          (fun π => π u = φ z)) g / ((blockFiber block c \ D).card : ℝ)) := by
  let Q := exposedFiber S D h
  let r : ℝ := (blockFiber block c \ D).card
  let f (π : Equiv.Perm α) :=
    terminalWeight block active S π (insert u D) (correct φ (π u) z) t g
  let ν := density ((exposedFiber (blockSupport block) D (h.trans φ)).filter
    (fun π => π u = φ z)) g
  have hQ : Q.Nonempty := ⟨h, exposed_self_mem S D hh⟩
  have hr : r ≠ 0 := by
    change ((blockFiber block c \ D).card : ℝ) ≠ 0
    exact_mod_cast Finset.card_ne_zero.mpr ⟨u, hu⟩
  have huc := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
  have hC : blockFiber block u = blockFiber block c := by
    ext x
    simp [blockFiber, huc]
  have hz' : z ∈ blockFiber block u \ D.image h := by simpa only [hC] using hz
  have havg := terminal_tail_average block active S hsub D h φ u z
    (Finset.mem_sdiff.mp hu).2 hz' t g hIH
  have hm := density_correction_mixture Q hQ u z r ν hr f havg
  calc
    _ = (1 / r) * (∑ π, density Q π *
        (((1 - 1 / r) * (if π u = z then 1 else 0) +
          (1 / r) * (1 - (r - 1) *
            (((Q.filter fun ρ => ρ u = z).card : ℝ) / Q.card))) * f π)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      by_cases hπ : π ∈ Q
      · have hi := exposed_image_eq S D h π hπ
        simp only [transition, hc, hi, hu, hz, and_self, if_true]
        rw [partnerProb_eq_of_mem S D h π hπ]
        simp only [partnerProb]
        change density Q π * ((1 / r *
          ((1 - 1 / r) * (if z = π u then 1 else 0) +
            (1 / r) * (1 - (r - 1) * (((Q.filter fun ρ => ρ u = z).card : ℝ) / Q.card)))) *
              f π) = _
        rw [eq_comm (a := z) (b := π u)]
        ring
      · have hπ' : π ∉ exposedFiber S D h := hπ
        simp only [density, hπ, hπ', if_false, zero_mul, mul_zero]
    _ = (1 / r) * (ν / r) := by rw [hm]
    _ = _ := rfl

theorem terminal_uniform_step (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (D : Finset α) (h : Equiv.Perm α) (hh : h ∈ S) (φ : Equiv.Perm α)
    (hφ : φ ∈ blockSupport block) (c : α) (hc : nextClass block active D = some c)
    (t : ℕ) (g : Equiv.Perm α)
    (hIH : ∀ u ∈ blockFiber block c \ D, ∀ z ∈ blockFiber block c \ D.image h,
      ∀ h' ∈ exposedFiber S D h,
      (∑ π, density (exposedFiber S (insert u D) h') π *
        terminalWeight block active S π (insert u D) (correct φ (h' u) z) t g) =
      density (exposedFiber (blockSupport block) (insert u D)
        (h'.trans (correct φ (h' u) z))) g) :
    (∑ π, density (exposedFiber S D h) π * terminalWeight block active S π D φ (t + 1) g) =
      density (exposedFiber (blockSupport block) D (h.trans φ)) g := by
  let U := blockFiber block c \ D
  let V := blockFiber block c \ D.image h
  let Q := exposedFiber S D h
  let R := exposedFiber (blockSupport block) D (h.trans φ)
  let F (u z : α) : ℝ := ∑ π, density Q π *
    (transition block active S π D (some (u, z)) *
      terminalWeight block active S π (advance D (some (u, z)))
        (advanceRelabel block active π D φ (some (u, z))) t g)
  have hcA := (mem_remaining block active D c).mp (nextClass_some_mem block active D hc)
  have hcU : c ∈ U := by simp [U, blockFiber, hcA.2]
  have hrNat : 0 < U.card := Finset.card_pos.mpr ⟨c, hcU⟩
  have hr : (U.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hrNat
  have hnone (π : Equiv.Perm α) : transition block active S π D none = 0 := by
    simp [transition, hc]
  have htotal :
      (∑ π, density Q π * terminalWeight block active S π D φ (t + 1) g) =
        ∑ u : α, ∑ z : α, F u z := by
    simp only [terminalWeight_succ, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Fintype.sum_option, Fintype.sum_prod_type, hnone, zero_mul, mul_zero,
      Finset.sum_const_zero, zero_add]
    rfl
  have hzero (u z : α) (hz : ¬(u ∈ U ∧ z ∈ V)) : F u z = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    by_cases hπ : π ∈ Q
    · have hi := exposed_image_eq S D h π hπ
      simp only [transition, hc, hi]
      change density Q π * ((if u ∈ U ∧ z ∈ V then _ else 0) * _) = 0
      rw [if_neg hz, zero_mul, mul_zero]
    · simp only [density, hπ, if_false, zero_mul]
  have hF (u : α) (hu : u ∈ U) (z : α) (hz : z ∈ V) :
      F u z = (1 / (U.card : ℝ)) *
        (density (R.filter fun π => π u = φ z) g / (U.card : ℝ)) := by
    have hrel (π : Equiv.Perm α) :
        advanceRelabel block active π D φ (some (u, z)) = correct φ (π u) z := by
      simp only [advanceRelabel, residualInputs, hc]
      exact if_pos hrNat
    simp only [F, advance, hrel]
    exact terminal_edge_average block active S hsub D h hh φ c hc u z hu hz t g
      (hIH u hu z hz)
  have hrow (u : α) (hu : u ∈ U) :
      (∑ z ∈ V, F u z) = (1 / (U.card : ℝ)) * density R g := by
    rw [Finset.sum_congr rfl (fun z hz => hF u hu z hz), ← Finset.mul_sum]
    have huc := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
    have hC : blockFiber block u = blockFiber block c := by ext x; simp [blockFiber, huc]
    have hm := corrected_extension_mixture block D h φ (hsub hh) hφ u
      (Finset.mem_sdiff.mp hu).2 g
    rw [hC] at hm
    have hm' : (∑ z ∈ V, density (R.filter fun π => π u = φ z) g / (U.card : ℝ)) =
        density R g := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hm
    rw [hm']
  calc
    _ = ∑ u : α, ∑ z : α, F u z := htotal
    _ = ∑ u : α, ∑ z : α, if u ∈ U ∧ z ∈ V then F u z else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : u ∈ U ∧ z ∈ V
      · rw [if_pos hz]
      · rw [if_neg hz, hzero u z hz]
    _ = ∑ u ∈ U, ∑ z ∈ V, F u z := by
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ u ∈ U, (1 / (U.card : ℝ)) * density R g := Finset.sum_congr rfl hrow
    _ = density R g := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp

end FinitePermutationCoupling.RandomOrder

end

section

namespace FinitePermutationCoupling.RandomOrder

open Classical
open scoped BigOperators

variable {α κ : Type*} [Fintype α]

theorem terminal_uniform (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S) (t : ℕ) (D : Finset α)
    (h : Equiv.Perm α) (hh : h ∈ S) (φ : Equiv.Perm α)
    (hφ : φ ∈ blockSupport block) (ht : (remaining block active D).card ≤ t)
    (g : Equiv.Perm α) :
    (∑ π, density (exposedFiber S D h) π * terminalWeight block active S π D φ t g) =
      density (exposedFiber (blockSupport block) D (h.trans φ)) g := by
  induction t generalizing D h φ with
  | zero =>
    have hD : remaining block active D = ∅ := Finset.card_eq_zero.mp (by omega)
    exact terminal_uniform_complete block active S hsub hsat D h hh hD φ hφ 0 g
  | succ t ih =>
    by_cases hD : remaining block active D = ∅
    · exact terminal_uniform_complete block active S hsub hsat D h hh hD φ hφ (t + 1) g
    · cases hc : nextClass block active D with
      | none => exact (hD ((nextClass_none block active D).mp hc)).elim
      | some c =>
        apply terminal_uniform_step block active S hsub D h hh φ hφ c hc t g
        intro u hu z hz h' hh'
        have huR : u ∈ remaining block active D := by
          apply residualInputs_subset_remaining block active D
          simpa only [residualInputs, hc] using hu
        have hcard : (remaining block active (insert u D)).card ≤ t := by
          rw [remaining_insert, Finset.card_erase_of_mem huR]
          omega
        have hh'S : h' ∈ S := (Finset.mem_filter.mp hh').1
        have hhu : block (h' u) = block u := (Finset.mem_filter.mp (hsub hh'S)).2 u
        have huc : block u = block c := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
        have hzc : block z = block c := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
        have hcorrect : correct φ (h' u) z ∈ blockSupport block :=
          correct_block_mem block φ hφ _ _ (hhu.trans (huc.trans hzc.symm))
        exact ih (insert u D) h' hh'S (correct φ (h' u) z) hcorrect hcard

theorem terminal_uniform_empty (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S) (hS : S.Nonempty)
    (t : ℕ) (ht : Fintype.card α ≤ t) (g : Equiv.Perm α) :
    (∑ π, density S π * terminalWeight block active S π ∅ (Equiv.refl α) t g) =
      density (blockSupport block) g := by
  obtain ⟨h, hh⟩ := hS
  have hφ : Equiv.refl α ∈ blockSupport block := by simp [blockSupport]
  have hcard : (remaining block active ∅).card ≤ t :=
    (Finset.card_le_univ (remaining block active ∅)).trans ht
  simpa [exposedFiber] using
    terminal_uniform block active S hsub hsat t ∅ h hh (Equiv.refl α) hφ hcard g

theorem terminal_uniform_initial (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S) (hS : S.Nonempty) (g : Equiv.Perm α) :
    (∑ π, density S π * terminalWeight block active S π ∅ (Equiv.refl α) (Fintype.card α) g) =
      density (blockSupport block) g :=
  terminal_uniform_empty block active S hsub hsat hS _ le_rfl g

end FinitePermutationCoupling.RandomOrder

end

section

namespace WeldedPath.CouplingHarmonic

theorem reciprocal_sum_eq_harmonic (m : ℕ) :
    (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) = (harmonic m : ℝ) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, one_div]

theorem reciprocal_sum_le (n m : ℕ) (hm : 1 ≤ m) (hhi : m ≤ 2 ^ n) :
    (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤ (n : ℝ) + 1 := by
  rw [reciprocal_sum_eq_harmonic]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpow : (m : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hhi
  have hlog : Real.log (m : ℝ) ≤ (n : ℝ) := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log hmpos hpow
      _ = (n : ℝ) * Real.log 2 := Real.log_pow 2 n
      _ ≤ (n : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      _ = (n : ℝ) := mul_one _
  have hh := harmonic_le_one_add_log m
  linarith

theorem harmonic_error_le (n m : ℕ) (hn : 1 ≤ n)
    (hlo : 2 ^ (n - 1) ≤ m) (hhi : m ≤ 2 ^ n) :
    (2 / (m : ℝ)) * (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤
      8 * (n : ℝ) / (2 : ℝ) ^ n := by
  have hm : 1 ≤ m := (Nat.one_le_pow (n - 1) 2 (by omega)).trans hlo
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hN : (2 : ℝ) ^ n ≤ 2 * (m : ℝ) := by
    have hn' : n = (n - 1) + 1 := by omega
    have hlo' : (2 : ℝ) ^ (n - 1) ≤ (m : ℝ) := by exact_mod_cast hlo
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by rw [← pow_succ, ← hn']
      _ ≤ (m : ℝ) * 2 := mul_le_mul_of_nonneg_right hlo' (by norm_num)
      _ = 2 * (m : ℝ) := mul_comm _ _
  have hrecip : 2 / (m : ℝ) ≤ 4 / (2 : ℝ) ^ n := by
    apply (div_le_div_iff₀ hmpos hNpos).mpr
    linarith
  have hsum : (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤ 2 * (n : ℝ) := by
    have hh := reciprocal_sum_le n m hm hhi
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    _ ≤ (2 / (m : ℝ)) * (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (4 / (2 : ℝ) ^ n) * (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hrecip (by positivity)
    _ = _ := by ring

theorem dyadic_certificate_sum_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ i : Fin (2 ^ n), 4 / ((2 : ℝ) ^ n * ((i : ℝ) + 1))) ≤
      16 * (n : ℝ) / (2 : ℝ) ^ n := by
  have hlo : (2 : ℕ) ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
  have hh := harmonic_error_le n (2 ^ n) hn hlo le_rfl
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hh
  calc
    _ = ∑ r ∈ Finset.range (2 ^ n), 4 / ((2 : ℝ) ^ n * ((r : ℝ) + 1)) :=
      (Finset.sum_range _).symm
    _ = 2 * ((2 / (2 : ℝ) ^ n) *
        (∑ r ∈ Finset.range (2 ^ n), 1 / ((r : ℝ) + 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [div_mul_eq_div_div]
      ring
    _ ≤ 2 * (8 * (n : ℝ) / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

theorem truncated_harmonic_error_le (n m : ℕ) (hn : 1 ≤ n)
    (hlo : 2 ^ (n - 1) ≤ m) (hhi : m ≤ 2 ^ n) :
    (2 / (m : ℝ)) * (∑ r ∈ Finset.Icc 2 m, 1 / (r : ℝ)) ≤
      8 * (n : ℝ) / (2 : ℝ) ^ n := by
  apply le_trans _ (harmonic_error_le n m hn hlo hhi)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [reciprocal_sum_eq_harmonic]
  have hsum : (∑ r ∈ Finset.Icc 2 m, 1 / (r : ℝ)) ≤
      ∑ r ∈ Finset.Icc 1 m, 1 / (r : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc (by omega) le_rfl
    · intro r _ _; positivity
  exact hsum.trans_eq (by simp [harmonic_eq_sum_Icc, Rat.cast_sum, one_div])

theorem small_n_error_ge_one (n cutoff : ℕ) (hn : 1 ≤ n) (hsmall : n ≤ cutoff) :
    1 ≤ (2 : ℝ) ^ cutoff * (n : ℝ) / (2 : ℝ) ^ n := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mpr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ cutoff := by gcongr; norm_num
  calc
    1 * (2 : ℝ) ^ n = (2 : ℝ) ^ n := one_mul _
    _ ≤ (2 : ℝ) ^ cutoff := hp
    _ ≤ (2 : ℝ) ^ cutoff * (n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hn'
        (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) cutoff))

section Independent

variable {α β X : Type*} [Fintype α] [Fintype β]

theorem product_row (μ : α → ℝ) (ν : β → ℝ) (hν : ∑ b, ν b = 1) (a : α) :
    (∑ b, μ a * ν b) = μ a := by rw [← Finset.mul_sum, hν, mul_one]

theorem product_col (μ : α → ℝ) (ν : β → ℝ) (hμ : ∑ a, μ a = 1) (b : β) :
    (∑ a, μ a * ν b) = ν b := by rw [← Finset.sum_mul, hμ, one_mul]

theorem product_disagreement_le (μ : α → ℝ) (ν : β → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (htotal : ∑ b, ν b = 1)
    (P : α → β → X → Prop) [∀ a b, DecidablePred (P a b)] (a : α) (x : X) :
    (∑ b, if P a b x then μ a * ν b else 0) ≤ μ a := by
  calc
    _ ≤ ∑ b, μ a * ν b := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hμ a) (hν b)
    _ = μ a := product_row μ ν htotal a

end Independent

end WeldedPath.CouplingHarmonic

end

section

namespace FinitePermutationCoupling.RandomOrder

open Classical
open scoped BigOperators

noncomputable def errorCost (m : ℕ) : ℝ :=
  2 * (∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1)) / m

theorem errorCost_zero : errorCost 0 = 0 := by simp [errorCost]

theorem errorCost_nonneg (m : ℕ) : 0 ≤ errorCost m := by
  unfold errorCost
  positivity

theorem errorCost_succ (m : ℕ) :
    errorCost (m + 1) = 2 / ((m : ℝ) + 1) ^ 2 +
      ((m : ℝ) / (m + 1)) * errorCost m := by
  by_cases hm : m = 0
  · subst m; norm_num [errorCost]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [errorCost, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem errorCost_step (m : ℕ) (hm : 0 < m) :
    errorCost m = 2 / (m : ℝ) ^ 2 +
      (((m - 1 : ℕ) : ℝ) / m) * errorCost (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    using errorCost_succ k

theorem errorCost_eq_harmonic (m : ℕ) : errorCost m = 2 * (harmonic m : ℝ) / m := by
  rw [errorCost, WeldedPath.CouplingHarmonic.reciprocal_sum_eq_harmonic]

variable {α κ : Type*} [Fintype α]

noncomputable def errorPotential (block : α → κ) (active : κ → Prop)
    (D : Finset α) (x : α) : ℝ :=
  if active (block x) ∧ x ∉ D then errorCost (blockFiber block x \ D).card else 0

theorem errorPotential_nonneg (block : α → κ) (active : κ → Prop)
    (D : Finset α) (x : α) : 0 ≤ errorPotential block active D x := by
  unfold errorPotential
  split_ifs
  · exact errorCost_nonneg _
  · exact le_rfl

theorem correction_col (block : α → κ) (S : Finset (Equiv.Perm α))
    (hsub : S ⊆ blockSupport block) (D : Finset α) (h : Equiv.Perm α)
    (hh : h ∈ S) (c : α) {z : α} (hz : z ∈ blockFiber block c \ D.image h) :
    (∑ u ∈ blockFiber block c \ D,
      (1 - (((blockFiber block c \ D).card : ℝ) - 1) * partnerProb S D h u z)) = 1 := by
  have hcol := conditionalPartner_col block S hsub D h hh c hz
  change (∑ u ∈ blockFiber block c \ D, partnerProb S D h u z) = 1 at hcol
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, hcol, mul_one]
  ring

theorem rectangular_touch_mass (U V : Finset α) (h : Equiv.Perm α)
    (hUV : ∀ x, h x ∈ V ↔ x ∈ U) (T : α → α → ℝ)
    (hT : ∀ u ∈ U, ∀ z ∈ V, 0 ≤ T u z)
    (hrow : ∀ u ∈ U, (∑ z ∈ V, T u z) = 1)
    (hcol : ∀ z ∈ V, (∑ u ∈ U, T u z) = 1) (x : α) :
    (∑ u ∈ U, ∑ z ∈ V, if Equiv.swap (h u) z (h x) ≠ h x then T u z else 0) ≤
      if x ∈ U then 2 else 0 := by
  have hp (u : α) (hu : u ∈ U) (z : α) (hz : z ∈ V) :
      (if Equiv.swap (h u) z (h x) ≠ h x then T u z else 0) ≤
        (if u = x then T u z else 0) + (if z = h x then T u z else 0) := by
    by_cases hu' : u = x
    · simp only [if_pos hu']
      split_ifs <;> linarith [hT u hu z hz]
    · by_cases hz' : z = h x
      · simp only [if_neg hu', if_pos hz', zero_add]
        split_ifs <;> linarith [hT u hu z hz]
      · have hfix := Equiv.swap_apply_of_ne_of_ne
          (fun he => hu' (h.injective he.symm)) (Ne.symm hz')
        simp only [hfix, ne_eq, not_true_eq_false, if_false, if_neg hu', if_neg hz', add_zero,
          le_refl]
  have hr : (∑ u ∈ U, ∑ z ∈ V, if u = x then T u z else 0) = if x ∈ U then 1 else 0 := by
    calc
      _ = ∑ u ∈ U, if u = x then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hu' : u = x
        · subst u; simpa using hrow x hu
        · simp [hu']
      _ = _ := by simp
  have hc : (∑ u ∈ U, ∑ z ∈ V, if z = h x then T u z else 0) = if x ∈ U then 1 else 0 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ z ∈ V, if z = h x then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hz' : z = h x
        · subst z; simpa using hcol (h x) hz
        · simp [hz']
      _ = _ := by simp [hUV]
  calc
    _ ≤ ∑ u ∈ U, ∑ z ∈ V,
        ((if u = x then T u z else 0) + (if z = h x then T u z else 0)) :=
      Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun z hz => hp u hu z hz
    _ = _ := by simp only [Finset.sum_add_distrib, hr, hc]; split_ifs <;> norm_num

theorem rectangular_correction_touch (U V : Finset α) (h φ : Equiv.Perm α)
    (hUV : ∀ x, h x ∈ V ↔ x ∈ U) (T : α → α → ℝ)
    (hT : ∀ u ∈ U, ∀ z ∈ V, 0 ≤ T u z)
    (hrow : ∀ u ∈ U, (∑ z ∈ V, T u z) = 1)
    (hcol : ∀ z ∈ V, (∑ u ∈ U, T u z) = 1) (r : ℝ) (hr : 0 < r) (x : α) :
    (∑ u ∈ U, ∑ z ∈ V,
      if correct φ (h u) z (h x) ≠ φ (h x) then
        (1 / r) * ((1 - 1 / r) * (if z = h u then 1 else 0) + (1 / r) * T u z)
      else 0) ≤ if x ∈ U then 2 / r ^ 2 else 0 := by
  have he (u z : α) :
      (if correct φ (h u) z (h x) ≠ φ (h x) then
        (1 / r) * ((1 - 1 / r) * (if z = h u then 1 else 0) + (1 / r) * T u z)
      else 0) = (1 / r ^ 2) *
        (if Equiv.swap (h u) z (h x) ≠ h x then T u z else 0) := by
    simp only [correct, Equiv.trans_apply, φ.injective.ne_iff]
    by_cases hh : Equiv.swap (h u) z (h x) ≠ h x
    · have hzu : z ≠ h u := by
        intro he; subst z; simp at hh
      simp only [if_pos hh, if_neg hzu, mul_zero, zero_add]
      field_simp
    · simp [hh]
  simp only [he, ← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (rectangular_touch_mass U V h hUV T hT hrow hcol x)
    (show 0 ≤ 1 / r ^ 2 by positivity)
  simpa only [mul_ite, mul_zero, mul_comm (1 / r ^ 2) 2, mul_one_div] using hh

theorem blockFiber_eq_of_block_eq (block : α → κ) {x c : α} (hxc : block x = block c) :
    blockFiber block x = blockFiber block c := by
  ext z
  simp [blockFiber, hxc]

theorem errorPotential_insert (block : α → κ) (active : κ → Prop) (D : Finset α)
    (c : α) (hc : active (block c)) {u : α} (hu : u ∈ blockFiber block c \ D) (x : α) :
    errorPotential block active (insert u D) x =
      if x ∈ blockFiber block c \ D then
        (if u = x then 0 else errorCost ((blockFiber block c \ D).card - 1))
      else errorPotential block active D x := by
  have hub := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).2
  by_cases hx : x ∈ blockFiber block c \ D
  · have hxb := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2
    have hxa : active (block x) := hxb.symm ▸ hc
    have hxD := (Finset.mem_sdiff.mp hx).2
    rw [if_pos hx]
    by_cases hux : u = x
    · subst u
      simp [errorPotential]
    · have hxi : x ∉ insert u D := by simp [hxD, Ne.symm hux]
      rw [if_neg hux, errorPotential, if_pos ⟨hxa, hxi⟩,
        blockFiber_eq_of_block_eq block hxb, Finset.sdiff_insert, Finset.card_erase_of_mem hu]
  · rw [if_neg hx]
    by_cases ha : active (block x) ∧ x ∉ D
    · have hxb : block x ≠ block c := by
        intro heq
        apply hx
        simp [blockFiber, heq, ha.2]
      have hux : u ≠ x := fun heq => hxb (heq ▸ hub)
      have huC : u ∉ blockFiber block x := by
        simp only [blockFiber, Finset.mem_filter, Finset.mem_univ, true_and]
        intro heq
        exact hxb (heq.symm.trans hub)
      have hxi : x ∉ insert u D := by simp [ha.2, Ne.symm hux]
      have hai : active (block x) ∧ x ∉ insert u D := ⟨ha.1, hxi⟩
      simp only [errorPotential, if_pos ha, if_pos hai,
        Finset.sdiff_insert_of_notMem huC]
    · have hai : ¬ (active (block x) ∧ x ∉ insert u D) := by
        rintro ⟨hxa, hxi⟩
        apply ha
        exact ⟨hxa, fun hxD => hxi (Finset.mem_insert_of_mem hxD)⟩
      simp only [errorPotential, if_neg ha, if_neg hai]

theorem transition_potential_sum (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (h : Equiv.Perm α) (hh : h ∈ S) (D : Finset α)
    (c : α) (hc : nextClass block active D = some c) (x : α) :
    (∑ e, transition block active S h D e * errorPotential block active (advance D e) x) =
      if x ∈ blockFiber block c \ D then
        (((blockFiber block c \ D).card - 1 : ℕ) : ℝ) /
          ((blockFiber block c \ D).card : ℝ) * errorCost ((blockFiber block c \ D).card - 1)
      else errorPotential block active D x := by
  have hcA := (mem_remaining block active D c).mp (nextClass_some_mem block active D hc)
  have hcU : c ∈ blockFiber block c \ D := by simp [blockFiber, hcA.2]
  have hr : ((blockFiber block c \ D).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨c, hcU⟩
  have he : (∑ e, transition block active S h D e * errorPotential block active (advance D e) x) =
      (1 / ((blockFiber block c \ D).card : ℝ)) *
        ∑ u ∈ blockFiber block c \ D, errorPotential block active (insert u D) x := by
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have hn : transition block active S h D none = 0 := by simp [transition, hc]
    simp only [hn, zero_mul, zero_add, advance]
    simp only [← Finset.sum_mul, transition_input_sum block active S hsub h hh D c hc,
      ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  rw [he]
  by_cases hx : x ∈ blockFiber block c \ D
  · rw [if_pos hx]
    have hsum : (∑ u ∈ blockFiber block c \ D, errorPotential block active (insert u D) x) =
        (((blockFiber block c \ D).card - 1 : ℕ) : ℝ) *
          errorCost ((blockFiber block c \ D).card - 1) := by
      calc
        _ = ∑ u ∈ blockFiber block c \ D,
            if u ≠ x then errorCost ((blockFiber block c \ D).card - 1) else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [errorPotential_insert block active D c hcA.1 hu x, if_pos hx]
          split_ifs <;> simp_all
        _ = _ := by
          rw [← Finset.sum_filter]
          simp [Finset.filter_ne', Finset.card_erase_of_mem hx]
    rw [hsum]
    ring
  · rw [if_neg hx]
    have hsum : (∑ u ∈ blockFiber block c \ D, errorPotential block active (insert u D) x) =
        ((blockFiber block c \ D).card : ℝ) * errorPotential block active D x := by
      calc
        _ = ∑ _u ∈ blockFiber block c \ D, errorPotential block active D x :=
          Finset.sum_congr rfl fun u hu => by
            rw [errorPotential_insert block active D c hcA.1 hu x, if_neg hx]
        _ = _ := by simp
    rw [hsum]
    field_simp

theorem transition_touch_sum (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hcap : PartnerCap block active S) (h : Equiv.Perm α) (hh : h ∈ S)
    (D : Finset α) (φ : Equiv.Perm α) (c : α)
    (hc : nextClass block active D = some c) (x : α) :
    (∑ e, if advanceRelabel block active h D φ e (h x) ≠ φ (h x) then
      transition block active S h D e else 0) ≤
      if x ∈ blockFiber block c \ D then
        2 / ((blockFiber block c \ D).card : ℝ) ^ 2 else 0 := by
  have hcA := (mem_remaining block active D c).mp (nextClass_some_mem block active D hc)
  have hcU : c ∈ blockFiber block c \ D := by simp [blockFiber, hcA.2]
  have hrN : 0 < (blockFiber block c \ D).card := Finset.card_pos.mpr ⟨c, hcU⟩
  have hr : (0 : ℝ) < (blockFiber block c \ D).card := by exact_mod_cast hrN
  have hUV : ∀ x, h x ∈ blockFiber block c \ D.image h ↔ x ∈ blockFiber block c \ D := by
    intro x
    constructor
    · intro hx
      simpa using residual_preimage_mem block S hsub D h c (exposed_self_mem S D hh) hx
    · exact residual_image_mem block S hsub D h c (exposed_self_mem S D hh)
  have hT (u : α) (hu : u ∈ blockFiber block c \ D)
      (z : α) (_hz : z ∈ blockFiber block c \ D.image h) :
      0 ≤ 1 - (((blockFiber block c \ D).card : ℝ) - 1) * partnerProb S D h u z := by
    exact sub_nonneg.mpr (conditionalPartner_cap block active S hcap D h hh c hcA.1 hu z)
  have hb := rectangular_correction_touch (blockFiber block c \ D)
    (blockFiber block c \ D.image h) h φ hUV
    (fun u z => 1 - (((blockFiber block c \ D).card : ℝ) - 1) * partnerProb S D h u z)
    hT (fun u hu => correction_row block S hsub D h hh c hu)
    (fun z hz => correction_col block S hsub D h hh c hz) _ hr x
  have he (u z : α) :
      (if advanceRelabel block active h D φ (some (u, z)) (h x) ≠ φ (h x) then
        transition block active S h D (some (u, z)) else 0) =
      if u ∈ blockFiber block c \ D then
        if z ∈ blockFiber block c \ D.image h then
          if correct φ (h u) z (h x) ≠ φ (h x) then
            (1 / ((blockFiber block c \ D).card : ℝ)) *
              ((1 - 1 / ((blockFiber block c \ D).card : ℝ)) * (if z = h u then 1 else 0) +
                (1 / ((blockFiber block c \ D).card : ℝ)) *
                  (1 - (((blockFiber block c \ D).card : ℝ) - 1) * partnerProb S D h u z))
          else 0
        else 0
      else 0 := by
    simp only [advanceRelabel, residualInputs, hc, if_pos hrN, transition]
    split_ifs <;> simp_all
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hn : (if advanceRelabel block active h D φ none (h x) ≠ φ (h x) then
      transition block active S h D none else 0) = 0 := by simp [advanceRelabel]
  rw [hn, zero_add]
  simp only [he,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  exact hb

theorem errorPotential_bellman (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hcap : PartnerCap block active S) (h : Equiv.Perm α) (hh : h ∈ S)
    (D : Finset α) (φ : Equiv.Perm α) (x : α) :
    (∑ e, transition block active S h D e *
      ((if advanceRelabel block active h D φ e (h x) ≠ φ (h x) then 1 else 0) +
        errorPotential block active (advance D e) x)) ≤ errorPotential block active D x := by
  cases hc : nextClass block active D with
  | none => simp [transition, hc, advanceRelabel, advance]
  | some c =>
    have hcA := (mem_remaining block active D c).mp (nextClass_some_mem block active D hc)
    have hcU : c ∈ blockFiber block c \ D := by simp [blockFiber, hcA.2]
    have hr : 0 < (blockFiber block c \ D).card := Finset.card_pos.mpr ⟨c, hcU⟩
    simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
    rw [transition_potential_sum block active S hsub h hh D c hc x]
    have ht := transition_touch_sum block active S hsub hcap h hh D φ c hc x
    by_cases hx : x ∈ blockFiber block c \ D
    · have hxb := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2
      have hxa : active (block x) := hxb.symm ▸ hcA.1
      have hxD := (Finset.mem_sdiff.mp hx).2
      have hxA : active (block x) ∧ x ∉ D := ⟨hxa, hxD⟩
      rw [if_pos hx] at ht ⊢
      rw [errorPotential, if_pos hxA, blockFiber_eq_of_block_eq block hxb,
        errorCost_step _ hr]
      linarith
    · rw [if_neg hx] at ht ⊢
      linarith

theorem weighted_error_triangle {X Y : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ g, 0 ≤ w g) (hsum : ∑ g, w g = 1) (f : X → Y) (a b : Y) :
    (∑ g, if f g ≠ a then w g else 0) ≤
      (∑ g, if f g ≠ b then w g else 0) + (if b ≠ a then 1 else 0) := by
  by_cases hab : b = a
  · simp [hab]
  · rw [if_pos hab]
    have hle : (∑ g, if f g ≠ a then w g else 0) ≤ 1 := by
      rw [← hsum]
      apply Finset.sum_le_sum
      intro g _
      split_ifs
      · exact le_rfl
      · exact hw g
    have hn : 0 ≤ ∑ g, if f g ≠ b then w g else 0 :=
      Finset.sum_nonneg fun g _ => by split_ifs <;> simp_all
    linarith

theorem terminal_error_bound (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (hsub : S ⊆ blockSupport block)
    (hcap : PartnerCap block active S) (h : Equiv.Perm α) (hh : h ∈ S)
    (D : Finset α) (φ : Equiv.Perm α) (t : ℕ) (x : α) :
    (∑ g, if g x ≠ φ (h x) then terminalWeight block active S h D φ t g else 0) ≤
      errorPotential block active D x := by
  induction t generalizing D φ with
  | zero =>
    have he (g : Equiv.Perm α) :
        (if g x ≠ φ (h x) then terminalWeight block active S h D φ 0 g else 0) = 0 := by
      by_cases hg : g x = φ (h x)
      · simp [hg]
      · have hne : h.trans φ ≠ g := by
          intro he
          exact hg (by rw [← he]; rfl)
        simp [hg, terminalWeight, outputAt, hne]
    simp only [he, Finset.sum_const_zero]
    exact errorPotential_nonneg block active D x
  | succ t ih =>
    have he : (∑ g, if g x ≠ φ (h x) then terminalWeight block active S h D φ (t + 1) g else 0) =
        ∑ e, transition block active S h D e *
          ∑ g, if g x ≠ φ (h x) then
            terminalWeight block active S h (advance D e) (advanceRelabel block active h D φ e) t g
          else 0 := by
      simp only [terminalWeight_succ]
      calc
        _ = ∑ g, ∑ e, transition block active S h D e *
            (if g x ≠ φ (h x) then
              terminalWeight block active S h (advance D e)
                (advanceRelabel block active h D φ e) t g else 0) := by
          apply Finset.sum_congr rfl
          intro g _
          split_ifs <;> simp
        _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [he]
    calc
      _ ≤ ∑ e, transition block active S h D e *
          ((if advanceRelabel block active h D φ e (h x) ≠ φ (h x) then 1 else 0) +
            errorPotential block active (advance D e) x) := by
        apply Finset.sum_le_sum
        intro e _
        apply mul_le_mul_of_nonneg_left _ (transition_nonneg block active S hcap h hh D e)
        have hb := weighted_error_triangle
          (terminalWeight block active S h (advance D e) (advanceRelabel block active h D φ e) t)
          (terminalWeight_nonneg block active S hcap h hh _ _ t)
          (terminalWeight_sum block active S hsub h hh _ _ t)
          (fun g : Equiv.Perm α => g x) (φ (h x)) (advanceRelabel block active h D φ e (h x))
        have hi := ih (advance D e) (advanceRelabel block active h D φ e)
        linarith
      _ ≤ _ := errorPotential_bellman block active S hsub hcap h hh D φ x

end FinitePermutationCoupling.RandomOrder

end

section

namespace FiniteCouplingChain

open scoped BigOperators

theorem exists_adjacent_change {X : Type*} {T : ℕ} (p : Fin (T + 1) → X)
    (hne : p 0 ≠ p (Fin.last T)) :
    ∃ i : Fin T, p i.castSucc ≠ p i.succ := by
  by_contra h
  push Not at h
  have hall (i : Fin (T + 1)) : p i = p 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (h i).symm.trans ih
  exact hne (hall (Fin.last T)).symm

theorem endpoint_indicator_le {X : Type*} [DecidableEq X] {T : ℕ}
    (p : Fin (T + 1) → X) (v : ℝ) (hv : 0 ≤ v) :
    (if p 0 ≠ p (Fin.last T) then v else 0) ≤
      ∑ i : Fin T, if p i.castSucc ≠ p i.succ then v else 0 := by
  by_cases he : p 0 = p (Fin.last T)
  · simp only [he, ne_eq, not_true_eq_false, if_false]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
  · obtain ⟨i, hi⟩ := exists_adjacent_change p he
    simp only [he, ne_eq, not_false_eq_true, if_true]
    have hs := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin T => if p j.castSucc ≠ p j.succ then v else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
    simpa only [if_pos hi] using hs

theorem weighted_endpoint_le {Ω X : Type*} [Fintype Ω] [DecidableEq X] {T : ℕ}
    (v : Ω → ℝ) (hv : ∀ ω, 0 ≤ v ω) (p : Ω → Fin (T + 1) → X)
    (b : Fin T → ℝ)
    (hstep : ∀ i, (∑ ω, if p ω i.castSucc ≠ p ω i.succ then v ω else 0) ≤ b i) :
    (∑ ω, if p ω 0 ≠ p ω (Fin.last T) then v ω else 0) ≤ ∑ i, b i := by
  calc
    _ ≤ ∑ ω, ∑ i : Fin T, if p ω i.castSucc ≠ p ω i.succ then v ω else 0 :=
      Finset.sum_le_sum (fun ω _ => endpoint_indicator_le (p ω) (v ω) (hv ω))
    _ = ∑ i : Fin T, ∑ ω, if p ω i.castSucc ≠ p ω i.succ then v ω else 0 :=
      Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hstep i)

section Pushforward

variable {H G Ω : Type*} [Fintype H] [Fintype G] [Fintype Ω] [DecidableEq G]

noncomputable def endpointWeight (v : H → Ω → ℝ) (out : Ω → G) (h : H) (g : G) : ℝ :=
  ∑ ω, if out ω = g then v h ω else 0

theorem endpointWeight_nonneg (v : H → Ω → ℝ) (out : Ω → G)
    (hv : ∀ h ω, 0 ≤ v h ω) (h : H) (g : G) : 0 ≤ endpointWeight v out h g := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hv h ω
  · exact le_rfl

theorem endpointWeight_row (v : H → Ω → ℝ) (out : Ω → G) (h : H) :
    (∑ g, endpointWeight v out h g) = ∑ ω, v h ω := by
  unfold endpointWeight
  rw [Finset.sum_comm]
  simp

theorem endpointWeight_test (v : H → Ω → ℝ) (out : Ω → G) (h : H)
    (P : G → Prop) [DecidablePred P] :
    (∑ g, if P g then endpointWeight v out h g else 0) =
      ∑ ω, if P (out ω) then v h ω else 0 := by
  unfold endpointWeight
  calc
    _ = ∑ g, ∑ ω, if out ω = g then (if P g then v h ω else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hp : P g <;> simp [hp]
    _ = _ := by
      rw [Finset.sum_comm]
      simp

end Pushforward

end FiniteCouplingChain

end

section

namespace FinitePermutationCoupling.RandomOrder

open Classical FiniteCouplingChain
open scoped BigOperators

variable {X I Y : Type*} [Fintype X]

def jumpPath {N : ℕ} (h g : X) (j : Fin N) (t : Fin (N + 1)) : X :=
  if t.val ≤ j.val then g else h

theorem jumpPath_zero {N : ℕ} (h g : X) (j : Fin N) : jumpPath h g j 0 = g := by
  simp [jumpPath]

theorem jumpPath_last {N : ℕ} (h g : X) (j : Fin N) :
    jumpPath h g j (Fin.last N) = h := by
  simp [jumpPath, Nat.not_le.mpr j.isLt]

theorem jumpPath_step {N : ℕ} (obs : X → I → Y) (h g : X) (j i : Fin N) (x : I) :
    obs (jumpPath h g j i.castSucc) x ≠ obs (jumpPath h g j i.succ) x ↔
      j = i ∧ obs g x ≠ obs h x := by
  by_cases hij : i = j
  · subst i
    simp [jumpPath]
  · have hv : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
    rcases lt_or_gt_of_ne hv with hi | hi
    · have hi' : i.val + 1 ≤ j.val := hi
      simp [jumpPath, Nat.le_of_lt hi, hi', Ne.symm hij]
    · have hi' : ¬i.val ≤ j.val := by omega
      have hi'' : ¬i.val + 1 ≤ j.val := by omega
      simp [jumpPath, hi', hi'', Ne.symm hij]

/-- A single randomized jump converts an endpoint bound into a prescribed
stage-by-stage bound. This is a concrete finite pushforward, with exact marginals. -/
theorem endpoint_coupling_jump_chain (N : ℕ) (obs : X → I → Y)
    (w : X → X → ℝ) (source target : X → ℝ)
    (hw : ∀ h g, 0 ≤ w h g)
    (hrow : ∀ h, (∑ g, w h g) = source h)
    (hcol : ∀ g, (∑ h, w h g) = target g)
    (B : Fin N → ℝ) (T : ℝ) (hB : ∀ i, 0 ≤ B i)
    (hT : 0 < T) (hBT : (∑ i, B i) = T) (δ : I → ℝ)
    (herr : ∀ h x, (∑ g, if obs g x ≠ obs h x then w h g else 0) ≤
      T * δ x * source h) :
    ∃ v : X → (Fin (N + 1) → X) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) = source h) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last N) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) = target g) ∧
      (∀ h x (i : Fin N),
        (∑ p, if obs (p i.castSucc) x ≠ obs (p i.succ) x then v h p else 0) ≤
          B i * δ x * source h) := by
  let base : X → X × Fin N → ℝ := fun h ω => w h ω.1 * (B ω.2 / T)
  let v : X → (Fin (N + 1) → X) → ℝ := fun h =>
    endpointWeight base (fun ω => jumpPath h ω.1 ω.2) h
  have hnorm : (∑ i, B i / T) = 1 := by
    rw [← Finset.sum_div, hBT, div_self (ne_of_gt hT)]
  have hn (h : X) (ω : X × Fin N) : 0 ≤ base h ω := by
    exact mul_nonneg (hw h ω.1) (div_nonneg (hB ω.2) (le_of_lt hT))
  refine ⟨v, fun h p => endpointWeight_nonneg _ _ hn h p, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [show (∑ p, v h p) = ∑ ω, base h ω from endpointWeight_row _ _ h]
    simp only [Fintype.sum_prod_type, base, ← Finset.mul_sum, hnorm, mul_one, hrow]
  · intro h p hp
    by_contra hne
    apply hp
    apply Finset.sum_eq_zero
    intro ω _
    have hbad : jumpPath h ω.1 ω.2 ≠ p := by
      intro heq
      apply hne
      rw [← heq, jumpPath_last]
    exact if_neg hbad
  · intro g
    calc
      _ = ∑ h, ∑ ω : X × Fin N, if jumpPath h ω.1 ω.2 0 = g then base h ω else 0 := by
        apply Finset.sum_congr rfl
        intro h _
        exact endpointWeight_test base (fun ω => jumpPath h ω.1 ω.2) h (fun p => p 0 = g)
      _ = target g := by
        have heach (h : X) :
            (∑ ω : X × Fin N, if jumpPath h ω.1 ω.2 0 = g then base h ω else 0) = w h g := by
          simp only [jumpPath_zero, Fintype.sum_prod_type, base]
          rw [Finset.sum_comm]
          simp [← Finset.mul_sum, hnorm]
        simp only [heach, hcol]
  · intro h x i
    have hcalc : (∑ p, if obs (p i.castSucc) x ≠ obs (p i.succ) x then v h p else 0) =
        (B i / T) * (∑ g, if obs g x ≠ obs h x then w h g else 0) := by
      rw [show (∑ p, if obs (p i.castSucc) x ≠ obs (p i.succ) x then v h p else 0) =
        ∑ ω : X × Fin N,
          if obs (jumpPath h ω.1 ω.2 i.castSucc) x ≠ obs (jumpPath h ω.1 ω.2 i.succ) x
          then base h ω else 0 from
        endpointWeight_test base (fun ω => jumpPath h ω.1 ω.2) h
          (fun p => obs (p i.castSucc) x ≠ obs (p i.succ) x)]
      simp only [Fintype.sum_prod_type, jumpPath_step, base]
      calc
        _ = ∑ g, (if obs g x ≠ obs h x then w h g else 0) * (B i / T) := by
          apply Finset.sum_congr rfl
          intro g _
          by_cases hg : obs g x ≠ obs h x <;> simp [hg]
        _ = _ := by rw [← Finset.sum_mul, mul_comm]
    rw [hcalc]
    calc
      _ ≤ (B i / T) * (T * δ x * source h) :=
        mul_le_mul_of_nonneg_left (herr h x) (div_nonneg (hB i) (le_of_lt hT))
      _ = _ := by field_simp

end FinitePermutationCoupling.RandomOrder

end

section

namespace FinitePermutationCoupling.RandomOrder

open scoped BigOperators

noncomputable def harmonicBudget (N : ℕ) : ℝ :=
  ∑ i : Fin N, 1 / ((i.val : ℝ) + 1)

theorem harmonicBudget_pos (N : ℕ) (hN : 0 < N) : 0 < harmonicBudget N := by
  apply Finset.sum_pos
  · intro i _
    positivity
  · exact ⟨⟨0, hN⟩, Finset.mem_univ _⟩

theorem harmonicBudget_eq (N : ℕ) :
    harmonicBudget N = ∑ r ∈ Finset.range N, 1 / ((r : ℝ) + 1) := by
  unfold harmonicBudget
  exact (Finset.sum_range (n := N) (fun r : ℕ => (1 : ℝ) / ((r : ℝ) + 1))).symm

theorem harmonicBudget_dominates (m N : ℕ) (hm : m ≤ N) :
    2 * (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) / (m : ℝ) ≤
      harmonicBudget N * (2 / (m : ℝ)) := by
  have hs : (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) ≤
      ∑ r ∈ Finset.range N, 1 / ((r : ℝ) + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    intro r _ _
    positivity
  rw [← harmonicBudget_eq N] at hs
  calc
    _ = (2 / (m : ℝ)) * (∑ r ∈ Finset.range m, 1 / ((r : ℝ) + 1)) := by ring
    _ ≤ (2 / (m : ℝ)) * harmonicBudget N :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := mul_comm _ _

theorem harmonic_stage_identity (m j : ℕ) :
    (1 / ((j : ℝ) + 1)) * (2 / (m : ℝ)) =
      2 / ((m : ℝ) * ((j : ℝ) + 1)) := by
  simp only [div_mul_eq_div_div]
  ring

end FinitePermutationCoupling.RandomOrder

end

section

namespace FinitePermutationCoupling

open Classical RandomOrder
open scoped BigOperators

theorem random_order_switching_proof
    {α κ : Type*} [Fintype α] (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hN : 0 < N) (hS : S.Nonempty) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S)
    (hcap : PartnerCap block active S)
    (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N) :
    ∃ v : Equiv.Perm α → (Fin (N + 1) → Equiv.Perm α) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) = density S h) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last N) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) =
        density (blockSupport block) g) ∧
      (∀ h (x : α) (i : Fin N),
        (∑ p, if (p i.castSucc) x ≠ (p i.succ) x then v h p else 0) ≤
          (if active (block x) then
            2 / (((blockFiber block x).card : ℝ) * ((i.val : ℝ) + 1))
          else 0) * density S h) := by
  let w (h g : Equiv.Perm α) : ℝ := density S h *
    terminalWeight block active S h ∅ (Equiv.refl α) (Fintype.card α) g
  have hd (h : Equiv.Perm α) : 0 ≤ density S h := by
    unfold density
    split_ifs <;> positivity
  have hw (h g : Equiv.Perm α) : 0 ≤ w h g := by
    by_cases hh : h ∈ S
    · exact mul_nonneg (hd h)
        (terminalWeight_nonneg block active S hcap h hh ∅ (Equiv.refl α) _ g)
    · simp [w, density, hh]
  have hrow (h : Equiv.Perm α) : (∑ g, w h g) = density S h := by
    by_cases hh : h ∈ S
    · simp only [w, ← Finset.mul_sum,
        terminalWeight_sum block active S hsub h hh, mul_one]
    · simp [w, density, hh]
  have hcol (g : Equiv.Perm α) : (∑ h, w h g) = density (blockSupport block) g :=
    terminal_uniform_initial block active S hsub hsat hS g
  let δ (x : α) : ℝ := if active (block x) then 2 / ((blockFiber block x).card : ℝ) else 0
  have herr (h : Equiv.Perm α) (x : α) :
      (∑ g, if g x ≠ h x then w h g else 0) ≤ harmonicBudget N * δ x * density S h := by
    by_cases hh : h ∈ S
    · have he := terminal_error_bound block active S hsub hcap h hh ∅
        (Equiv.refl α) (Fintype.card α) x
      have he' : (∑ g, if g x ≠ h x then
          terminalWeight block active S h ∅ (Equiv.refl α) (Fintype.card α) g else 0) ≤
          if active (block x) then errorCost (blockFiber block x).card else 0 := by
        simp only [Equiv.refl_apply, errorPotential, Finset.notMem_empty, not_false_eq_true, and_true,
          Finset.sdiff_empty] at he
        convert he using 1 <;>
          first
          | apply Finset.sum_congr rfl
            intro g _
            split_ifs <;> rfl
          | congr 1 <;> exact Subsingleton.elim _ _
      have hb : (if active (block x) then errorCost (blockFiber block x).card else 0) ≤
          harmonicBudget N * δ x := by
        by_cases ha : active (block x)
        · simp only [δ, if_pos ha, errorCost]
          exact harmonicBudget_dominates (blockFiber block x).card N (hsize x ha)
        · simp [δ, ha]
      calc
        _ = density S h * (∑ g, if g x ≠ h x then
            terminalWeight block active S h ∅ (Equiv.refl α) (Fintype.card α) g else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _
          split_ifs <;> simp [w]
        _ ≤ density S h * (if active (block x) then errorCost (blockFiber block x).card else 0) :=
          mul_le_mul_of_nonneg_left he' (hd h)
        _ ≤ density S h * (harmonicBudget N * δ x) :=
          mul_le_mul_of_nonneg_left hb (hd h)
        _ = _ := by ring
    · simp [w, density, hh]
  let B (i : Fin N) : ℝ := 1 / ((i.val : ℝ) + 1)
  obtain ⟨v, hv, hvr, hvl, hvc, hvs⟩ :=
    endpoint_coupling_jump_chain N (fun (π : Equiv.Perm α) (x : α) => π x)
      w (density S) (density (blockSupport block)) hw hrow hcol
      B (harmonicBudget N) (fun i => by dsimp [B]; positivity)
      (harmonicBudget_pos N hN) rfl δ herr
  refine ⟨v, hv, hvr, hvl, ?_, ?_⟩
  · intro g
    convert hvc g using 1
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> rfl
  intro h x i
  have hc : B i * δ x =
      if active (block x) then
        2 / (((blockFiber block x).card : ℝ) * ((i.val : ℝ) + 1)) else 0 := by
    by_cases ha : active (block x)
    · simp only [B, δ, if_pos ha]
      exact harmonic_stage_identity (blockFiber block x).card i.val
    · simp [δ, ha]
  simpa only [hc] using hvs h x i

end FinitePermutationCoupling

end

open Classical FinitePermutationCoupling
open scoped BigOperators

theorem solution
    {α κ : Type*} [Fintype α] (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) (N : ℕ)
    (hN : 0 < N) (hS : S.Nonempty) (hsub : S ⊆ blockSupport block)
    (hsat : ActiveSaturated block active S)
    (hcap : PartnerCap block active S)
    (hsize : ∀ x, active (block x) → (blockFiber block x).card ≤ N) :
    ∃ v : Equiv.Perm α → (Fin (N + 1) → Equiv.Perm α) → ℝ,
      (∀ h p, 0 ≤ v h p) ∧
      (∀ h, (∑ p, v h p) = density S h) ∧
      (∀ h p, v h p ≠ 0 → p (Fin.last N) = h) ∧
      (∀ g, (∑ h, ∑ p, if p 0 = g then v h p else 0) =
        density (blockSupport block) g) ∧
      (∀ h (x : α) (i : Fin N),
        (∑ p, if (p i.castSucc) x ≠ (p i.succ) x then v h p else 0) ≤
          (if active (block x) then
            2 / (((blockFiber block x).card : ℝ) * ((i.val : ℝ) + 1))
          else 0) * density S h) := by
  exact FinitePermutationCoupling.random_order_switching_proof block active S N hN hS hsub hsat hcap hsize

