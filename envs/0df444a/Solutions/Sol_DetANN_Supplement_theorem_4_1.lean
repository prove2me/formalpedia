-- Prove2me | solution 1 for DetANN.Supplement.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T05:09:08.578589+00:00
-- url     : https://prove2.me/submissions/a3652a6e-9026-46aa-9156-a24b42bbae05

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily
import Theorems.Thm_DetANN_eq_27

namespace DetANNT41Aux

open DetANN

variable {n d : ℕ}

/-- Summing over all tuples by fixing coordinate `j`. -/
lemma sum_insertNth {M : Type*} [AddCommMonoid M] (j : Fin (n + 1))
    (F : (Fin (n + 1) → Fin d) → M) :
    ∑ ω, F ω = ∑ a : Fin d, ∑ ρ : Fin n → Fin d, F (Fin.insertNth j a ρ) := by
  rw [← (Fin.insertNthEquiv (fun _ => Fin d) j).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The exhaustive family. -/
def exS (n d : ℕ) : (Fin (n + 1) → Fin d) → Fin (n + 1) → Fin d := fun ω j => ω j

lemma sum_pairs_fun {M : Type*} [AddCommMonoid M] (f : Fin d → M) :
    ∑ p : (Fin (n + 1) → Fin d) × Fin (n + 1), f (p.1 p.2) =
      ((n + 1) * d ^ n) • ∑ i, f i := by
  rw [Fintype.sum_prod_type_right]
  have : ∀ j : Fin (n + 1), ∑ ω : Fin (n + 1) → Fin d, f (ω j) = d ^ n • ∑ i, f i := by
    intro j
    rw [sum_insertNth j]
    simp [Fin.insertNth_apply_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.smul_sum]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul]

lemma blockCount_exS (i : Fin d) : blockCount (exS n d) i = (n + 1) * d ^ n := by
  have h := sum_pairs_fun (n := n) (d := d) (fun a => if a = i then (1 : ℕ) else 0)
  unfold blockCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact h.trans (by simp)

lemma uniformFreq_exS : UniformFreq (exS n d) := by
  intro i
  rw [blockCount_exS]
  simp [Fintype.card_fin]; ring


section Variance

open scoped RealInnerProductSpace

variable (x : (Fin (n + 1) → Fin d) → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d))

/-- The conditional mean given coordinate `j`: `g j i = E[x_ω − x⋆ | ω_j = i]`. -/
noncomputable def gcond (j : Fin (n + 1)) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  ((d : ℝ) ^ n)⁻¹ • ∑ ρ : Fin n → Fin d, (x (Fin.insertNth j i ρ) - xs)

lemma card_V : Fintype.card (Fin (n + 1) → Fin d) = d ^ (n + 1) := by simp

lemma fiber_sum (i : Fin d) :
    ∑ p ∈ Finset.univ.filter (fun p : (Fin (n + 1) → Fin d) × Fin (n + 1) => exS n d p.1 p.2 = i),
        (x p.1 - xs) =
      ∑ j : Fin (n + 1), ∑ ρ : Fin n → Fin d, (x (Fin.insertNth j i ρ) - xs) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_insertNth j]
  simp [exS, Fin.insertNth_apply_same]

lemma condMean_exS (hd : 1 ≤ d) (i : Fin d) :
    condMean (exS n d) x xs i = ((n : ℝ) + 1)⁻¹ • ∑ j, gcond x xs j i := by
  have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  unfold condMean gcond
  rw [blockCount_exS, fiber_sum, ← Finset.smul_sum, smul_smul]
  congr 1
  push_cast; field_simp

lemma sum_gcond (hd : 1 ≤ d) (j : Fin (n + 1)) :
    ∑ i, gcond x xs j i = (d : ℝ) • mean x xs := by
  have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  unfold gcond mean
  rw [← Finset.smul_sum, ← sum_insertNth j (fun ω => x ω - xs), card_V, smul_smul]
  congr 1
  push_cast; field_simp; ring

lemma betweenVar_exS (hd : 1 ≤ d) :
    betweenVar (exS n d) x xs =
      (d : ℝ)⁻¹ * ∑ i, ‖condMean (exS n d) x xs i - mean x xs‖ ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  unfold betweenVar
  have h := sum_pairs_fun (n := n) (d := d) (fun i => ‖condMean (exS n d) x xs i - mean x xs‖ ^ 2)
  simp only [exS] at h ⊢
  rw [h, nsmul_eq_mul, card_V]
  simp only [Fintype.card_fin]
  push_cast
  field_simp
  ring

lemma total_var (hd : 1 ≤ d) :
    withinVar (exS n d) x xs + betweenVar (exS n d) x xs =
      ((d : ℝ) ^ (n + 1))⁻¹ * ∑ ω, ‖x ω - xs - mean x xs‖ ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  set c := condMean (exS n d) x xs
  set a := mean x xs
  -- the cross terms vanish fiberwise
  have hcross : ∑ p : (Fin (n + 1) → Fin d) × Fin (n + 1),
      ⟪x p.1 - xs - c (exS n d p.1 p.2), c (exS n d p.1 p.2) - a⟫ = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ (fun p : (Fin (n + 1) → Fin d) × Fin (n + 1) =>
      exS n d p.1 p.2)]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hfib : ∀ p ∈ Finset.univ.filter (fun p : (Fin (n + 1) → Fin d) × Fin (n + 1) =>
        exS n d p.1 p.2 = i), ⟪x p.1 - xs - c (exS n d p.1 p.2), c (exS n d p.1 p.2) - a⟫ =
          ⟪x p.1 - xs - c i, c i - a⟫ := by
      intro p hp; rw [(Finset.mem_filter.1 hp).2]
    rw [Finset.sum_congr rfl hfib, ← sum_inner, Finset.sum_sub_distrib, Finset.sum_const]
    have hc : c i = (blockCount (exS n d) i : ℝ)⁻¹ •
        ∑ p ∈ Finset.univ.filter (fun p : (Fin (n + 1) → Fin d) × Fin (n + 1) =>
          exS n d p.1 p.2 = i), (x p.1 - xs) := rfl
    have hbc : (blockCount (exS n d) i : ℝ) ≠ 0 := by
      rw [blockCount_exS]; push_cast; positivity
    have hcard : (Finset.univ.filter (fun p : (Fin (n + 1) → Fin d) × Fin (n + 1) =>
        exS n d p.1 p.2 = i)).card = blockCount (exS n d) i := rfl
    rw [hcard, hc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hbc, one_smul,
      sub_self, inner_zero_left]
  have hpt : ∀ p : (Fin (n + 1) → Fin d) × Fin (n + 1),
      ‖x p.1 - xs - c (exS n d p.1 p.2)‖ ^ 2 + ‖c (exS n d p.1 p.2) - a‖ ^ 2 =
        ‖x p.1 - xs - a‖ ^ 2 - 2 * ⟪x p.1 - xs - c (exS n d p.1 p.2), c (exS n d p.1 p.2) - a⟫ := by
    intro p
    have : x p.1 - xs - a = (x p.1 - xs - c (exS n d p.1 p.2)) + (c (exS n d p.1 p.2) - a) := by abel
    rw [this, norm_add_sq_real]; ring
  unfold withinVar betweenVar
  rw [← mul_add, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun p _ => hpt p),
    Finset.sum_sub_distrib, ← Finset.mul_sum, hcross, mul_zero, sub_zero,
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, card_V]
  rw [← Finset.mul_sum]
  push_cast
  field_simp

/-- The centred coordinate projections. -/
noncomputable def hproj (j : Fin (n + 1)) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  gcond x xs j i - mean x xs

lemma sum_ins_z (hd : 1 ≤ d) (j : Fin (n + 1)) (i : Fin d) :
    ∑ ρ : Fin n → Fin d, (x (Fin.insertNth j i ρ) - xs - mean x xs) =
      ((d : ℝ) ^ n) • hproj x xs j i := by
  have hd0 : ((d : ℝ) ^ n) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  unfold hproj gcond
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, smul_sub, smul_smul, mul_inv_cancel₀ hd0, one_smul,
    ← Nat.cast_smul_eq_nsmul ℝ]
  norm_cast

lemma B1 (hd : 1 ≤ d) (j : Fin (n + 1)) :
    ∑ ω, ⟪x ω - xs - mean x xs, hproj x xs j (ω j)⟫ = (d : ℝ) ^ n * ∑ i, ‖hproj x xs j i‖ ^ 2 := by
  rw [sum_insertNth j]
  simp only [Fin.insertNth_apply_same]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_inner, sum_ins_z x xs hd, real_inner_smul_left, real_inner_self_eq_norm_sq]

lemma B2 (j : Fin (n + 1)) :
    ∑ ω : Fin (n + 1) → Fin d, ‖hproj x xs j (ω j)‖ ^ 2 =
      (d : ℝ) ^ n * ∑ i, ‖hproj x xs j i‖ ^ 2 := by
  rw [sum_insertNth j]
  simp [Fin.insertNth_apply_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]

lemma sum_hproj (hd : 1 ≤ d) (k : Fin (n + 1)) : ∑ b, hproj x xs k b = 0 := by
  unfold hproj
  rw [Finset.sum_sub_distrib, sum_gcond x xs hd, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, sub_self]

lemma B3 (hd : 1 ≤ d) (j k : Fin (n + 1)) (hjk : j ≠ k) :
    ∑ ω : Fin (n + 1) → Fin d, ⟪hproj x xs j (ω j), hproj x xs k (ω k)⟫ = 0 := by
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjk
  rw [sum_insertNth k, Finset.sum_comm]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [← inner_sum, sum_hproj x xs hd, inner_zero_right]

lemma bessel (hd : 1 ≤ d) :
    (d : ℝ)⁻¹ * ∑ j, ∑ i, ‖hproj x xs j i‖ ^ 2 ≤
      ((d : ℝ) ^ (n + 1))⁻¹ * ∑ ω, ‖x ω - xs - mean x xs‖ ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set z := fun ω : Fin (n + 1) → Fin d => x ω - xs - mean x xs
  set H := fun ω : Fin (n + 1) → Fin d => ∑ j, hproj x xs j (ω j)
  have hexp : ∀ ω, ‖z ω - H ω‖ ^ 2 =
      ‖z ω‖ ^ 2 - 2 * ∑ j, ⟪z ω, hproj x xs j (ω j)⟫ +
        ∑ j, ∑ k, ⟪hproj x xs j (ω j), hproj x xs k (ω k)⟫ := by
    intro ω
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (H ω)]
    simp only [H, inner_sum, sum_inner]
    congr 1
    exact Finset.sum_comm
  have hcross : ∑ ω : Fin (n + 1) → Fin d, ∑ j, ∑ k, ⟪hproj x xs j (ω j), hproj x xs k (ω k)⟫ =
      ∑ j, (d : ℝ) ^ n * ∑ i, ‖hproj x xs j i‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single j]
    · rw [← B2]; simp
    · intro k _ hkj; exact B3 x xs hd j k (Ne.symm hkj)
    · simp
  have h0 : 0 ≤ ∑ ω, ‖z ω - H ω‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  rw [Finset.sum_congr rfl (fun ω _ => hexp ω), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hcross, ← Finset.mul_sum, Finset.sum_comm] at h0
  simp only [z] at h0
  simp only [B1 x xs hd] at h0
  rw [← Finset.mul_sum] at h0
  have key : (d : ℝ) ^ n * ∑ j, ∑ i, ‖hproj x xs j i‖ ^ 2 ≤ ∑ ω, ‖x ω - xs - mean x xs‖ ^ 2 := by
    nlinarith
  rw [pow_succ, mul_inv, mul_comm ((d : ℝ) ^ n)⁻¹, mul_assoc]
  gcongr
  rw [le_inv_mul_iff₀ (by positivity)]
  exact key

lemma condMean_sub_mean (hd : 1 ≤ d) (i : Fin d) :
    condMean (exS n d) x xs i - mean x xs = ((n : ℝ) + 1)⁻¹ • ∑ j, hproj x xs j i := by
  rw [condMean_exS x xs hd]
  unfold hproj
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : ((n : ℝ) + 1)⁻¹ * ((n + 1 : ℕ) : ℝ) = 1 := by push_cast; field_simp
  rw [this, one_smul]

lemma norm_avg_sq (v : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) :
    ‖((n : ℝ) + 1)⁻¹ • ∑ j, v j‖ ^ 2 ≤ ((n : ℝ) + 1)⁻¹ * ∑ j, ‖v j‖ ^ 2 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)]
  have h1 : ‖∑ j, v j‖ ^ 2 ≤ (∑ j, ‖v j‖) ^ 2 := by
    gcongr; exact norm_sum_le _ _
  have h2 : (∑ j, ‖v j‖) ^ 2 ≤ ((n : ℝ) + 1) * ∑ j, ‖v j‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖v j‖)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  calc ((n : ℝ) + 1)⁻¹ ^ 2 * ‖∑ j, v j‖ ^ 2 ≤ ((n : ℝ) + 1)⁻¹ ^ 2 * (((n : ℝ) + 1) * ∑ j, ‖v j‖ ^ 2) := by
        gcongr; exact h1.trans h2
    _ = ((n : ℝ) + 1)⁻¹ * ∑ j, ‖v j‖ ^ 2 := by field_simp

/-- **Lemma 5.1 bound** for the exhaustive family: `between ≤ within / (s − 1)`, `s = n + 1`. -/
lemma between_le_within (hd : 1 ≤ d) (hn : 1 ≤ n) :
    betweenVar (exS n d) x xs ≤ (1 / (n : ℝ)) * withinVar (exS n d) x xs := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hB : betweenVar (exS n d) x xs ≤
      ((n : ℝ) + 1)⁻¹ * (withinVar (exS n d) x xs + betweenVar (exS n d) x xs) := by
    rw [total_var x xs hd, betweenVar_exS x xs hd]
    calc (d : ℝ)⁻¹ * ∑ i, ‖condMean (exS n d) x xs i - mean x xs‖ ^ 2
        ≤ (d : ℝ)⁻¹ * ∑ i, ((n : ℝ) + 1)⁻¹ * ∑ j, ‖hproj x xs j i‖ ^ 2 := by
          gcongr with i
          rw [condMean_sub_mean x xs hd]
          exact norm_avg_sq _
      _ = ((n : ℝ) + 1)⁻¹ * ((d : ℝ)⁻¹ * ∑ j, ∑ i, ‖hproj x xs j i‖ ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_comm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (bessel x xs hd) (by positivity)
  have hW : 0 ≤ withinVar (exS n d) x xs := by
    unfold withinVar; positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hnpos]
  have h1 : ((n : ℝ) + 1) * betweenVar (exS n d) x xs ≤
      withinVar (exS n d) x xs + betweenVar (exS n d) x xs := by
    have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  nlinarith

end Variance


/-- Part 2: `|C_{α,τ,s} − α| ≤ K (1/√s + √τ)` with `K = 10|A| + 8`. -/
lemma part2 (Abd : ℝ) : ∃ K : ℝ, ∀ α τ : ℝ, 1 ≤ α → α ≤ Abd → 0 < τ → τ ≤ 1 / 2 →
    ∀ s : ℕ, 2 ≤ s →
      |(α + Real.sqrt (2 * α ^ 2 / ((s : ℝ) - 1) + 12 * τ * (1 + α) ^ 2)) /
          Real.sqrt (1 - τ) - α| ≤
        K * (1 / Real.sqrt s + Real.sqrt τ) := by
  refine ⟨10 * |Abd| + 8, fun α τ hα hαA hτ hτ2 s hs => ?_⟩
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  set u := Real.sqrt τ with hu_def
  set w := 1 / Real.sqrt s with hw_def
  set r := Real.sqrt (1 - τ) with hr_def
  set X := 2 * α ^ 2 / ((s : ℝ) - 1) + 12 * τ * (1 + α) ^ 2 with hX_def
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = τ := Real.sq_sqrt hτ.le
  have hu1 : u ≤ 1 := by nlinarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have hw0 : 0 < w := by positivity
  have hw2 : w ^ 2 = 1 / s := by
    rw [hw_def, div_pow, Real.sq_sqrt (by linarith)]; ring
  have hr2 : r ^ 2 = 1 - τ := Real.sq_sqrt (by linarith)
  have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr1 : r ≤ 1 := by nlinarith
  have hrh : 1 / 2 ≤ r := by nlinarith
  have hrτ : 1 - τ ≤ r := by nlinarith
  have hA : α ≤ |Abd| := hαA.trans (le_abs_self _)
  -- √X ≤ 2αw + 4(1+α)u
  have hXle : X ≤ (2 * α * w + 4 * (1 + α) * u) ^ 2 := by
    have h1 : 2 * α ^ 2 / ((s : ℝ) - 1) ≤ 4 * α ^ 2 * w ^ 2 := by
      rw [hw2, div_le_iff₀ (by linarith)]
      have : 4 * α ^ 2 * (1 / (s : ℝ)) * ((s : ℝ) - 1) = 4 * α ^ 2 - 4 * α ^ 2 / s := by
        field_simp
      rw [this]
      have : 4 * α ^ 2 / (s : ℝ) ≤ 2 * α ^ 2 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have h2 : 12 * τ * (1 + α) ^ 2 ≤ 16 * (1 + α) ^ 2 * u ^ 2 := by
      rw [hu2]; nlinarith
    have h3 : 0 ≤ 16 * α * (1 + α) * w * u := by positivity
    nlinarith
  have hsX : Real.sqrt X ≤ 2 * α * w + 4 * (1 + α) * u :=
    (Real.sqrt_le_left (by positivity)).2 hXle
  have hX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hge : α ≤ (α + Real.sqrt X) / r := by
    rw [le_div_iff₀ hr0]; nlinarith
  rw [abs_of_nonneg (by linarith)]
  have hle : (α + Real.sqrt X) / r ≤ α + (10 * |Abd| + 8) * (w + u) := by
    rw [div_le_iff₀ hr0]
    have hK : 0 ≤ (10 * |Abd| + 8) * (w + u) := by positivity
    have e1 : α * u ^ 2 ≤ α * u :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    have e2 : α * τ = α * u ^ 2 := by rw [hu2]
    have s1 : α * (1 - τ) ≤ α * r := mul_le_mul_of_nonneg_left hrτ (by linarith)
    have s2 : (10 * |Abd| + 8) * (w + u) * (1 / 2) ≤ (10 * |Abd| + 8) * (w + u) * r :=
      mul_le_mul_of_nonneg_left hrh hK
    have s3 : 2 * α * w ≤ (5 * |Abd| + 4) * w :=
      mul_le_mul_of_nonneg_right (by linarith) hw0.le
    have s4 : (5 * α + 4) * u ≤ (5 * |Abd| + 4) * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu0
    have : (α + (10 * |Abd| + 8) * (w + u)) * r = α * r + (10 * |Abd| + 8) * (w + u) * r := by ring
    rw [this]
    linarith
  linarith


/-- Part 1, with `s = n + 1`. -/
lemma part1 {d b n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (τ α : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hα : 1 ≤ α) (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hA : IsBalancedBlockSystem τ P A)
    (q : EuclideanSpace ℝ (Fin d)) (x : (Fin (n + 1) → Fin d) → EuclideanSpace ℝ (Fin d))
    (hxP : ∀ ω, x ω ∈ P)
    (hloc : LocalGuarantee A (fun (ω : Fin (n + 1) → Fin d) (j : Fin (n + 1)) => ω j) P q x α) :
    ∃ ω : Fin (n + 1) → Fin d, ∀ y ∈ P,
      ‖q - x ω‖ ≤
        (α + Real.sqrt (2 * α ^ 2 / (((n + 1 : ℕ) : ℝ) - 1) + 12 * τ * (1 + α) ^ 2)) /
          Real.sqrt (1 - τ) * ‖q - y‖ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨xs, hxs, hmin⟩ := P.exists_min_image (fun y => ‖q - y‖)
    ⟨x (fun _ => ⟨0, hd⟩), hxP _⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hκ := between_le_within x xs hd hn
  obtain ⟨-, ω, hω⟩ := eq_27 (Vtx := Fin (n + 1) → Fin d) (Occ := Fin (n + 1)) τ α hτ0 hτ1 hα P A hA
    (exS n d) uniformFreq_exS q xs hxs x hxP hloc (1 / (n : ℝ)) (by positivity) hκ
  have hC : (2 * α ^ 2 / (((n + 1 : ℕ) : ℝ) - 1)) = 2 * α ^ 2 * (1 / (n : ℝ)) := by
    push_cast; ring
  refine ⟨ω, fun y hy => ?_⟩
  rw [hC]
  have hCnn : 0 ≤ (α + Real.sqrt (2 * α ^ 2 * (1 / (n : ℝ)) + 12 * τ * (1 + α) ^ 2)) /
      Real.sqrt (1 - τ) := by
    have : 0 ≤ α := by linarith
    positivity
  exact hω.trans (mul_le_mul_of_nonneg_left (hmin y hy) hCnn)

end DetANNT41Aux

open DetANN DetANNT41Aux in
theorem solution :
    (∀ {d b s : ℕ}, 1 ≤ d → 2 ≤ s →
      ∀ τ α : ℝ, 0 < τ → τ < 1 → 1 ≤ α →
        ∀ (P : Finset (EuclideanSpace ℝ (Fin d)))
          (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b)),
          IsBalancedBlockSystem τ P A →
          ∀ (q : EuclideanSpace ℝ (Fin d)) (x : (Fin s → Fin d) → EuclideanSpace ℝ (Fin d)),
            (∀ ω, x ω ∈ P) →
            LocalGuarantee A (fun (ω : Fin s → Fin d) (j : Fin s) => ω j) P q x α →
            ∃ ω : Fin s → Fin d, ∀ y ∈ P,
              ‖q - x ω‖ ≤
                (α + Real.sqrt (2 * α ^ 2 / ((s : ℝ) - 1) + 12 * τ * (1 + α) ^ 2)) /
                  Real.sqrt (1 - τ) * ‖q - y‖) ∧
    (∀ Abd : ℝ, ∃ K : ℝ, ∀ α τ : ℝ, 1 ≤ α → α ≤ Abd → 0 < τ → τ ≤ 1 / 2 →
      ∀ s : ℕ, 2 ≤ s →
        |(α + Real.sqrt (2 * α ^ 2 / ((s : ℝ) - 1) + 12 * τ * (1 + α) ^ 2)) /
            Real.sqrt (1 - τ) - α| ≤
          K * (1 / Real.sqrt s + Real.sqrt τ)) := by
  refine ⟨?_, part2⟩
  intro d b s hd hs τ α hτ0 hτ1 hα P A hA q x hxP hloc
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  exact part1 hd (by omega) τ α hτ0 hτ1 hα P A hA q x hxP hloc
