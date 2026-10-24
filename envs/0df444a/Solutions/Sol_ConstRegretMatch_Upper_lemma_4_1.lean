-- Prove2me | solution 1 for ConstRegretMatch.Upper.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:09:23.233609+00:00
-- url     : https://prove2.me/submissions/8c0c2b74-f8f6-453f-82b0-a48ec2b8b41f

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy
import Theorems.Thm_ConstRegretMatch_Upper_eq_4_basis_inverse
import Theorems.Thm_ConstRegretMatch_Upper_dual_theta

open ConstRegretMatch.Upper

namespace CRML41Sol

variable {n d : ℕ}

lemma expect_mono (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ)
    (F G : (ℕ → Fin n) → ℝ) (h : ∀ ω, F ω ≤ G ω) : expect lam t F ≤ expect lam t G := by
  unfold expect
  split_ifs with hn
  · apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left (h _)
    exact Finset.prod_nonneg (fun s _ => (hlam.1 _).le)
  · exact le_refl _

lemma expect_zero (lam : Fin n → ℝ) (t : ℕ) : expect lam t (fun _ => 0) = 0 := by
  unfold expect; split_ifs <;> simp

lemma expect_sub (lam : Fin n → ℝ) (t : ℕ) (F G : (ℕ → Fin n) → ℝ) :
    expect lam t (fun ω => F ω - G ω) = expect lam t F - expect lam t G := by
  unfold expect
  split_ifs
  · rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro w _; ring
  · simp

lemma expect_sum {ι : Type*} (lam : Fin n → ℝ) (t : ℕ) (S : Finset ι)
    (F : ι → (ℕ → Fin n) → ℝ) :
    expect lam t (fun ω => ∑ i ∈ S, F i ω) = ∑ i ∈ S, expect lam t (F i) := by
  unfold expect
  split_ifs
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro w _; rw [Finset.mul_sum]
  · simp

lemma expect_const_mul (lam : Fin n → ℝ) (t : ℕ) (c : ℝ) (F : (ℕ → Fin n) → ℝ) :
    expect lam t (fun ω => c * F ω) = c * expect lam t F := by
  unfold expect
  split_ifs
  · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring
  · simp

lemma expect_succ (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ)
    (G : (ℕ → Fin n) → ℝ) (hG : ∀ ω ω', (∀ s < t, ω s = ω' s) → G ω = G ω') :
    expect lam (t + 1) G = expect lam t G := by
  unfold expect
  split_ifs with hn
  · rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w' _
    have hext : ∀ a, G (extendPath ((Fin.snocEquiv (fun _ => Fin n)) (a, w')) ⟨0, hn⟩) =
        G (extendPath w' ⟨0, hn⟩) := by
      intro a
      apply hG
      intro s hs
      have hs1 : s < t + 1 := by omega
      simp only [extendPath, hs, hs1, dif_pos, Fin.snocEquiv_apply]
      have : (⟨s, hs1⟩ : Fin (t + 1)) = Fin.castSucc ⟨s, hs⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [hext, Fin.prod_univ_castSucc, Fin.snocEquiv_apply, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hlam.2]
    ring
  · rfl

lemma arrivals_mono (ω : ℕ → Fin n) {s t : ℕ} (h : t ≤ s) (i : Fin n) :
    arrivals ω t i ≤ arrivals ω s i := by
  unfold arrivals arrivalsBetween
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Ico_subset_Ico_right h

lemma arrivals_congr (ω ω' : ℕ → Fin n) (t : ℕ) (h : ∀ s < t, ω s = ω' s) :
    arrivals ω t = arrivals ω' t := by
  funext i
  unfold arrivals arrivalsBetween
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [h x hx.2]

lemma cast_inc_sum (N : MatchingNetwork n d) (i : Fin n) (y : Fin d → ℕ) :
    ∑ m, N.M i m * (y m : ℝ) = ((∑ m, N.inc i m * y m : ℕ) : ℝ) := by
  push_cast; rfl

lemma staticOpt_le_dual (N : MatchingNetwork n d) (r : Fin d → ℝ) (u : Fin n → ℕ)
    (θ : Fin n → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : ∀ m, r m ≤ ∑ i, N.M i m * θ i) :
    staticOpt N r u ≤ ∑ i, θ i * (u i : ℝ) := by
  unfold staticOpt
  apply Finset.max'_le
  intro x hx
  rw [Finset.mem_insert, Finset.mem_image] at hx
  rcases hx with rfl | ⟨y, hy, rfl⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hθ0 i) (Nat.cast_nonneg _))
  · have hf := (Finset.mem_filter.mp hy).2
    calc ∑ m, r m * (y m : ℝ) ≤ ∑ m, (∑ i, N.M i m * θ i) * (y m : ℝ) :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_right (hθ m) (Nat.cast_nonneg _))
      _ = ∑ i, θ i * (∑ m, N.M i m * (y m : ℝ)) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro m _; ring
      _ ≤ ∑ i, θ i * (u i : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hθ0 i)
          rw [cast_inc_sum]
          exact_mod_cast hf i

lemma gpGap_nonneg (z : Fin d → ℝ) (s : Fin n → ℝ) : 0 ≤ gpGap z s := by
  unfold gpGap
  split_ifs with h
  · apply Finset.le_min'
    intro y hy
    simp only [gapValues, Finset.mem_union, Finset.mem_image, Mplus, Qplus, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy
    rcases hy with ⟨m, hm, rfl⟩ | ⟨j, hj, rfl⟩
    · exact hm.le
    · exact hj.le
  · exact le_refl 0

end CRML41Sol

open CRML41Sol in
theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ) (hr : IsMatchValues r) :
    ∀ C : ℝ, 0 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
      ∀ D : Policy n d, IsAdmissible N D →
        (∀ t ω, ∀ m ∈ Mzero z, D t ω m = 0) →
        (∀ t : ℕ, 1 ≤ t → ∀ i ∈ Qzero s,
          expect lam t (fun ω => (queue N D ω t i : ℝ)) ≤ C / gpGap z s) →
        ∀ t : ℕ, 1 ≤ t → Rstar N lam r t - valueOf lam r D t ≤ C' / gpGap z s := by
  obtain ⟨ω0, hω0, hY⟩ := eq_4_basis_inverse N
  intro C hC
  set Θ := ω0 * ∑ m, r m with hΘdef
  have hΘ : 0 ≤ Θ := mul_nonneg hω0.le (Finset.sum_nonneg fun m _ => (hr m).le)
  refine ⟨n * Θ * C, by positivity, ?_⟩
  intro lam hlam z s hGP D hD hM0 hQ t ht
  obtain ⟨⟨θ, hθ, -⟩, hall⟩ := dual_theta N r hr lam hlam z s hGP
  obtain ⟨hform, hθ0, hθfeas, -, -⟩ := hall θ hθ
  obtain ⟨Y, hYB, -, -, -, hYb⟩ := hY r hr lam hlam z s hGP
  have hθle : ∀ i, θ i ≤ Θ := by
    intro i
    rw [hform Y hYB i]
    calc ∑ m : {m // m ∈ Mplus z}, r m.1 * Y (Sum.inl m) i
          ≤ ∑ m : {m // m ∈ Mplus z}, r m.1 * ω0 :=
          Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans (hYb _ _)) (hr _).le)
      _ ≤ ∑ m, r m * ω0 := by
          rw [← Finset.sum_subtype (Mplus z) (p := fun m => m ∈ Mplus z) (fun _ => Iff.rfl)
            (fun m => r m * ω0)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun m _ _ => mul_nonneg (hr m).le hω0.le)
      _ = Θ := by rw [← Finset.sum_mul, hΘdef]; ring
  -- X i ω = A^t_i - (M D^t)_i
  set X : Fin n → (ℕ → Fin n) → ℝ := fun i ω =>
    (arrivals ω t i : ℝ) - ∑ m, N.M i m * (D t ω m : ℝ) with hX
  have hpath1 : ∀ ω, staticOpt N r (arrivals ω t) - ∑ m, r m * (D t ω m : ℝ) ≤
      ∑ i ∈ Qzero s, θ i * X i ω := by
    intro ω
    have h1 := staticOpt_le_dual N r (arrivals ω t) θ hθ0 hθfeas
    have h2 : ∑ m, r m * (D t ω m : ℝ) = ∑ i, θ i * ∑ m, N.M i m * (D t ω m : ℝ) := by
      have : ∀ m, r m * (D t ω m : ℝ) = (∑ i, N.M i m * θ i) * (D t ω m : ℝ) := by
        intro m
        by_cases hm : m ∈ Mplus z
        · rw [hθ.2 m hm]
        · have : m ∈ Mzero z := by
            simp only [Mplus, Mzero, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
            exact hm
          rw [hM0 t ω m this]; simp
      simp_rw [this, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro m _; ring
    have h3 : ∑ i, θ i * X i ω = ∑ i ∈ Qzero s, θ i * X i ω := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have : i ∈ Qplus s := by
        simp only [Qplus, Qzero, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact not_not.mp hi
      rw [hθ.1 i this, zero_mul]
    rw [← h3]
    simp only [hX, mul_sub, Finset.sum_sub_distrib]
    linarith
  have hpath2 : ∀ i ω, X i ω ≤ (queue N D ω (t + 1) i : ℝ) := by
    intro i ω
    have hf := hD.2.2.2 t ω i
    have hm := arrivals_mono ω (Nat.le_succ t) i
    simp only [hX, queue, Nat.add_sub_cancel]
    rw [Nat.cast_sub (hf.trans hm), cast_inc_sum]
    have : (arrivals ω t i : ℝ) ≤ (arrivals ω (t + 1) i : ℝ) := by exact_mod_cast hm
    linarith
  have hXdep : ∀ i ω ω', (∀ k < t, ω k = ω' k) → X i ω = X i ω' := by
    intro i ω ω' h
    simp only [hX]
    rw [arrivals_congr ω ω' t h, hD.2.2.1 t ω ω' h]
  have hQt := hQ (t + 1) (by omega)
  calc Rstar N lam r t - valueOf lam r D t
      = expect lam t (fun ω => staticOpt N r (arrivals ω t) - ∑ m, r m * (D t ω m : ℝ)) := by
        unfold Rstar valueOf; rw [expect_sub]
    _ ≤ expect lam t (fun ω => ∑ i ∈ Qzero s, θ i * X i ω) := expect_mono lam hlam t _ _ hpath1
    _ = ∑ i ∈ Qzero s, θ i * expect lam (t + 1) (X i) := by
        rw [expect_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [expect_const_mul, expect_succ lam hlam t (X i) (hXdep i)]
    _ ≤ ∑ i ∈ Qzero s, Θ * (C / gpGap z s) := by
        apply Finset.sum_le_sum
        intro i hi
        have e1 := expect_mono lam hlam (t + 1) _ _ (hpath2 i)
        have e2 := hQt i hi
        have e0 : 0 ≤ expect lam (t + 1) (fun ω => (queue N D ω (t + 1) i : ℝ)) := by
          have := expect_mono lam hlam (t + 1) (fun _ => (0 : ℝ))
            (fun ω => (queue N D ω (t + 1) i : ℝ)) (fun ω => Nat.cast_nonneg _)
          rwa [expect_zero] at this
        have hc : 0 ≤ C / gpGap z s := e0.trans e2
        calc θ i * expect lam (t + 1) (X i) ≤ θ i * (C / gpGap z s) :=
              mul_le_mul_of_nonneg_left (e1.trans e2) (hθ0 i)
          _ ≤ Θ * (C / gpGap z s) := mul_le_mul_of_nonneg_right (hθle i) hc
    _ = (Qzero s).card * (Θ * (C / gpGap z s)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (Θ * (C / gpGap z s)) := by
        have hc : 0 ≤ Θ * (C / gpGap z s) := mul_nonneg hΘ (div_nonneg hC (gpGap_nonneg z s))
        apply mul_le_mul_of_nonneg_right _ hc
        have : (Qzero s).card ≤ n := by
          calc (Qzero s).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
            _ = n := by simp
        exact_mod_cast this
    _ = n * Θ * C / gpGap z s := by ring
