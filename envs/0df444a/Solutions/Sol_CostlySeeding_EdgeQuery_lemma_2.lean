-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:19:33.114896+00:00
-- url     : https://prove2.me/submissions/96e18c7e-2d72-4a1a-943e-3a8082aab367

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

open CostlySeeding.EdgeQuery

namespace L2Aux

lemma percW_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Sym2 (Fin n))) :
    0 ≤ percW G p A := by
  unfold percW
  split_ifs
  · exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  · exact le_refl _

lemma sum_percW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) : ∑ A ∈ G.edgeFinset.powerset, percW G p A = 1 := by
  have h : ∀ A ∈ G.edgeFinset.powerset,
      percW G p A = p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) := by
    intro A hA
    unfold percW
    rw [if_pos (Finset.mem_powerset.1 hA)]
  rw [Finset.sum_congr rfl h, Finset.sum_pow_mul_eq_add_pow]
  simp

lemma phi_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (S : Finset (Fin n)) :
    0 ≤ phi G p v S := by
  unfold phi
  apply Finset.sum_nonneg
  intro A _
  apply mul_nonneg (percW_nonneg G p hp0 hp1 A)
  split_ifs <;> norm_num

lemma phi_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (S : Finset (Fin n)) :
    phi G p v S ≤ 1 := by
  unfold phi
  calc _ ≤ ∑ A ∈ G.edgeFinset.powerset, percW G p A := by
        apply Finset.sum_le_sum
        intro A _
        have := percW_nonneg G p hp0 hp1 A
        split_ifs <;> simp [this]
    _ = 1 := sum_percW G p

lemma Gam_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    0 ≤ Gam G p S :=
  Finset.sum_nonneg fun v _ => phi_nonneg G p hp0 hp1 v S

lemma Gam_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    Gam G p S ≤ n := by
  unfold Gam
  calc _ ≤ ∑ _v : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun v _ => phi_le_one G p hp0 hp1 v S
    _ = n := by simp


lemma hoeffding_finset {n : ℕ} (P : Finset (Fin n)) (hP : P.Nonempty) (y : Fin n → ℝ)
    (a b : ℝ) (hy : ∀ i ∈ P, a ≤ y i ∧ y i ≤ b) (h0 : ∑ i ∈ P, y i = 0) (t : ℝ) :
    ∑ i ∈ P, Real.exp (t * y i) ≤ P.card * Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  classical
  obtain ⟨i0, hi0⟩ := id hP
  have hab : a ≤ b := le_trans (hy i0 hi0).1 (hy i0 hi0).2
  set pm := PMF.uniformOfFinset P hP with hpm
  set μ := pm.toMeasure with hμ
  set X : Fin n → ℝ := fun i => if i ∈ P then y i else a with hX
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.2 ⟨i0, hi0⟩
  have hpmval : ∀ i, (pm i).toReal = if i ∈ P then 1 / (P.card : ℝ) else 0 := by
    intro i
    rw [hpm, PMF.uniformOfFinset_apply]
    split_ifs <;> simp
  have hint : ∀ g : Fin n → ℝ, ∫ i, g i ∂μ = (1 / (P.card : ℝ)) * ∑ i ∈ P, g i := by
    intro g
    rw [hμ, PMF.integral_eq_sum]
    simp only [hpmval, smul_eq_mul, ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum]
  have hmean : ∫ i, X i ∂μ = 0 := by
    rw [hint]
    have : ∑ i ∈ P, X i = ∑ i ∈ P, y i := Finset.sum_congr rfl fun i hi => by simp [hX, hi]
    rw [this, h0, mul_zero]
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b := by
    apply Filter.Eventually.of_forall
    intro ω
    simp only [hX]
    split_ifs with h
    · exact ⟨(hy ω h).1, (hy ω h).2⟩
    · exact ⟨le_refl a, hab⟩
  have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (Measurable.aemeasurable (measurable_of_finite X)) hb hmean
  have hm := hsg.mgf_le t
  rw [ProbabilityTheory.mgf, hint] at hm
  have hsum : ∑ i ∈ P, Real.exp (t * X i) = ∑ i ∈ P, Real.exp (t * y i) :=
    Finset.sum_congr rfl fun i hi => by simp [hX, hi]
  rw [hsum] at hm
  have hc : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) * t ^ 2 / 2 = (b - a) ^ 2 * t ^ 2 / 8 := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [hc] at hm
  rw [one_div, inv_mul_le_iff₀ hcard] at hm
  exact hm

/-! ### Double counting for `powersetCard` -/

lemma double_count {n : ℕ} (P : Finset (Fin n)) (m : ℕ) (F : Finset (Fin n) → ℝ) :
    ∑ i ∈ P, ∑ R ∈ (P.erase i).powersetCard m, F (insert i R) =
      (m + 1 : ℝ) * ∑ R ∈ P.powersetCard (m + 1), F R := by
  have h1 : ∑ R ∈ P.powersetCard (m + 1), ∑ _i ∈ R, F R =
      (m + 1 : ℝ) * ∑ R ∈ P.powersetCard (m + 1), F R := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    rw [Finset.sum_const, (Finset.mem_powersetCard.1 hR).2, nsmul_eq_mul]
    push_cast; ring
  rw [← h1]
  rw [Finset.sum_comm' (t' := P) (s' := fun i => (P.powersetCard (m + 1)).filter (fun R => i ∈ R))]
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_nbij' (fun R => insert i R) (fun R => R.erase i)
    · intro R hR
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hR
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      have hiR : i ∉ R := fun h => by
        have := hR.1 h; simp at this
      refine ⟨⟨Finset.insert_subset hi (hR.1.trans (Finset.erase_subset _ _)), ?_⟩,
        Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hiR, hR.2]
    · intro R hR
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hR
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨Finset.erase_subset_erase _ hR.1.1, ?_⟩
      rw [Finset.card_erase_of_mem hR.2, hR.1.2]; rfl
    · intro R hR
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hR
      have hiR : i ∉ R := fun h => by
        have := hR.1 h; simp at this
      exact Finset.erase_insert hiR
    · intro R hR
      simp only [Finset.mem_coe, Finset.mem_filter] at hR
      exact Finset.insert_erase hR.2
    · intro R _; rfl
  · intro R i
    simp only [Finset.mem_powersetCard, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hRP, hc⟩, hi⟩; exact ⟨⟨⟨hRP, hc⟩, hi⟩, hRP hi⟩
    · rintro ⟨⟨h, hi⟩, _⟩; exact ⟨h, hi⟩

/-! ### Hoeffding's inequality for sampling without replacement -/

lemma mgf_wo {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (l : ℝ) :
    ∀ (m : ℕ) (P : Finset (Fin n)), m ≤ P.card →
      ∑ R ∈ P.powersetCard m,
        Real.exp (l * (∑ i ∈ R, x i - m * ((∑ i ∈ P, x i) / P.card))) ≤
        (P.card.choose m : ℝ) * Real.exp (l ^ 2 * m / 8) := by
  intro m
  induction m with
  | zero =>
    intro P _
    simp
  | succ m ih =>
    intro P hP
    set N := P.card with hN
    set μ := (∑ i ∈ P, x i) / N with hμ
    have hNpos : 0 < N := by omega
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
    set c : ℝ := 1 - m / ((N : ℝ) - 1) with hc
    have hc0 : 0 ≤ c := by
      rw [hc, sub_nonneg]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · have : (m : ℝ) ≤ (N : ℝ) - 1 := by
          have : m + 1 ≤ N := hP
          have : ((m + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
          push_cast at this; linarith
        rw [div_le_one (by linarith [show (1 : ℝ) ≤ m by exact_mod_cast hpos])]
        exact this
    have hc1 : c ≤ 1 := by
      rw [hc]
      have : 0 ≤ (m : ℝ) / ((N : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · simp [h0]
        · apply div_nonneg (Nat.cast_nonneg _)
          have : m + 1 ≤ N := hP
          have : ((m + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
          push_cast at this; linarith
      linarith
    -- key algebraic identity for one removed element
    have hsplit : ∀ i ∈ P, ∀ R ∈ (P.erase i).powersetCard m,
        Real.exp (l * (∑ j ∈ insert i R, x j - ((m + 1 : ℕ) : ℝ) * μ)) =
          Real.exp (l * (c * (x i - μ))) *
          Real.exp (l * (∑ j ∈ R, x j - m * ((∑ j ∈ P.erase i, x j) / (P.erase i).card))) := by
      intro i hi R hR
      have hiR : i ∉ R := fun h => by
        have := (Finset.mem_powersetCard.1 hR).1 h; simp at this
      rw [← Real.exp_add, Finset.sum_insert hiR, Finset.card_erase_of_mem hi]
      congr 1
      have hsum : ∑ j ∈ P.erase i, x j = N * μ - x i := by
        rw [hμ, mul_div_cancel₀ _ hNR.ne', ← Finset.add_sum_erase P x hi]; ring
      rw [hsum]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        rw [Finset.mem_powersetCard] at hR
        rw [Finset.card_eq_zero.1 hR.2]
        simp [hc]
      · have hN2 : 2 ≤ N := by
          have : m + 1 ≤ N := hP
          omega
        have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hN1, hc]
        have hne : (N : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
          linarith
        field_simp
        push_cast
        ring
    have hstep : ∀ i ∈ P, ∑ R ∈ (P.erase i).powersetCard m,
        Real.exp (l * (∑ j ∈ insert i R, x j - ((m + 1 : ℕ) : ℝ) * μ)) ≤
          Real.exp (l * (c * (x i - μ))) *
            (((N - 1).choose m : ℝ) * Real.exp (l ^ 2 * m / 8)) := by
      intro i hi
      rw [Finset.sum_congr rfl (hsplit i hi), ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hcard : (P.erase i).card = N - 1 := Finset.card_erase_of_mem hi
      have := ih (P.erase i) (by rw [hcard]; omega)
      rw [hcard] at this
      rw [hcard]
      exact this
    have hhoef := hoeffding_finset P (Finset.card_pos.1 hNpos) (fun i => c * (x i - μ))
      (-(c * μ)) (c * (1 - μ)) (by
        intro i _
        have := hx i
        constructor <;> nlinarith) (by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hμ,
          mul_div_cancel₀ _ hNR.ne', sub_self, mul_zero]) l
    have hbnd : (c * (1 - μ) - -(c * μ)) ^ 2 * l ^ 2 / 8 ≤ l ^ 2 / 8 := by
      have : (c * (1 - μ) - -(c * μ)) ^ 2 = c ^ 2 := by ring
      rw [this]
      have : c ^ 2 ≤ 1 := by nlinarith
      have : 0 ≤ l ^ 2 := sq_nonneg l
      nlinarith
    have hhoef2 : ∑ i ∈ P, Real.exp (l * (c * (x i - μ))) ≤ N * Real.exp (l ^ 2 / 8) :=
      hhoef.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hbnd) (Nat.cast_nonneg _))
    -- combine
    have hdc := double_count P m (fun R =>
      Real.exp (l * (∑ j ∈ R, x j - ((m + 1 : ℕ) : ℝ) * μ)))
    have hsum := Finset.sum_le_sum hstep
    rw [hdc, ← Finset.sum_mul] at hsum
    have hchoose : (N : ℝ) * ((N - 1).choose m : ℝ) = (N.choose (m + 1) : ℝ) * (m + 1) := by
      have := Nat.add_one_mul_choose_eq (N - 1) m
      rw [show N - 1 + 1 = N by omega] at this
      exact_mod_cast this
    have hpos : (0 : ℝ) < m + 1 := by positivity
    have : (m + 1 : ℝ) * ∑ R ∈ P.powersetCard (m + 1),
        Real.exp (l * (∑ j ∈ R, x j - ((m + 1 : ℕ) : ℝ) * μ)) ≤
        (m + 1 : ℝ) * ((N.choose (m + 1) : ℝ) * Real.exp (l ^ 2 * ((m + 1 : ℕ) : ℝ) / 8)) := by
      calc _ ≤ _ := hsum
        _ ≤ N * Real.exp (l ^ 2 / 8) * (((N - 1).choose m : ℝ) * Real.exp (l ^ 2 * m / 8)) :=
          mul_le_mul_of_nonneg_right hhoef2 (by positivity)
        _ = ((N : ℝ) * ((N - 1).choose m : ℝ)) * (Real.exp (l ^ 2 / 8) * Real.exp (l ^ 2 * m / 8)) := by
          ring
        _ = _ := by
          rw [hchoose, ← Real.exp_add]; push_cast; ring_nf
    exact le_of_mul_le_mul_left this hpos

/-! ### Tail bounds -/

lemma tail_upper {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (m : ℕ) (hm : 0 < m)
    (hmn : m ≤ n) (s : ℝ) (hs : 0 < s) :
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun R => s ≤ ∑ i ∈ R, x i - m * ((∑ i, x i) / n))).card : ℝ) ≤
      (n.choose m : ℝ) * Real.exp (-2 * s ^ 2 / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set l := 4 * s / m with hl
  have hl0 : 0 < l := by positivity
  have hmgf := mgf_wo x hx l m Finset.univ (by simpa using hmn)
  simp only [Finset.card_univ, Fintype.card_fin] at hmgf
  set F := fun R : Finset (Fin n) => ∑ i ∈ R, x i - m * ((∑ i, x i) / n) with hF
  have h1 : (((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun R => s ≤ F R)).card
      ≤ ∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          Real.exp (l * F R) * Real.exp (-(l * s)) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    calc _ = ∑ R ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun R => s ≤ F R),
          (1 : ℝ) := by simp
      _ ≤ ∑ R ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun R => s ≤ F R),
          Real.exp (l * F R) * Real.exp (-(l * s)) := by
        apply Finset.sum_le_sum
        intro R hR
        have hR' := (Finset.mem_filter.1 hR).2
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
  rw [← Finset.sum_mul] at h1
  calc _ ≤ _ := h1
    _ ≤ (n.choose m : ℝ) * Real.exp (l ^ 2 * m / 8) * Real.exp (-(l * s)) :=
        mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = (n.choose m : ℝ) * Real.exp (-2 * s ^ 2 / m) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        rw [hl]; field_simp; ring

lemma tail_lower {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (m : ℕ) (hm : 0 < m)
    (hmn : m ≤ n) (s : ℝ) (hs : 0 < s) :
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun R => s ≤ m * ((∑ i, x i) / n) - ∑ i ∈ R, x i)).card : ℝ) ≤
      (n.choose m : ℝ) * Real.exp (-2 * s ^ 2 / m) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := tail_upper (fun i => 1 - x i) (fun i => ⟨by linarith [(hx i).2], by linarith [(hx i).1]⟩)
    m hm hmn s hs
  convert h using 4
  rename_i R hR
  have hc := (Finset.mem_powersetCard.1 hR).2
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, hc]
  have : (m : ℝ) * ((n - ∑ i, x i) / n) = m - m * ((∑ i, x i) / n) := by
    field_simp
  constructor <;> intro h' <;> linarith

/-! ### Numerics -/

lemma log_five : (1.594 : ℝ) < Real.log 5 := by
  have h2 := Real.log_two_gt_d9
  have h : (2 : ℝ) ^ 23 < 5 ^ 10 := by norm_num
  have := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

lemma num_core (D eps a m : ℝ) (heps : 0 < eps) (hD5 : 5.3 ≤ D)
    (hρ' : (2 + eps) * D / (2 * eps ^ 2) ≤ a) (hmR : 0 < m) (hm2 : m < a + 1) :
    0 < eps * a - 1 ∧ D ≤ 2 * (eps * a - 1) ^ 2 / m := by
  have hb1 : (2 + eps) * D ≤ 2 * eps * (eps * a) := by
    rw [div_le_iff₀ (by positivity)] at hρ'
    nlinarith
  generalize hb : eps * a = b at hb1 ⊢
  have ha' : a = b / eps := by rw [← hb]; field_simp
  generalize hu : b - D / 2 = u
  have hbu : b = u + D / 2 := by rw [← hu]; ring
  subst hbu
  have hu1 : D ≤ eps * u := by nlinarith
  have hu0 : 0 < u := by
    by_contra h
    push Not at h
    have : eps * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos heps.le h
    linarith
  have hs0 : 0 < u + D / 2 - 1 := by linarith
  refine ⟨hs0, ?_⟩
  have hQ : u * (u + D / 2) ≤ 2 * (u + D / 2 - 1) ^ 2 - D := by
    have e : 2 * (u + D / 2 - 1) ^ 2 - D - u * (u + D / 2) =
        D ^ 2 / 2 - 3 * D + 2 + u ^ 2 + (3 * D / 2 - 4) * u := by ring
    have : 0 ≤ D ^ 2 / 2 - 3 * D + 2 := by nlinarith
    have : 0 ≤ (3 * D / 2 - 4) * u := mul_nonneg (by linarith) hu0.le
    nlinarith
  have hbpos : 0 < u + D / 2 := by linarith
  have h1 : D * (u + D / 2) ≤ eps * (2 * (u + D / 2 - 1) ^ 2 - D) := by
    have h1a : D * (u + D / 2) ≤ eps * u * (u + D / 2) :=
      mul_le_mul_of_nonneg_right hu1 hbpos.le
    have h1b : eps * (u * (u + D / 2)) ≤ eps * (2 * (u + D / 2 - 1) ^ 2 - D) :=
      mul_le_mul_of_nonneg_left hQ heps.le
    linarith [show eps * u * (u + D / 2) = eps * (u * (u + D / 2)) by ring]
  have hkey : D * (a + 1) ≤ 2 * (u + D / 2 - 1) ^ 2 := by
    rw [ha']
    have : D * ((u + D / 2) / eps + 1) * eps = D * (u + D / 2) + D * eps := by
      field_simp
    have h3 : D * ((u + D / 2) / eps + 1) * eps ≤ 2 * (u + D / 2 - 1) ^ 2 * eps := by
      rw [this]; linarith
    exact le_of_mul_le_mul_right h3 heps
  rw [le_div_iff₀ hmR]
  have : D * m ≤ D * (a + 1) := mul_le_mul_of_nonneg_left hm2.le (by linarith)
  linarith

lemma K_le_D (L δ k : ℝ) (hL : 1.594 < L) (hk : 1 ≤ k) (hδ : 2 * L ≤ δ) :
    δ + k * L ≤ δ * k * L := by
  have hkL : L ≤ k * L := le_mul_of_one_le_left (by linarith) hk
  have h1 : 0 ≤ k * L - 1 := by linarith
  have h2 : 2 * L * (k * L - 1) ≤ δ * (k * L - 1) := mul_le_mul_of_nonneg_right hδ h1
  have h3 : L * (2 * L - 1) ≤ k * L * (2 * L - 1) :=
    mul_le_mul_of_nonneg_right hkL (by linarith)
  have h4 : 0 ≤ L * (2 * L - 3) := mul_nonneg (by linarith) (by linarith)
  have e1 : δ * k * L = δ * (k * L - 1) + δ := by ring
  nlinarith

lemma numerics (n k : ℕ) (hk : 1 ≤ k) (hn : 5 ≤ n) (eps δ ρ : ℝ) (heps : 0 < eps)
    (hδ : 2 * Real.log n ≤ δ) (hρ : rhoPar n k eps δ ≤ ρ) (m : ℕ) (hm0 : 0 < m)
    (hm2 : (m : ℝ) < n * ρ + 1) :
    0 < eps * ρ * n - 1 ∧
      2 * (n.choose k : ℝ) * Real.exp (-2 * (eps * ρ * n - 1) ^ 2 / m) ≤ Real.exp (-δ) := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hL5 : (1.594 : ℝ) < Real.log n := by
    have := Real.log_le_log (by norm_num) hnR
    linarith [log_five]
  have hlog2 := Real.log_two_gt_d9
  have hδL : 2 * Real.log n * Real.log n ≤ δ * k * Real.log n := by
    have h0 : 0 ≤ Real.log n := by linarith
    have : 2 * Real.log n ≤ δ * k := by
      have : δ ≤ δ * k := le_mul_of_one_le_right (by linarith) hkR
      linarith
    exact mul_le_mul_of_nonneg_right this h0
  have hD5 : (5.3 : ℝ) ≤ δ * k * Real.log n + Real.log 2 := by nlinarith
  have hρ' : (2 + eps) * (δ * k * Real.log n + Real.log 2) / (2 * eps ^ 2) ≤ n * ρ := by
    have h := hρ
    unfold rhoPar at h
    rw [div_le_iff₀ (by positivity)] at h
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨hs0, hkey⟩ := num_core _ eps (n * ρ) m heps hD5 hρ' hmR hm2
  have hs : eps * ρ * n - 1 = eps * (n * ρ) - 1 := by ring
  rw [hs]
  refine ⟨hs0, ?_⟩
  have hK := K_le_D (Real.log n) δ k hL5 hkR hδ
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
  have hnk : Real.exp (k * Real.log n) = (n : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hnpos]
  have hfinal : 2 * (n : ℝ) ^ k * Real.exp (-(δ + k * Real.log n + Real.log 2)) =
      Real.exp (-δ) := by
    rw [show -(δ + k * Real.log n + Real.log 2) = -δ + (-(k * Real.log n) + -Real.log 2) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg (k * Real.log n), Real.exp_neg (Real.log 2), hnk,
      Real.exp_log (by norm_num)]
    have : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    field_simp
  have hexp : -2 * (eps * (n * ρ) - 1) ^ 2 / m ≤ -(δ + k * Real.log n + Real.log 2) := by
    have : -2 * (eps * (n * ρ) - 1) ^ 2 / m = -(2 * (eps * (n * ρ) - 1) ^ 2 / m) := by ring
    rw [this]
    linarith
  calc 2 * (n.choose k : ℝ) * Real.exp (-2 * (eps * (n * ρ) - 1) ^ 2 / m)
      ≤ 2 * (n : ℝ) ^ k * Real.exp (-(δ + k * Real.log n + Real.log 2)) := by
        apply mul_le_mul (by linarith) (Real.exp_le_exp.2 hexp) (by positivity) (by positivity)
    _ = Real.exp (-δ) := hfinal

end L2Aux

theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps delta rho : ℝ) (heps : 0 < eps) (hdelta : 2 * Real.log n ≤ delta)
    (hrho0 : 0 < rho) (hrho : rhoPar n k eps delta ≤ rho) (hrho1 : rho ≤ 1) :
    1 - Real.exp (-delta) ≤
      initialEventProb n (Nat.ceil ((n : ℝ) * rho)) (fun Vrho =>
        ∀ S : Finset (Fin n), S.card = k →
          |GamRho G p Vrho rho S - Gam G p S| ≤ eps * n) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set m := Nat.ceil ((n : ℝ) * rho) with hm
  have hm1 : (n : ℝ) * rho ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < n * rho + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm0 : 0 < m := Nat.ceil_pos.2 (by positivity)
  have hmn : m ≤ n := by
    apply Nat.ceil_le.2
    have := mul_le_mul_of_nonneg_left hrho1 hnpos.le
    linarith
  obtain ⟨hs0, hnum⟩ := L2Aux.numerics n k hk hn eps delta rho heps hdelta hrho m hm0 hm2
  set s := eps * rho * n - 1 with hs
  set e := Real.exp (-2 * s ^ 2 / m) with he
  set C := (Finset.univ : Finset (Fin n)).powersetCard m with hC
  have hCcard : (C.card : ℝ) = n.choose m := by
    rw [hC, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hcpos : (0 : ℝ) < C.card := by
    rw [hCcard]; exact_mod_cast Nat.choose_pos hmn
  set P : Finset (Fin n) → Prop := fun Vrho => ∀ S : Finset (Fin n), S.card = k →
      |GamRho G p Vrho rho S - Gam G p S| ≤ eps * n with hP
  set x : Finset (Fin n) → Fin n → ℝ := fun S v => phi G p v S with hx
  have hxb : ∀ S v, 0 ≤ x S v ∧ x S v ≤ 1 := fun S v =>
    ⟨L2Aux.phi_nonneg G p hp0 hp1 v S, L2Aux.phi_le_one G p hp0 hp1 v S⟩
  set up : Finset (Fin n) → Finset (Finset (Fin n)) := fun S =>
    C.filter (fun R => s ≤ ∑ i ∈ R, x S i - m * ((∑ i, x S i) / n)) with hup
  set lo : Finset (Fin n) → Finset (Finset (Fin n)) := fun S =>
    C.filter (fun R => s ≤ m * ((∑ i, x S i) / n) - ∑ i ∈ R, x S i) with hlo
  -- bad sets are covered
  have hcover : C.filter (fun V => ¬ P V) ⊆
      ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion (fun S => up S ∪ lo S) := by
    intro V hV
    rw [Finset.mem_filter] at hV
    obtain ⟨hVC, hbad⟩ := hV
    simp only [hP, not_forall] at hbad
    obtain ⟨S, hSk, hS⟩ := hbad
    rw [Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hSk⟩, ?_⟩
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hG0 : 0 ≤ Gam G p S := L2Aux.Gam_nonneg G p hp0 hp1 S
    have hGn : Gam G p S ≤ n := L2Aux.Gam_le G p hp0 hp1 S
    have hGsum : Gam G p S = ∑ i, x S i := rfl
    have hRho : GamRho G p V rho S = (1 / rho) * ∑ i ∈ V, x S i := rfl
    rw [hRho, hGsum] at hS
    rw [hGsum] at hG0 hGn
    set X := ∑ i ∈ V, x S i
    set Γ := ∑ i, x S i
    have hμ : 0 ≤ (m - n * rho) * (Γ / n) ∧ (m - n * rho) * (Γ / n) ≤ 1 := by
      have h1 : 0 ≤ Γ / n := div_nonneg hG0 hnpos.le
      have h2 : Γ / n ≤ 1 := by rw [div_le_one hnpos]; exact hGn
      constructor
      · exact mul_nonneg (by linarith) h1
      · have : (m - n * rho) * (Γ / n) ≤ 1 * 1 :=
          mul_le_mul (by linarith) h2 h1 (by norm_num)
        linarith
    have hsplit : (m : ℝ) * (Γ / n) = rho * Γ + (m - n * rho) * (Γ / n) := by
      field_simp; ring
    rw [not_le, lt_abs] at hS
    rcases hS with h | h
    · left
      refine ⟨hVC, ?_⟩
      have : eps * rho * n < X - rho * Γ := by
        have h' : eps * n * rho < (1 / rho * X - Γ) * rho := mul_lt_mul_of_pos_right h hrho0
        have : (1 / rho * X - Γ) * rho = X - rho * Γ := by field_simp
        linarith
      rw [hs]; linarith
    · right
      refine ⟨hVC, ?_⟩
      have : eps * rho * n < rho * Γ - X := by
        have h' : eps * n * rho < (-(1 / rho * X - Γ)) * rho := mul_lt_mul_of_pos_right h hrho0
        have : (-(1 / rho * X - Γ)) * rho = rho * Γ - X := by field_simp; ring
        linarith
      rw [hs]; linarith
  have hbadcard : ((C.filter (fun V => ¬ P V)).card : ℝ) ≤
      (n.choose k : ℝ) * (2 * ((n.choose m : ℝ) * e)) := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)).powersetCard k)
      (t := fun S => up S ∪ lo S)
    have h3 : ∀ S, ((up S ∪ lo S).card : ℝ) ≤ 2 * ((n.choose m : ℝ) * e) := by
      intro S
      have hu := L2Aux.tail_upper (x S) (hxb S) m hm0 hmn s hs0
      have hl := L2Aux.tail_lower (x S) (hxb S) m hm0 hmn s hs0
      have hun : ((up S ∪ lo S).card : ℝ) ≤ (up S).card + (lo S).card := by
        exact_mod_cast Finset.card_union_le _ _
      have : ((up S).card : ℝ) ≤ (n.choose m : ℝ) * e := hu
      have : ((lo S).card : ℝ) ≤ (n.choose m : ℝ) * e := hl
      linarith
    calc ((C.filter (fun V => ¬ P V)).card : ℝ)
        ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ((up S ∪ lo S).card : ℝ) := by
          exact_mod_cast h1.trans h2
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 2 * ((n.choose m : ℝ) * e) :=
          Finset.sum_le_sum fun S _ => h3 S
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  -- the probability
  unfold initialEventProb
  simp only
  rw [← hC]
  have hsum : ∑ V ∈ C, 1 / (C.card : ℝ) * (if P V then 1 else 0) =
      1 / (C.card : ℝ) * (C.filter P).card := by
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [hsum]
  have hsplit := Finset.card_filter_add_card_filter_not (s := C) P
  have hgood : ((C.filter P).card : ℝ) = C.card - (C.filter (fun V => ¬ P V)).card := by
    rw [← hsplit]; push_cast; ring
  rw [hgood]
  rw [hCcard] at hcpos ⊢
  have hfin : 1 - (n.choose k : ℝ) * (2 * e) ≤
      1 / (n.choose m : ℝ) * ((n.choose m : ℝ) - (C.filter (fun V => ¬ P V)).card) := by
    have e1 : 1 / (n.choose m : ℝ) * ((n.choose m : ℝ) - (C.filter (fun V => ¬ P V)).card) =
        1 - ((C.filter (fun V => ¬ P V)).card : ℝ) / (n.choose m : ℝ) := by
      field_simp
    rw [e1]
    have : ((C.filter (fun V => ¬ P V)).card : ℝ) / (n.choose m : ℝ) ≤
        (n.choose k : ℝ) * (2 * e) := by
      rw [div_le_iff₀ hcpos]
      nlinarith
    linarith
  have : 2 * (n.choose k : ℝ) * e ≤ Real.exp (-delta) := hnum
  linarith

