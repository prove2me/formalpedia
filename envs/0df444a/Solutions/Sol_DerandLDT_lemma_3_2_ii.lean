-- Prove2me | solution 1 for DerandLDT.lemma_3_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T14:12:42.877109+00:00
-- url     : https://prove2.me/submissions/423c4d48-6969-431b-b4db-e9578fae81e9

import Mathlib

set_option autoImplicit false

theorem solution : ∀ p k D : ℕ, 1 ≤ k → 20 * k < D → 2 ≤ p →
    (D : ℝ) ^ 3 / (12 * k) <
      (((Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
        fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + k * m.2.2 ≤ D ∧ (m.2.2 = 0 ∨ ¬ p ∣ m.2.2)).card : ℝ) := by
  intro p k D hk hD hp
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDR : (20 : ℝ) * (k : ℝ) < (D : ℝ) := by exact_mod_cast hD
  let T : Finset (ℕ × ℕ × ℕ) :=
    (Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
      (fun m : ℕ × ℕ × ℕ => m.1 + m.2.1 + k * m.2.2 ≤ D ∧ (m.2.2 = 0 ∨ ¬ p ∣ m.2.2))
  let pair : ℕ → Finset (ℕ × ℕ) := fun R =>
    (Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter (fun m : ℕ × ℕ => m.1 + m.2 ≤ R)
  let tri : ℕ → ℕ := fun R => (pair R).card
  have htri2 : ∀ R ≤ D, 2 * tri R = (R + 1) * (R + 2) := by
    intro R hRD
    have h1 : pair R = (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).filter
        (fun m : ℕ × ℕ => m.1 + m.2 ≤ R) := by
      ext m
      obtain ⟨i, j⟩ := m
      simp only [pair, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    have h2 : (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).filter
        (fun m : ℕ × ℕ => m.1 + m.2 ≤ R)
        = (Finset.range (R + 1)).biUnion (fun k => Finset.HasAntidiagonal.antidiagonal k) := by
      ext m
      obtain ⟨i, j⟩ := m
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion,
        Finset.HasAntidiagonal.mem_antidiagonal]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨i + j, by omega, by omega⟩
      · rintro ⟨a, ha, hsum⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    have htri_eq : tri R = ((Finset.range (R + 1)).biUnion (fun k => Finset.HasAntidiagonal.antidiagonal k)).card := by
      rw [show tri R = (pair R).card from rfl, h1, h2]
    rw [htri_eq]
    rw [Finset.card_biUnion (t := fun k => Finset.HasAntidiagonal.antidiagonal k)]
    · have hsum : ∀ n, 2 * (∑ k ∈ Finset.range (n + 1), (k + 1)) = (n + 1) * (n + 2) := by
        intro n
        induction n with
        | zero => simp
        | succ m ih =>
            rw [Finset.sum_range_succ, mul_add, ih]
            ring
      rw [Finset.sum_congr rfl (fun k _ => Finset.Nat.card_antidiagonal k)]
      exact hsum R
    · intro a _ c _ hab
      refine Finset.disjoint_left.2 (fun m hm hm' => ?_)
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hm hm'
      exact hab (by omega)
  let L := D / k
  let M := L / 2
  let idx : ℕ → ℕ := fun m => if p ∣ 2 * m + 2 then 2 * m + 1 else 2 * m + 2
  have hidx_lower : ∀ m, 2 * m + 1 ≤ idx m := by
    intro m
    simp only [idx]
    split_ifs <;> omega
  have hidx_le : ∀ m, idx m ≤ 2 * m + 2 := by
    intro m
    simp only [idx]
    split_ifs <;> omega
  have hidx_pos : ∀ m, 1 ≤ idx m := by
    intro m
    have := hidx_lower m
    omega
  have hidx_ndvd : ∀ m, ¬ p ∣ idx m := by
    intro m
    simp only [idx]
    split_ifs with h
    · intro hdvd
      have hsub : p ∣ (2 * m + 2) - (2 * m + 1) := Nat.dvd_sub h hdvd
      rw [show 2 * m + 2 - (2 * m + 1) = 1 by omega] at hsub
      have hp1 : p = 1 := Nat.dvd_one.mp hsub
      omega
    · exact h
  have hM_le : 2 * M ≤ L := Nat.mul_div_le L 2
  have hM_ge : L ≤ 2 * M + 1 := by
    have hdiv : 2 * (L / 2) + L % 2 = L := Nat.div_add_mod L 2
    have hmod : L % 2 < 2 := Nat.mod_lt L (by norm_num)
    have h : M = L / 2 := rfl
    omega
  have hkL : k * L ≤ D := Nat.mul_div_le D k
  have hD_lt : D < k * (L + 1) := by
    have hdiv : k * L + D % k = D := by
      rw [show L = D / k from rfl]
      exact Nat.div_add_mod D k
    have hmod : D % k < k := Nat.mod_lt D (by omega)
    have hkp : k * (L + 1) = k * L + k := by ring
    omega
  have hidx_kD : ∀ m ∈ Finset.range M, k * idx m ≤ D := by
    intro m hm
    have hm' : m < M := Finset.mem_range.mp hm
    have h1 : idx m ≤ 2 * M := by
      have := hidx_le m
      omega
    calc k * idx m ≤ k * (2 * M) := Nat.mul_le_mul_left k h1
      _ ≤ k * L := Nat.mul_le_mul_left k hM_le
      _ ≤ D := hkL
  let S : Finset ℕ := insert 0 ((Finset.range M).image idx)
  have hidx_inj : ∀ a ∈ Finset.range M, ∀ b ∈ Finset.range M, idx a = idx b → a = b := by
    intro a _ b _ hab
    have ha1 := hidx_lower a
    have ha2 := hidx_le a
    have hb1 := hidx_lower b
    have hb2 := hidx_le b
    by_contra h
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt <;> omega
  have hzero_not : 0 ∉ (Finset.range M).image idx := by
    simp only [Finset.mem_image]
    rintro ⟨m, -, hm⟩
    have := hidx_pos m
    omega
  have hS_props : ∀ ℓ ∈ S, ℓ ≤ D ∧ k * ℓ ≤ D ∧ (ℓ = 0 ∨ ¬ p ∣ ℓ) := by
    intro ℓ hℓ
    simp only [S, Finset.mem_insert, Finset.mem_image] at hℓ
    rcases hℓ with rfl | ⟨m, hm, rfl⟩
    · exact ⟨by simp, by simp, Or.inl rfl⟩
    · have hkℓ := hidx_kD m hm
      have hpos := hidx_pos m
      have hle : idx m ≤ k * idx m := Nat.le_mul_of_pos_left _ (by omega : 0 < k)
      exact ⟨by omega, hkℓ, Or.inr (hidx_ndvd m)⟩
  have hSsub : S ⊆ Finset.range (D + 1) := by
    intro ℓ hℓ
    obtain ⟨hℓD, -, -⟩ := hS_props ℓ hℓ
    simpa using hℓD
  have hfiber_lb : ∀ ℓ ∈ S, tri (D - k * ℓ) ≤
      (T.filter (fun m : ℕ × ℕ × ℕ => m.2.2 = ℓ)).card := by
    intro ℓ hℓS
    obtain ⟨hℓD, hkℓD, hℓp⟩ := hS_props ℓ hℓS
    have hsub : ((pair (D - k * ℓ)).image (fun m : ℕ × ℕ => (m.1, m.2, ℓ)))
        ⊆ T.filter (fun m : ℕ × ℕ × ℕ => m.2.2 = ℓ) := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨⟨i, j⟩, hpp, rfl⟩ := hx
      simp only [pair, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpp
      obtain ⟨⟨hi, hj⟩, hsum⟩ := hpp
      have hmT : (i, j, ℓ) ∈
          (Finset.range (D + 1) ×ˢ Finset.range (D + 1) ×ˢ Finset.range (D + 1)) := by
        rw [Finset.mem_product, Finset.mem_product]
        exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hℓD)⟩
      have hdeg : i + j + k * ℓ ≤ D := by
        calc i + j + k * ℓ ≤ (D - k * ℓ) + k * ℓ := Nat.add_le_add_right hsum _
          _ = D := Nat.sub_add_cancel hkℓD
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hmT, hdeg, hℓp⟩, rfl⟩
    calc tri (D - k * ℓ)
        = ((pair (D - k * ℓ)).image (fun m : ℕ × ℕ => (m.1, m.2, ℓ))).card := by
          rw [Finset.card_image_of_injOn]
          intro a _ b _ hab
          have h1 : a.1 = b.1 := congrArg (fun z : ℕ × ℕ × ℕ => z.1) hab
          have h2 : a.2 = b.2 := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) hab
          exact Prod.ext h1 h2
      _ ≤ _ := Finset.card_le_card hsub
  have hfiber_sum : T.card =
      ∑ ℓ ∈ Finset.range (D + 1), (T.filter (fun m : ℕ × ℕ × ℕ => m.2.2 = ℓ)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro m hm
    have hm' : m ∈ T := hm
    dsimp only [T] at hm'
    rw [Finset.mem_filter] at hm'
    rw [Finset.mem_product, Finset.mem_product] at hm'
    exact hm'.1.2.2
  have hsum_lb : ∑ ℓ ∈ S, tri (D - k * ℓ) ≤ T.card := by
    calc ∑ ℓ ∈ S, tri (D - k * ℓ)
        ≤ ∑ ℓ ∈ S, (T.filter (fun m : ℕ × ℕ × ℕ => m.2.2 = ℓ)).card :=
          Finset.sum_le_sum hfiber_lb
      _ ≤ ∑ ℓ ∈ Finset.range (D + 1),
            (T.filter (fun m : ℕ × ℕ × ℕ => m.2.2 = ℓ)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (by simp)
      _ = T.card := hfiber_sum.symm
  have hS_sum : ∑ ℓ ∈ S, tri (D - k * ℓ)
      = tri D + ∑ m ∈ Finset.range M, tri (D - k * idx m) := by
    have hS_eq : S = insert 0 ((Finset.range M).image idx) := rfl
    rw [hS_eq, Finset.sum_insert hzero_not, Finset.sum_image hidx_inj]
    simp
  have hLge : 20 ≤ L := by
    have h : L = D / k := rfl
    rw [h]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
    omega
  have hMpos : 1 ≤ M := by
    have h : M = L / 2 := rfl
    rw [h]
    exact Nat.div_pos (by omega) (by norm_num)
  set b : ℕ → ℝ := fun m => (D : ℝ) - (k : ℝ) * (2 * m + 2) with hb
  have hb_nonneg : ∀ m < M, 0 ≤ b m := by
    intro m hm
    have h2m : 2 * m + 2 ≤ L := by omega
    have h1 : (k : ℝ) * (2 * m + 2) ≤ (k : ℝ) * L :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h2m) hkR.le
    have h2 : (k : ℝ) * L ≤ (D : ℝ) := by exact_mod_cast hkL
    simp only [hb]
    linarith
  have hb_ge : ∀ m, m + 2 ≤ M → 2 * (k : ℝ) ≤ b m := by
    intro m hm
    have h2m : 2 * m + 4 ≤ L := by omega
    have h1 : (k : ℝ) * (2 * m + 4) ≤ (k : ℝ) * L :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h2m) hkR.le
    have h2 : (k : ℝ) * L ≤ (D : ℝ) := by exact_mod_cast hkL
    simp only [hb]
    push_cast
    linarith
  have hb_step : ∀ m, b (m + 1) = b m - 2 * (k : ℝ) := by
    intro m
    simp only [hb]
    push_cast
    ring
  have hb_last : b (M - 1) < 2 * (k : ℝ) := by
    have h1 : (L : ℝ) + 1 ≤ 2 * (M : ℝ) + 2 := by
      have h : L + 1 ≤ 2 * M + 2 := by omega
      exact_mod_cast h
    have h2 : (k : ℝ) * ((L : ℝ) + 1) ≤ (k : ℝ) * (2 * (M : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left h1 hkR.le
    have h4 : (D : ℝ) < (k : ℝ) * ((L : ℝ) + 1) := by exact_mod_cast hD_lt
    have h3 : (D : ℝ) < (k : ℝ) * (2 * (M : ℝ) + 2) := by linarith
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hMpos]
      norm_num
    have hcastM : 2 * ((M - 1 : ℕ) : ℝ) + 2 = 2 * (M : ℝ) := by
      rw [hM1]
      ring
    simp only [hb]
    rw [hcastM]
    linarith
  have htele : ∀ n, n + 1 ≤ M →
      ∑ m ∈ Finset.range n, (b m) ^ 2 ≥ ((b 0) ^ 3 - (b n) ^ 3) / (6 * (k : ℝ)) := by
    intro n hn
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have ih' := ih (by omega)
        have hbm : 2 * (k : ℝ) ≤ b m := hb_ge m (by omega)
        have hstep : ((b m) ^ 3 - (b (m + 1)) ^ 3) / (6 * (k : ℝ)) ≤ (b m) ^ 2 := by
          rw [hb_step m]
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * (k : ℝ))]
          have hexp : (b m) ^ 3 - (b m - 2 * (k : ℝ)) ^ 3
              = 6 * (k : ℝ) * (b m) ^ 2 - 12 * (k : ℝ) ^ 2 * (b m) + 8 * (k : ℝ) ^ 3 := by
            ring
          have hkey : 8 * (k : ℝ) ^ 3 ≤ 12 * (k : ℝ) ^ 2 * (b m) := by nlinarith [hbm, hkR]
          nlinarith [hexp, hkey]
        have hcomb : ((b 0) ^ 3 - (b m) ^ 3) / (6 * (k : ℝ))
            + ((b m) ^ 3 - (b (m + 1)) ^ 3) / (6 * (k : ℝ))
            = ((b 0) ^ 3 - (b (m + 1)) ^ 3) / (6 * (k : ℝ)) := by
          rw [← add_div]
          ring
        linarith [ih', hstep, hcomb]
  have hkey_mul : (D : ℝ) ^ 3 <
      (((D : ℝ) + 1) * ((D : ℝ) + 2) / 2) * (12 * (k : ℝ))
        + (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) := by
    have hexp : ((D : ℝ) - 2 * (k : ℝ)) ^ 3
        = (D : ℝ) ^ 3 - 6 * (D : ℝ) ^ 2 * (k : ℝ) + 12 * (D : ℝ) * (k : ℝ) ^ 2
          - 8 * (k : ℝ) ^ 3 := by ring
    rw [hexp]
    nlinarith [hkR, hDR]
  have hkey : (D : ℝ) ^ 3 / (12 * k) <
      ((D : ℝ) + 1) * ((D : ℝ) + 2) / 2
        + (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (12 * (k : ℝ)) := by
    have hk0 : (0 : ℝ) < 12 * (k : ℝ) := by linarith
    rw [div_lt_iff₀ hk0]
    have heq : (((D : ℝ) + 1) * ((D : ℝ) + 2) / 2
          + (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (12 * (k : ℝ)))
          * (12 * (k : ℝ))
        = (((D : ℝ) + 1) * ((D : ℝ) + 2) / 2) * (12 * (k : ℝ))
          + (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) := by
      field_simp
    rw [heq]
    exact hkey_mul
  have htriD : ((D : ℝ) + 1) * ((D : ℝ) + 2) / 2 ≤ (tri D : ℝ) := by
    have h := htri2 D le_rfl
    have hcast : (2 : ℝ) * (tri D : ℝ) = ((D + 1) * (D + 2) : ℕ) := by
      exact_mod_cast h
    have h2 : (2 : ℝ) * (tri D : ℝ) = ((D : ℝ) + 1) * ((D : ℝ) + 2) := by
      rw [hcast]
      push_cast
      ring
    linarith
  have hsum2 : ∑ m ∈ Finset.range M, ((b m) ^ 2 / 2) ≤
      ∑ m ∈ Finset.range M, (tri (D - k * idx m) : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    have hm' : m < M := Finset.mem_range.mp hm
    have hkℓ : k * idx m ≤ D := hidx_kD m hm
    have hRle : D - k * idx m ≤ D := Nat.sub_le _ _
    have htri := htri2 (D - k * idx m) hRle
    have htri_lb : ((D - k * idx m : ℕ) : ℝ) ^ 2 / 2 ≤ (tri (D - k * idx m) : ℝ) := by
      have hcast : (2 : ℝ) * (tri (D - k * idx m) : ℝ)
          = (((D - k * idx m) + 1) * ((D - k * idx m) + 2) : ℕ) := by
        exact_mod_cast htri
      have hsq : ((D - k * idx m : ℕ) : ℝ) ^ 2 ≤ (2 : ℝ) * (tri (D - k * idx m) : ℝ) := by
        rw [hcast]
        push_cast
        nlinarith [Nat.zero_le (D - k * idx m)]
      linarith
    have hcast_sub : ((D - k * idx m : ℕ) : ℝ) = (D : ℝ) - (k : ℝ) * (idx m) := by
      rw [Nat.cast_sub hkℓ]
      push_cast
      ring
    have hidxle : (idx m : ℝ) ≤ 2 * (m : ℝ) + 2 := by
      exact_mod_cast hidx_le m
    have hbb : b m ≤ (D - k * idx m : ℕ) := by
      rw [hcast_sub]
      simp only [hb]
      push_cast
      nlinarith [hidxle, hkR.le]
    have hbnn : 0 ≤ b m := hb_nonneg m hm'
    have hstep : (b m) ^ 2 / 2 ≤ ((D - k * idx m : ℕ) : ℝ) ^ 2 / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith [hbb, hbnn]
    linarith [htri_lb, hstep]
  have htele_used : ((b 0) ^ 3 - (2 * (k : ℝ)) ^ 3) / (6 * (k : ℝ)) ≤
      ∑ m ∈ Finset.range M, (b m) ^ 2 := by
    have h1 := htele (M - 1) (by omega)
    have h2 : ∑ m ∈ Finset.range M, (b m) ^ 2
        = ∑ m ∈ Finset.range (M - 1), (b m) ^ 2 + (b (M - 1)) ^ 2 := by
      conv_lhs => rw [show M = (M - 1) + 1 by omega]
      rw [Finset.sum_range_succ]
    have hbM : 0 ≤ b (M - 1) := hb_nonneg (M - 1) (by omega)
    have hbM3 : (b (M - 1)) ^ 3 ≤ (2 * (k : ℝ)) ^ 3 := by
      have h := hb_last
      exact pow_le_pow_left₀ hbM h.le 3
    rw [h2]
    have h3 : ((b 0) ^ 3 - (b (M - 1)) ^ 3) / (6 * (k : ℝ))
        ≥ ((b 0) ^ 3 - (2 * (k : ℝ)) ^ 3) / (6 * (k : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hbM2 : (0 : ℝ) ≤ (b (M - 1)) ^ 2 := sq_nonneg _
    linarith [h1, h3, hbM2]
  have hb0 : b 0 = (D : ℝ) - 2 * (k : ℝ) := by
    simp only [hb]
    push_cast
    ring
  have hTlb : ((D : ℝ) + 1) * ((D : ℝ) + 2) / 2
      + (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (12 * (k : ℝ)) ≤ (T.card : ℝ) := by
    have h1 : ((∑ ℓ ∈ S, tri (D - k * ℓ) : ℕ) : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast hsum_lb
    rw [hS_sum] at h1
    push_cast at h1
    have h2 : (tri D : ℝ) + ∑ m ∈ Finset.range M, (tri (D - k * idx m) : ℝ)
        ≥ ((D : ℝ) + 1) * ((D : ℝ) + 2) / 2 + ∑ m ∈ Finset.range M, ((b m) ^ 2 / 2) := by
      linarith [htriD, hsum2]
    have h3 : ∑ m ∈ Finset.range M, ((b m) ^ 2 / 2)
        ≥ (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (12 * (k : ℝ)) := by
      have hh := htele_used
      rw [hb0] at hh
      have h8 : (2 * (k : ℝ)) ^ 3 = 8 * (k : ℝ) ^ 3 := by ring
      rw [h8] at hh
      have h4 : ∑ m ∈ Finset.range M, ((b m) ^ 2 / 2)
          = (∑ m ∈ Finset.range M, (b m) ^ 2) / 2 := by
        rw [Finset.sum_div]
      rw [h4]
      have hstep : (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (6 * (k : ℝ)) / 2
          ≤ (∑ m ∈ Finset.range M, (b m) ^ 2) / 2 :=
        div_le_div_of_nonneg_right hh (by norm_num)
      have heq : (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (6 * (k : ℝ)) / 2
          = (((D : ℝ) - 2 * (k : ℝ)) ^ 3 - 8 * (k : ℝ) ^ 3) / (12 * (k : ℝ)) := by
        rw [div_div]
        ring
      linarith [hstep, heq]
    linarith [h1, h2, h3]
  linarith [hkey, hTlb]
