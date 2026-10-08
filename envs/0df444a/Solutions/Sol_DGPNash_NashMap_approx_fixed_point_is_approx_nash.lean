-- Prove2me | solution 1 for DGPNash.NashMap.approx_fixed_point_is_approx_nash
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:58:36.738278+00:00
-- url     : https://prove2.me/submissions/9455c9d3-552c-4ab9-83f7-c35da715632b

import Definitions.Def_DGPNash_NashMap_nashMap



namespace DGPNash.NashMap

open Finset

lemma dgp_prod_update {r n : ℕ} (z : Fin r → Fin n → ℝ) (i : Fin r) (c : Fin n → ℝ)
    (s : Fin r → Fin n) :
    ∏ k, (Function.update z i c) k (s k) = c (s i) * ∏ k ∈ univ.erase i, z k (s k) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

lemma dgp_sum_prod {r n : ℕ} (w : Fin r → Fin n → ℝ) :
    ∑ s : Fin r → Fin n, ∏ k, w k (s k) = ∏ k, ∑ j, w k j := by
  rw [Fintype.prod_sum]

lemma dgp_lemA {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (p : Fin r) (M : ℝ)
    (hu0 : ∀ s, 0 ≤ u p s) (huM : ∀ s, u p s ≤ M)
    (z : Fin r → Fin n → ℝ) (hz : AGT.IsMixedProfile z) (i : Fin r) (a b : Fin n → ℝ) :
    |AGT.expectedPayoff u (Function.update z i a) p - AGT.expectedPayoff u (Function.update z i b) p|
      ≤ M * ∑ j, |a j - b j| := by
  have hM : 0 ≤ M := le_trans (hu0 (fun _ => ⟨0, by
      rcases n with _ | n
      · exact (Fin.elim0 (by simpa using (hz i).2))
      · omega⟩)) (huM _)
  unfold AGT.expectedPayoff AGT.profileProb
  rw [← Finset.sum_sub_distrib]
  have key : ∀ s : Fin r → Fin n,
      |(∏ k, (Function.update z i a) k (s k)) * u p s - (∏ k, (Function.update z i b) k (s k)) * u p s|
        ≤ M * ∏ k, (Function.update z i (fun j => |a j - b j|)) k (s k) := by
    intro s
    rw [dgp_prod_update, dgp_prod_update, dgp_prod_update]
    have hQ : 0 ≤ ∏ k ∈ univ.erase i, z k (s k) := Finset.prod_nonneg (fun k _ => (hz k).1 _)
    rw [show a (s i) * (∏ k ∈ univ.erase i, z k (s k)) * u p s
        - b (s i) * (∏ k ∈ univ.erase i, z k (s k)) * u p s
        = (a (s i) - b (s i)) * ((∏ k ∈ univ.erase i, z k (s k)) * u p s) by ring]
    rw [abs_mul, abs_of_nonneg (mul_nonneg hQ (hu0 s))]
    have := hu0 s; have := huM s
    have h1 : 0 ≤ |a (s i) - b (s i)| := abs_nonneg _
    calc |a (s i) - b (s i)| * ((∏ k ∈ univ.erase i, z k (s k)) * u p s)
        ≤ |a (s i) - b (s i)| * ((∏ k ∈ univ.erase i, z k (s k)) * M) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ s : Fin r → Fin n, |(∏ k, (Function.update z i a) k (s k)) * u p s - (∏ k, (Function.update z i b) k (s k)) * u p s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin r → Fin n, M * ∏ k, (Function.update z i (fun j => |a j - b j|)) k (s k) :=
        Finset.sum_le_sum (fun s _ => key s)
    _ = M * ∑ j, |a j - b j| := by
        rw [← Finset.mul_sum, dgp_sum_prod]
        congr 1
        rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
        simp only [Function.update_self]
        rw [Finset.prod_eq_one, mul_one]
        intro k hk
        rw [Function.update_of_ne (ne_of_mem_erase hk)]
        exact (hz k).2


lemma dgp_lemB {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (p : Fin r) (M : ℝ)
    (hu0 : ∀ s, 0 ≤ u p s) (huM : ∀ s, u p s ≤ M)
    (x x' : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x') :
    |AGT.expectedPayoff u x p - AGT.expectedPayoff u x' p|
      ≤ M * ∑ i, ∑ j, |x i j - x' i j| := by
  classical
  let h : Finset (Fin r) → Fin r → Fin n → ℝ := fun T k => if k ∈ T then x' k else x k
  have hmix : ∀ T, AGT.IsMixedProfile (h T) := by
    intro T k; by_cases hk : k ∈ T <;> simp [h, hk, hx k, hx' k]
  have claim : ∀ T : Finset (Fin r), |AGT.expectedPayoff u x p - AGT.expectedPayoff u (h T) p|
      ≤ M * ∑ i ∈ T, ∑ j, |x i j - x' i j| := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : h ∅ = x := by funext k; simp [h]
      simp [this]
    | insert a T ha ih =>
      have e1 : h (insert a T) = Function.update (h T) a (x' a) := by
        funext k; by_cases hk : k = a
        · subst hk; simp [h]
        · simp [h, hk, Function.update_of_ne hk]
      have e2 : h T = Function.update (h T) a (x a) := by
        funext k; by_cases hk : k = a
        · subst hk; simp [h, ha]
        · simp [Function.update_of_ne hk]
      have := dgp_lemA u p M hu0 huM (h T) (hmix T) a (x a) (x' a)
      rw [← e2, ← e1] at this
      rw [Finset.sum_insert ha, mul_add]
      calc _ ≤ |AGT.expectedPayoff u x p - AGT.expectedPayoff u (h T) p|
            + |AGT.expectedPayoff u (h T) p - AGT.expectedPayoff u (h (insert a T)) p| :=
              abs_sub_le _ _ _
        _ ≤ _ := by linarith
  have hu : h univ = x' := by funext k; simp [h]
  simpa [hu] using claim univ


lemma dgp_maxPayoff_ge {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (p : Fin r) (s : Fin r → Fin n) :
    u p s ≤ maxPayoff u := by
  unfold maxPayoff
  exact le_csSup (Set.finite_range _).bddAbove ⟨(p, s), rfl⟩

lemma dgp_maxPayoff_nonneg {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s) : 0 ≤ maxPayoff u :=
  le_trans (hu ⟨0, by omega⟩ (fun _ => ⟨0, hn⟩)) (dgp_maxPayoff_ge u _ _)

lemma dgp_frac (A A' G G' : ℝ) (hG : 0 ≤ G) (hG' : 0 ≤ G') (hA' : 0 ≤ A') (hA'1 : A' ≤ 1 + G') :
    |A / (1 + G) - A' / (1 + G')| ≤ |A - A'| + |G - G'| := by
  have hD : 0 < 1 + G := by linarith
  have hD' : 0 < 1 + G' := by linarith
  set q := A' / (1 + G') with hq
  have hq0 : 0 ≤ q := div_nonneg hA' hD'.le
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hD']; exact hA'1
  have hA'q : A' = q * (1 + G') := by rw [hq]; field_simp
  have e : A / (1 + G) - q = (A - A') / (1 + G) + q * (G' - G) / (1 + G) := by
    rw [hA'q]; field_simp; ring
  rw [e]
  calc _ ≤ |(A - A') / (1 + G)| + |q * (G' - G) / (1 + G)| := abs_add_le _ _
    _ ≤ |A - A'| + |G - G'| := by
      refine add_le_add ?_ ?_
      · rw [abs_div, abs_of_pos hD]; exact div_le_self (abs_nonneg _) (by linarith)
      · rw [abs_div, abs_of_pos hD, abs_mul, abs_of_nonneg hq0, abs_sub_comm]
        calc q * |G - G'| / (1 + G) ≤ q * |G - G'| := div_le_self (by positivity) (by linarith)
          _ ≤ 1 * |G - G'| := by gcongr
          _ = _ := one_mul _

lemma dgp_pure_mixed {r n : ℕ} (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x) (p : Fin r)
    (j : Fin n) : AGT.IsMixedProfile (Function.update x p (fun k => if k = j then 1 else 0)) := by
  intro i
  by_cases hi : i = p
  · subst hi; simp only [Function.update_self]
    refine ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
  · rw [Function.update_of_ne hi]; exact hx i

lemma dgp_gain_nonneg {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (x : Fin r → Fin n → ℝ)
    (p : Fin r) (j : Fin n) : 0 ≤ gain u x p j := le_max_left _ _

theorem lemma_3_4_core {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x x' : Fin r → Fin n → ℝ)
    (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x')
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ p j, |x p j - x' p j| ≤ δ) :
    ∀ p j, |nashMap u x p j - nashMap u x' p j| ≤
      (1 + 2 * maxPayoff u * (r : ℝ) * (n : ℝ) * ((n : ℝ) + 1)) * δ := by
  intro p j
  set U := maxPayoff u with hUdef
  have hU0 : 0 ≤ U := dgp_maxPayoff_nonneg hr hn u hu
  have hsum : ∀ y y' : Fin r → Fin n → ℝ, (∀ i k, |y i k - y' i k| ≤ δ) →
      ∑ i, ∑ k, |y i k - y' i k| ≤ (r : ℝ) * n * δ := by
    intro y y' h
    calc ∑ i, ∑ k, |y i k - y' i k| ≤ ∑ _i : Fin r, ∑ _k : Fin n, δ :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => h i k))
      _ = _ := by simp; ring
  have hE : |AGT.expectedPayoff u x p - AGT.expectedPayoff u x' p| ≤ U * (r * n * δ) :=
    le_trans (dgp_lemB u p U (hu p) (dgp_maxPayoff_ge u p) x x' hx hx')
      (mul_le_mul_of_nonneg_left (hsum x x' hclose) hU0)
  have hP : ∀ k, |purePayoff u x p k - purePayoff u x' p k| ≤ U * (r * n * δ) := by
    intro k
    refine le_trans (dgp_lemB u p U (hu p) (dgp_maxPayoff_ge u p) _ _
      (dgp_pure_mixed x hx p k) (dgp_pure_mixed x' hx' p k))
      (mul_le_mul_of_nonneg_left (hsum _ _ ?_) hU0)
    intro i l
    by_cases hi : i = p
    · subst hi; simp [hδ]
    · simp only [Function.update_of_ne hi]; exact hclose i l
  have hB : ∀ k, |gain u x p k - gain u x' p k| ≤ 2 * (U * (r * n * δ)) := by
    intro k
    unfold gain
    rw [max_comm 0, max_comm 0]
    refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
    have := hP k
    calc _ = |(purePayoff u x p k - purePayoff u x' p k)
              - (AGT.expectedPayoff u x p - AGT.expectedPayoff u x' p)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := by linarith
  have hG : |∑ k, gain u x p k - ∑ k, gain u x' p k| ≤ n * (2 * (U * (r * n * δ))) := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc _ ≤ ∑ _k : Fin n, 2 * (U * (r * n * δ)) := Finset.sum_le_sum (fun k _ => hB k)
      _ = _ := by simp
  have hA : |(x p j + gain u x p j) - (x' p j + gain u x' p j)| ≤ δ + 2 * (U * (r * n * δ)) := by
    calc _ = |(x p j - x' p j) + (gain u x p j - gain u x' p j)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (hclose p j) (hB j)
  have hx'1 : x' p j ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => (hx' p).1 k) (mem_univ j) (f := x' p)
    rw [(hx' p).2] at this; exact this
  have hBle : gain u x' p j ≤ ∑ k, gain u x' p k :=
    Finset.single_le_sum (fun k _ => dgp_gain_nonneg u x' p k) (mem_univ j)
  unfold nashMap
  refine le_trans (dgp_frac _ _ _ _ (Finset.sum_nonneg (fun k _ => dgp_gain_nonneg u x p k))
    (Finset.sum_nonneg (fun k _ => dgp_gain_nonneg u x' p k))
    (add_nonneg ((hx' p).1 j) (dgp_gain_nonneg u x' p j)) (by linarith)) ?_
  have := add_le_add hA hG
  refine le_trans this (le_of_eq ?_)
  ring


lemma dgp_linear {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (x : Fin r → Fin n → ℝ)
    (p : Fin r) (y : Fin n → ℝ) :
    AGT.expectedPayoff u (Function.update x p y) p = ∑ j, y j * purePayoff u x p j := by
  unfold purePayoff AGT.expectedPayoff AGT.profileProb
  simp_rw [dgp_prod_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 2
  simp [mul_ite]

lemma dgp_E_bounds {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (p : Fin r) (M : ℝ)
    (hu0 : ∀ s, 0 ≤ u p s) (huM : ∀ s, u p s ≤ M)
    (z : Fin r → Fin n → ℝ) (hz : AGT.IsMixedProfile z) :
    0 ≤ AGT.expectedPayoff u z p ∧ AGT.expectedPayoff u z p ≤ M := by
  unfold AGT.expectedPayoff AGT.profileProb
  have hp : ∀ s : Fin r → Fin n, 0 ≤ ∏ k, z k (s k) := fun s => Finset.prod_nonneg (fun k _ => (hz k).1 _)
  have h1 : ∑ s : Fin r → Fin n, ∏ k, z k (s k) = 1 := by
    rw [dgp_sum_prod]; exact Finset.prod_eq_one (fun k _ => (hz k).2)
  refine ⟨Finset.sum_nonneg (fun s _ => mul_nonneg (hp s) (hu0 s)), ?_⟩
  calc _ ≤ ∑ s : Fin r → Fin n, (∏ k, z k (s k)) * M :=
        Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (huM s) (hp s))
    _ = M := by rw [← Finset.sum_mul, h1, one_mul]

theorem approx_core {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x)
    (ε' : ℝ) (hε' : 0 ≤ ε')
    (hclose : ∀ p j, |nashMap u x p j - x p j| ≤ ε') :
    IsApproxNash u x
      ((n : ℝ) * Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u)) *
        (1 + Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u))) *
        max (maxPayoff u) 1) := by
  refine ⟨hx, ?_⟩
  intro p y hy
  set U := maxPayoff u with hUdef
  have hU0 : 0 ≤ U := dgp_maxPayoff_nonneg hr hn u hu
  have hUge := dgp_maxPayoff_ge u p
  set E := AGT.expectedPayoff u x p with hEdef
  have hE := dgp_E_bounds u p U (hu p) hUge x hx
  have hPb : ∀ k, 0 ≤ purePayoff u x p k ∧ purePayoff u x p k ≤ U := fun k =>
    dgp_E_bounds u p U (hu p) hUge _ (dgp_pure_mixed x hx p k)
  set G := ∑ k, gain u x p k with hGdef
  have hB0 : ∀ k, 0 ≤ gain u x p k := dgp_gain_nonneg u x p
  have hBU : ∀ k, gain u x p k ≤ U := by
    intro k; unfold gain; rw [← hEdef]
    exact max_le hU0 (by linarith [(hPb k).2, hE.1])
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun k _ => hB0 k)
  have hGn : G ≤ n * U := by
    calc G ≤ ∑ _k : Fin n, U := Finset.sum_le_sum (fun k _ => hBU k)
      _ = _ := by simp
  set c := ε' * (1 + n * U) with hcdef
  have hc0 : 0 ≤ c := mul_nonneg hε' (by positivity)
  have hfix : ∀ k, |gain u x p k - x p k * G| ≤ c := by
    intro k
    have h := hclose p k
    have hD : 0 < 1 + G := by linarith
    have e : nashMap u x p k - x p k = (gain u x p k - x p k * G) / (1 + G) := by
      unfold nashMap; rw [← hGdef]; field_simp; ring
    rw [e, abs_div, abs_of_pos hD, div_le_iff₀ hD] at h
    calc _ ≤ ε' * (1 + G) := h
      _ ≤ c := mul_le_mul_of_nonneg_left (by linarith) hε'
  -- sum identity
  have hlin := dgp_linear u x p (x p)
  rw [Function.update_eq_self] at hlin
  have hsum0 : ∑ k, x p k * (purePayoff u x p k - E) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← hlin, ← Finset.sum_mul, (hx p).2, one_mul, sub_self]
  have hsplit : ∑ k, x p k * gain u x p k = ∑ k, x p k * max 0 (E - purePayoff u x p k) := by
    have : ∀ k, x p k * gain u x p k = x p k * max 0 (E - purePayoff u x p k)
        + x p k * (purePayoff u x p k - E) := by
      intro k; unfold gain; rw [← hEdef]
      rcases le_total (purePayoff u x p k) E with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    simp_rw [this]; rw [Finset.sum_add_distrib, hsum0, add_zero]
  have hneg : G * ∑ k, x p k * max 0 (E - purePayoff u x p k) ≤ n * (c * U) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _k : Fin n, c * U := by
          apply Finset.sum_le_sum
          intro k _
          rcases le_total (E - purePayoff u x p k) 0 with h | h
          · rw [max_eq_left h]; simp; positivity
          · rw [max_eq_right h]
            have hg : gain u x p k = 0 := by
              unfold gain; rw [← hEdef]; exact max_eq_left (by linarith)
            have h1 := hfix k
            rw [hg] at h1
            have h2 : x p k * G ≤ c := by
              have := neg_abs_le (0 - x p k * G); linarith
            have h3 : E - purePayoff u x p k ≤ U := by linarith [(hPb k).1, hE.2]
            have hxk := (hx p).1 k
            calc G * (x p k * (E - purePayoff u x p k)) = (x p k * G) * (E - purePayoff u x p k) := by ring
              _ ≤ c * U := mul_le_mul h2 h3 h hc0
      _ = _ := by simp
  have hmaxB : ∀ j, gain u x p j ≤ c + Real.sqrt (n * U * c) := by
    intro j
    set t := Real.sqrt (n * U * c) with ht
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t * t = n * U * c := Real.mul_self_sqrt (by positivity)
    have hxj := (hx p).1 j
    have hj : x p j * G * gain u x p j ≤ n * (c * U) := by
      have : x p j * gain u x p j ≤ ∑ k, x p k * gain u x p k :=
        Finset.single_le_sum (f := fun k => x p k * gain u x p k)
          (fun k _ => mul_nonneg ((hx p).1 k) (hB0 k)) (mem_univ j)
      rw [hsplit] at this
      calc x p j * G * gain u x p j = G * (x p j * gain u x p j) := by ring
        _ ≤ G * ∑ k, x p k * max 0 (E - purePayoff u x p k) := mul_le_mul_of_nonneg_left this hG0
        _ ≤ _ := hneg
    have hl : gain u x p j - c ≤ x p j * G := by
      have := le_abs_self (gain u x p j - x p j * G); linarith [hfix j]
    by_contra hcon
    push Not at hcon
    have h1 : t < x p j * G := by linarith
    have h2 : t * (c + t) < x p j * G * gain u x p j := by
      exact mul_lt_mul'' h1 hcon ht0 (by positivity)
    nlinarith
  -- final bound
  set M := max U 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hUM : U ≤ M := le_max_left _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnM : 1 ≤ (n : ℝ) * M := by nlinarith
  have hsc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
  have hsc0 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  have ht : Real.sqrt (n * U * c) ≤ n * M * Real.sqrt c := by
    have : n * U * c ≤ (n * M * Real.sqrt c) ^ 2 := by
      have : (n * M * Real.sqrt c) ^ 2 = (n * M) ^ 2 * c := by rw [mul_pow, Real.sq_sqrt hc0]
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hc0
      nlinarith
    calc _ ≤ Real.sqrt ((n * M * Real.sqrt c) ^ 2) := Real.sqrt_le_sqrt this
      _ = _ := Real.sqrt_sq (by positivity)
  have hbound : ∀ j, gain u x p j ≤
      (n : ℝ) * Real.sqrt c * (1 + Real.sqrt c) * M := by
    intro j
    have := hmaxB j
    have : c ≤ n * M * c := by nlinarith
    nlinarith
  rw [dgp_linear]
  calc ∑ j, y j * purePayoff u x p j
      ≤ ∑ j, y j * (E + (n : ℝ) * Real.sqrt c * (1 + Real.sqrt c) * M) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (hy.1 j)
        have : purePayoff u x p j - E ≤ gain u x p j := by unfold gain; rw [← hEdef]; exact le_max_right _ _
        linarith [hbound j]
    _ = _ := by rw [← Finset.sum_mul, hy.2, one_mul]

end DGPNash.NashMap

open DGPNash.NashMap


theorem solution {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x)
    (ε' : ℝ) (hε' : 0 ≤ ε')
    (hclose : ∀ p j, |nashMap u x p j - x p j| ≤ ε') :
    IsApproxNash u x
      ((n : ℝ) * Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u)) *
        (1 + Real.sqrt (ε' * (1 + (n : ℝ) * maxPayoff u))) *
        max (maxPayoff u) 1) := by
  exact approx_core hr hn u hu x hx ε' hε' hclose
