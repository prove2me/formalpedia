-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.428696+00:00
-- url     : https://prove2.me/submissions/2a255bf9-80d6-4d84-97f5-3718e2707f40

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_3_5

section
set_option autoImplicit false

namespace GabidulinProx.Dev.L36

open GabidulinProx.UniqueDecoding Polynomial

section
variable {L : Type*} [Field L]

/-- ℕ-indexed linearized polynomial. -/
noncomputable def lin (q k : ℕ) (g : ℕ → L) : Polynomial L :=
  ∑ i ∈ Finset.range k, monomial (q ^ i) (g i)

lemma coeff_lin (q k : ℕ) (hq : 2 ≤ q) (g : ℕ → L) (j : ℕ) (hj : j < k) :
    (lin q k g).coeff (q ^ j) = g j := by
  simp only [lin, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (Nat.pow_right_injective hq h)
  · intro h; exact absurd (Finset.mem_range.2 hj) h

lemma coeff_comp_lin (p m : ℕ) [Fact p.Prime] [CharP L p] (q : ℕ) (hqm : q = p ^ m)
    (hq : 2 ≤ q) (e k : ℕ) (f g : ℕ → L) (j : ℕ) :
    ((lin q (e + 1) f).comp (lin q k g)).coeff (q ^ j) =
      ∑ r ∈ Finset.range (e + 1), ∑ i ∈ Finset.range k,
        if i + r = j then f r * g i ^ (q ^ r) else 0 := by
  unfold lin
  rw [sum_comp, finsetSum_coeff]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [monomial_comp]
  have hr : q ^ r = p ^ (m * r) := by rw [hqm, pow_mul]
  rw [hr, sum_pow_char_pow, coeff_C_mul, finsetSum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [monomial_pow, coeff_monomial, ← hr]
  by_cases h : i + r = j
  · subst h
    rw [if_pos, if_pos rfl]
    rw [← pow_add]
  · rw [if_neg h, if_neg, mul_zero]
    intro h2
    apply h
    have : q ^ (i + r) = q ^ j := by rw [pow_add]; exact h2
    exact Nat.pow_right_injective hq this


/-- Recurrence from the coefficient of `X^(q^j)`. -/
lemma rec_of_comp (p m : ℕ) [Fact p.Prime] [CharP L p] (q : ℕ) (hqm : q = p ^ m)
    (hq : 2 ≤ q) (e k : ℕ) (f g h : ℕ → L) (j : ℕ) (hj : j < k)
    (hE : (lin q (e + 1) f).comp (lin q k g) + lin q (k + e) h = 0) :
    f 0 * g j + ∑ r ∈ Finset.range (min e j), f (r + 1) * g (j - (r + 1)) ^ (q ^ (r + 1)) + h j
      = 0 := by
  have h1 := congrArg (fun P => P.coeff (q ^ j)) hE
  simp only [coeff_add, coeff_zero] at h1
  rw [coeff_comp_lin p m q hqm hq, coeff_lin q _ hq _ _ (by omega)] at h1
  have h2 : ∀ r ∈ Finset.range (e + 1),
      (∑ i ∈ Finset.range k, if i + r = j then f r * g i ^ (q ^ r) else 0) =
        if r ≤ j then f r * g (j - r) ^ (q ^ r) else 0 := by
    intro r _
    by_cases hr : r ≤ j
    · rw [if_pos hr, Finset.sum_eq_single (j - r)]
      · rw [if_pos (by omega)]
      · intro i _ hi; rw [if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    · rw [if_neg hr]
      exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ'] at h1
  simp only [zero_le, if_true, Nat.sub_zero, pow_zero, pow_one] at h1
  have h3 : ∑ r ∈ Finset.range e, (if r + 1 ≤ j then f (r + 1) * g (j - (r + 1)) ^ (q ^ (r + 1))
      else 0) = ∑ r ∈ Finset.range (min e j), f (r + 1) * g (j - (r + 1)) ^ (q ^ (r + 1)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext r; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]; omega
  rw [h3] at h1
  linear_combination h1

lemma sigma_split (q r j : ℕ) (h : r + 1 ≤ j) :
    sigma q j = sigma q r + q ^ (r + 1) * sigma q (j - (r + 1)) := by
  unfold sigma
  have : j + 1 = (r + 1) + (j - (r + 1) + 1) := by omega
  rw [this, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]

lemma sigma_pos (q j : ℕ) : 1 ≤ sigma q j := by
  unfold sigma
  calc 1 ≤ ∑ i ∈ Finset.range 1, q ^ i := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

lemma sigma_mono (q : ℕ) {i j : ℕ} (h : i ≤ j) : sigma q i ≤ sigma q j := by
  unfold sigma
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- The cleared-denominator recursion `N_j` of the paper. -/
noncomputable def N (q e : ℕ) (a0 : Polynomial L) (ta tb : ℕ → Polynomial L) :
    ℕ → Polynomial L
  | j => -(tb j * a0 ^ (sigma q j - 1)) -
      ∑ r ∈ (Finset.range (min e j)).attach,
        ta (r.1 + 1) * a0 ^ (sigma q r.1 - 1) * (N q e a0 ta tb (j - (r.1 + 1))) ^ (q ^ (r.1 + 1))
  termination_by j => j
  decreasing_by
    have h1 := Finset.mem_range.1 r.2
    have h2 : min e j ≤ j := min_le_right _ _
    omega

lemma N_eq (q e : ℕ) (a0 : Polynomial L) (ta tb : ℕ → Polynomial L) (j : ℕ) :
    N q e a0 ta tb j = -(tb j * a0 ^ (sigma q j - 1)) -
      ∑ r ∈ Finset.range (min e j),
        ta (r + 1) * a0 ^ (sigma q r - 1) * (N q e a0 ta tb (j - (r + 1))) ^ (q ^ (r + 1)) := by
  rw [N]
  congr 1
  exact Finset.sum_attach (Finset.range (min e j))
    (fun r => ta (r + 1) * a0 ^ (sigma q r - 1) * (N q e a0 ta tb (j - (r + 1))) ^ (q ^ (r + 1)))

lemma N_eval (q e k : ℕ) (a0 : Polynomial L) (ta tb : ℕ → Polynomial L) (z : L)
    (c : ℕ → L)
    (hrec : ∀ j < k, a0.eval z * c j +
      ∑ r ∈ Finset.range (min e j), (ta (r + 1)).eval z * c (j - (r + 1)) ^ (q ^ (r + 1))
      + (tb j).eval z = 0) :
    ∀ j < k, (N q e a0 ta tb j).eval z = (a0.eval z) ^ (sigma q j) * c j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rw [N_eq]
  simp only [eval_sub, eval_neg, eval_mul, eval_finsetSum, eval_pow]
  have hs : ∀ r ∈ Finset.range (min e j),
      (ta (r + 1)).eval z * (a0.eval z) ^ (sigma q r - 1) *
        ((a0.eval z) ^ sigma q (j - (r + 1)) * c (j - (r + 1))) ^ (q ^ (r + 1)) =
      (a0.eval z) ^ (sigma q j - 1) *
        ((ta (r + 1)).eval z * c (j - (r + 1)) ^ (q ^ (r + 1))) := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    have hmin : min e j ≤ j := min_le_right _ _
    have hsp := sigma_split q r j (by omega)
    have hp1 := sigma_pos q r
    have hexp : sigma q j - 1 = (sigma q r - 1) + sigma q (j - (r + 1)) * q ^ (r + 1) := by
      rw [hsp]; have := Nat.mul_comm (q ^ (r + 1)) (sigma q (j - (r + 1))); omega
    rw [hexp, mul_pow, ← pow_mul, pow_add]
    ring
  have hmin : min e j ≤ j := min_le_right _ _
  have hs2 : ∑ r ∈ Finset.range (min e j),
      (ta (r + 1)).eval z * (a0.eval z) ^ (sigma q r - 1) *
        ((N q e a0 ta tb (j - (r + 1))).eval z) ^ (q ^ (r + 1)) =
      (a0.eval z) ^ (sigma q j - 1) * ∑ r ∈ Finset.range (min e j),
        ((ta (r + 1)).eval z * c (j - (r + 1)) ^ (q ^ (r + 1))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    rw [ih (j - (r + 1)) (by omega) (by omega)]
    exact hs r hr
  rw [hs2]
  have hσ := sigma_pos q j
  have hj1 : (a0.eval z) ^ sigma q j = (a0.eval z) ^ (sigma q j - 1) * a0.eval z := by
    rw [← pow_succ]; congr 1; omega
  have := hrec j hj
  rw [hj1]
  linear_combination (-(a0.eval z) ^ (sigma q j - 1)) * this

lemma arith_deg (s A B Q : ℕ) (hA : 1 ≤ A) (hQ : Q ≤ s + 1) :
    (s + 1 - Q) + (A - 1) * s + Q * (s * B + 1) ≤ s * (A + Q * B) + 1 := by
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, s + 1 = Q + t := ⟨s + 1 - Q, by omega⟩
  have h1 : s + 1 - Q = t := by omega
  rw [h1]
  simp only [Nat.add_sub_cancel]
  have : s = Q + t - 1 := by omega
  nlinarith [ht]

lemma N_deg (q e : ℕ) (a0 : Polynomial L) (ta tb : ℕ → Polynomial L)
    (ha0 : a0.natDegree ≤ sigma q e - 1)
    (hta : ∀ r ≤ e, (ta r).natDegree ≤ sigma q e - q ^ r)
    (htb : ∀ j, (tb j).natDegree ≤ sigma q e) (hq : 1 ≤ q) :
    ∀ j, (N q e a0 ta tb j).natDegree ≤ (sigma q e - 1) * sigma q j + 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rw [N_eq]
  have hσe := sigma_pos q e
  have hσj := sigma_pos q j
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_neg]
    refine (natDegree_mul_le).trans ?_
    have h2 : (a0 ^ (sigma q j - 1)).natDegree ≤ (sigma q j - 1) * (sigma q e - 1) :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ ha0)
    calc (tb j).natDegree + (a0 ^ (sigma q j - 1)).natDegree
        ≤ sigma q e + (sigma q j - 1) * (sigma q e - 1) := Nat.add_le_add (htb j) h2
      _ = (sigma q e - 1) * sigma q j + 1 := by
        obtain ⟨u, hu⟩ : ∃ u, sigma q e = u + 1 := ⟨sigma q e - 1, by omega⟩
        obtain ⟨v, hv⟩ : ∃ v, sigma q j = v + 1 := ⟨sigma q j - 1, by omega⟩
        rw [hu, hv]; simp only [Nat.add_sub_cancel]; ring
  · refine natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    have hmin : min e j ≤ j := min_le_right _ _
    have hmine : min e j ≤ e := min_le_left _ _
    have hsp := sigma_split q r j (by omega)
    have hA := sigma_pos q r
    have hQ : q ^ (r + 1) ≤ sigma q e - 1 + 1 := by
      have : q ^ (r + 1) ≤ sigma q e := by
        unfold sigma
        exact Finset.single_le_sum (f := fun i => q ^ i) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (by omega))
      omega
    have hN := ih (j - (r + 1)) (by omega)
    refine (natDegree_mul_le).trans ?_
    refine (Nat.add_le_add natDegree_mul_le natDegree_pow_le).trans ?_
    have e1 := hta (r + 1) (by omega)
    have e2 : (a0 ^ (sigma q r - 1)).natDegree ≤ (sigma q r - 1) * (sigma q e - 1) :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ ha0)
    have e3 : q ^ (r + 1) * (N q e a0 ta tb (j - (r + 1))).natDegree ≤
        q ^ (r + 1) * ((sigma q e - 1) * sigma q (j - (r + 1)) + 1) :=
      Nat.mul_le_mul_left _ hN
    have key := arith_deg (sigma q e - 1) (sigma q r) (sigma q (j - (r + 1))) (q ^ (r + 1))
      hA hQ
    rw [← hsp] at key
    calc _ ≤ (sigma q e - q ^ (r + 1)) + (sigma q r - 1) * (sigma q e - 1) +
        q ^ (r + 1) * ((sigma q e - 1) * sigma q (j - (r + 1)) + 1) :=
          Nat.add_le_add (Nat.add_le_add e1 e2) e3
      _ ≤ _ := by
        have : sigma q e - 1 + 1 = sigma q e := by omega
        rw [this] at key
        calc _ = (sigma q e - q ^ (r + 1)) + (sigma q r - 1) * (sigma q e - 1) +
            q ^ (r + 1) * ((sigma q e - 1) * sigma q (j - (r + 1)) + 1) := rfl
          _ ≤ _ := by
            have k2 : (sigma q r - 1) * (sigma q e - 1) = (sigma q r - 1) * (sigma q e - 1) := rfl
            rw [Nat.mul_comm (sigma q r - 1)] at *
            exact key

lemma lin_congr (q k : ℕ) (f g : ℕ → L) (h : ∀ i < k, f i = g i) : lin q k f = lin q k g := by
  unfold lin
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

lemma linearized_eq_lin (q k : ℕ) (c : Fin k → L) (f : ℕ → L) (hf : ∀ i : Fin k, f i = c i) :
    linearized q c = lin q k f := by
  unfold linearized lin
  rw [← Fin.sum_univ_eq_sum_range (fun i => monomial (q ^ i) (f i)) k]
  exact Finset.sum_congr rfl fun i _ => by rw [hf i]

lemma C_mul_lin (q k : ℕ) (x : L) (g : ℕ → L) :
    C x * lin q k g = lin q k (fun i => x * g i) := by
  simp [lin, Finset.mul_sum, C_mul_monomial]

lemma lagrange_eval (S : Finset L) (c : L → L) (z : L) (hz : z ∈ S) :
    (lagrange S c).eval z = c z := by
  classical
  unfold lagrange
  rw [eval_finsetSum, Finset.sum_eq_single z]
  · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    have hne : ∏ w ∈ S.erase z, (z - w) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun w hw => sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hw))
    field_simp
  · intro w _ hwz
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    have h0 : ∏ x ∈ S.erase w, (z - x) = 0 :=
      Finset.prod_eq_zero (i := z) (Finset.mem_erase.2 ⟨Ne.symm hwz, hz⟩) (sub_self z)
    rw [h0, mul_zero]
  · intro h; exact absurd hz h

lemma rootProduct_dvd (S : Finset L) (D : Polynomial L) (h : ∀ z ∈ S, D.eval z = 0) :
    rootProduct S ∣ D := by
  by_cases hD : D = 0
  · rw [hD]; exact dvd_zero _
  unfold rootProduct
  have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hD S.val).2
    ((Multiset.le_iff_subset S.nodup).2 fun z hz =>
      (mem_roots hD).2 (h z hz))
  exact this

end
end GabidulinProx.Dev.L36

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.L36 Polynomial

theorem chk_lemma_3_6 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (a : Fin (e + 1) → Polynomial L)
    (b : Fin (k + e) → Polynomial L)
    (hAB : GlobalIdentity (Fintype.card K) α u₀ u₁ a b)
    (hbounds : GlobalBounds (Fintype.card K) a b)
    (hS : sigma (Fintype.card K) e < (goodParameters K α k e u₀ u₁).card)
    (Pz : L → Polynomial L)
    (hPz : DecodedFamily K α u₀ u₁ k e (goodParameters K α k e u₀ u₁) Pz) :
    let q := Fintype.card K
    let S := goodParameters K α k e u₀ u₁
    let S₀ := regularParameters S (a 0)
    let p := coefficientInterpolants q k S Pz
    ∃ pt : Fin k → Polynomial L,
      (∀ j, (pt j).natDegree ≤ clearingBound q k e) ∧
      (∀ j, rootProduct S₀ ∣ pt j - (a 0) ^ (sigma q (k - 1)) * p j) ∧
      ∀ z ∈ S₀, specialize q pt z = Polynomial.C ((a 0).eval z ^ (sigma q (k - 1))) * Pz z := by
  intro q S S₀ p
  classical
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  haveI : CharP L (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
  obtain ⟨m, -, hqm⟩ := FiniteField.card K (ringChar K)
  let ta : ℕ → Polynomial L := fun r => if h : r < e + 1 then a ⟨r, h⟩ else 0
  let tb : ℕ → Polynomial L := fun r => if h : r < k + e then b ⟨r, h⟩ else 0
  have hta0 : ta 0 = a 0 := by simp [ta]
  have hsa : ∀ z, specialize q a z = lin q (e + 1) (fun r => (ta r).eval z) := fun z =>
    linearized_eq_lin q _ _ _ fun i => by simp [ta, Nat.le_of_lt_succ i.2]
  have hsb : ∀ z, specialize q b z = lin q (k + e) (fun r => (tb r).eval z) := fun z =>
    linearized_eq_lin q _ _ _ fun i => by simp [tb]
  have hsP : ∀ z ∈ S, Pz z = lin q k (fun i => (Pz z).coeff (q ^ i)) := by
    intro z hz
    obtain ⟨c0, hc0⟩ := (hPz z hz).1
    have h1 : Pz z = lin q k (fun i => if h : i < k then c0 ⟨i, h⟩ else 0) :=
      hc0.trans (linearized_eq_lin q k c0 _ fun i => by simp)
    conv_lhs => rw [h1]
    refine lin_congr q k _ _ fun i hi => ?_
    rw [h1, coeff_lin q k hq2 _ i hi, dif_pos hi]
  have hrec : ∀ z ∈ S, ∀ j < k, (ta 0).eval z * (Pz z).coeff (q ^ j) +
      ∑ r ∈ Finset.range (min e j), (ta (r + 1)).eval z *
        (Pz z).coeff (q ^ (j - (r + 1))) ^ (q ^ (r + 1)) + (tb j).eval z = 0 := by
    intro z hz j hj
    have hE := lemma_3_5 hk hkn he hdec α hα u₀ u₁ a b hAB z (Pz z) (hPz z hz).1 (hPz z hz).2
    rw [hsa, hsb] at hE
    conv at hE => lhs; rw [show Pz z = lin q k (fun i => (Pz z).coeff (q ^ i)) from hsP z hz]
    exact rec_of_comp (ringChar K) m q hqm hq2 e k _ _ _ j hj hE
  have ha0 : (a 0).natDegree ≤ sigma q e - 1 := by
    have := hbounds.2.1 0
    simpa using this
  have hta : ∀ r ≤ e, (ta r).natDegree ≤ sigma q e - q ^ r := by
    intro r hr
    have := hbounds.2.1 ⟨r, by omega⟩
    have hr1 : r < e + 1 := by omega
    rw [show ta r = a ⟨r, hr1⟩ from dif_pos hr1]
    simpa using this
  have htb : ∀ j, (tb j).natDegree ≤ sigma q e := by
    intro j
    by_cases h : j < k + e
    · simpa [tb, h] using hbounds.2.2 ⟨j, h⟩
    · simp [tb, h]
  have hN := N_deg q e (a 0) ta tb ha0 hta htb (by omega)
  refine ⟨fun j => (a 0) ^ (sigma q (k - 1) - sigma q j.val) * N q e (a 0) ta tb j.val,
    ?_, ?_, ?_⟩
  · intro j
    have hjk : j.val ≤ k - 1 := by omega
    have hmono := sigma_mono q hjk
    refine natDegree_mul_le.trans ?_
    have h2 : ((a 0) ^ (sigma q (k - 1) - sigma q j.val)).natDegree ≤
        (sigma q (k - 1) - sigma q j.val) * (sigma q e - 1) :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ ha0)
    have h3 := hN j.val
    unfold clearingBound
    calc _ ≤ (sigma q (k - 1) - sigma q j.val) * (sigma q e - 1) +
          ((sigma q e - 1) * sigma q j.val + 1) := Nat.add_le_add h2 h3
      _ = _ := by
        obtain ⟨d, hd⟩ : ∃ d, sigma q (k - 1) = sigma q j.val + d := ⟨_, (Nat.add_sub_cancel' hmono).symm⟩
        rw [hd]; simp only [Nat.add_sub_cancel_left]; ring
  · intro j
    refine rootProduct_dvd _ _ fun z hz => ?_
    have hz' : z ∈ S ∧ (a 0).eval z ≠ 0 := by
      simpa [S₀, regularParameters] using hz
    obtain ⟨hzS, hza⟩ := hz'
    have hev := N_eval q e k (a 0) ta tb z (fun i => (Pz z).coeff (q ^ i))
      (fun j hj => by
        have := hrec z hzS j hj
        rwa [hta0] at this) j.val j.2
    simp only [eval_sub, eval_mul, eval_pow, hev]
    simp only [p, coefficientInterpolants, lagrange_eval S _ z hzS]
    have hmono := sigma_mono q (show j.val ≤ k - 1 by omega)
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmono, sub_self]
  · intro z hz
    have hz' : z ∈ S ∧ (a 0).eval z ≠ 0 := by
      simpa [S₀, regularParameters] using hz
    obtain ⟨hzS, hza⟩ := hz'
    have hev : ∀ j : Fin k, (N q e (a 0) ta tb j.val).eval z =
        (a 0).eval z ^ sigma q j.val * (Pz z).coeff (q ^ j.val) := fun j =>
      N_eval q e k (a 0) ta tb z (fun i => (Pz z).coeff (q ^ i))
        (fun j hj => by
          have := hrec z hzS j hj
          rwa [hta0] at this) j.val j.2
    have hev2 : ∀ j : Fin k, (a 0 ^ (sigma q (k - 1) - sigma q j.val) *
        N q e (a 0) ta tb j.val).eval z = (a 0).eval z ^ sigma q (k - 1) * (Pz z).coeff (q ^ j.val) := by
      intro j
      have hmono := sigma_mono q (show j.val ≤ k - 1 by omega)
      rw [eval_mul, eval_pow, hev, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmono]
    unfold specialize
    rw [linearized_eq_lin q k _ (fun i => (a 0).eval z ^ sigma q (k - 1) * (Pz z).coeff (q ^ i))
      (fun i => (hev2 i).symm)]
    conv_rhs => rw [hsP z hzS, C_mul_lin]

end GabidulinProx.UniqueDecoding

end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_lemma_3_6 := @GabidulinProx.UniqueDecoding.chk_lemma_3_6
