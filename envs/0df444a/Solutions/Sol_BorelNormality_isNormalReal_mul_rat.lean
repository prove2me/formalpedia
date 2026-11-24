-- Prove2me | solution 1 for BorelNormality.isNormalReal_mul_rat
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:56:18.690193+00:00
-- url     : https://prove2.me/submissions/2b01f5f1-38cf-4e7a-9349-0d0a6773f04a

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

-- (`open BorelNormality` omitted: the namespace has no declarations outside the target module,
--  and the statement uses nothing from it.)
open Filter Topology

/-!
# Normality is preserved by multiplication by a nonzero rational (D. D. Wall, 1949)

Plan.
1. *Pyatetskii-Shapiro criterion* (`ps_main`): if every word `w` over `{0,…,b-1}` eventually
   satisfies `count(w, N) ≤ C N b^{-|w|}`, the digit sequence is normal. Proof: take any
   subsequence along which all word frequencies converge (compactness of `[0,1]^(List ℕ)`);
   the limit `F` is a shift-invariant probability on words with `F ≤ C b^{-n}`. Its block
   entropy `H_n` is subadditive, `≤ n log b`, and `≥ n log b - log C`; hence `H_n = n log b`
   and `F` is uniform on words of each length (equality case of Gibbs' inequality).
2. *Upper bound for `x·p/q`*: an occurrence of `w` (length `k`) in the digits of `z = x p/q`
   at position `n` forces the `k` digits of `x` at `n` to lie in a set of at most
   `(q + 2|p|)²` words (the integers `p⌊x bᵐ⌋ - q⌊z bᵐ⌋`, `m = n, n+k`, lie in
   `(-|p|, q+|p|)`); normality of `x` then gives the bound of step 1.
-/

/-! ## Words of the sequence -/

/-- The word of length `m` of `s` starting at position `i`. -/
private def Wd (s : ℕ → ℕ) (m i : ℕ) : List ℕ := List.ofFn (fun t : Fin m => s (i + t))

private lemma Wd_length (s : ℕ → ℕ) (m i : ℕ) : (Wd s m i).length = m := by simp [Wd]

private lemma occ_iff (s : ℕ → ℕ) (u : List ℕ) (i : ℕ) :
    (∀ j : Fin u.length, s (i + j) = u.get j) ↔ Wd s u.length i = u := by
  constructor
  · intro h
    apply List.ext_getElem (Wd_length s _ i)
    intro t h1 h2
    simp only [Wd, List.getElem_ofFn]
    have := h ⟨t, h2⟩
    simpa using this
  · intro h j
    have := congrArg (fun l => l.getD j 0) h
    simp only [Wd] at this
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ j.2] at this
    simpa using this

private lemma count_eq (s : ℕ → ℕ) (u : List ℕ) (N : ℕ) :
    Normal.count s u N = ((Finset.range N).filter (fun i => Wd s u.length i = u)).card := by
  unfold Normal.count
  congr 1
  apply Finset.filter_congr
  intro i _
  exact occ_iff s u i

private lemma count_le (s : ℕ → ℕ) (u : List ℕ) (N : ℕ) : Normal.count s u N ≤ N := by
  unfold Normal.count
  exact (Finset.card_filter_le _ _).trans (by simp)

/-! ## `strs` -/

private lemma mem_strs_of {b : ℕ} : ∀ (n : ℕ) (l : List ℕ), l.length = n →
    (∀ d ∈ l, d < b) → l ∈ Normal.strs b n
  | 0, l, hl, _ => by
    rw [List.length_eq_zero_iff] at hl
    subst hl; simp [Normal.strs]
  | n + 1, [], hl, _ => by simp at hl
  | n + 1, d :: l, hl, hd => by
    simp only [Normal.strs, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    refine ⟨(d, l), ⟨hd d (by simp), mem_strs_of n l (by simpa using hl)
      (fun e he => hd e (by simp [he]))⟩, rfl⟩

private lemma of_mem_strs {b : ℕ} : ∀ (n : ℕ) (l : List ℕ), l ∈ Normal.strs b n →
    l.length = n ∧ ∀ d ∈ l, d < b
  | 0, l, h => by simp [Normal.strs] at h; subst h; simp
  | n + 1, l, h => by
    simp only [Normal.strs, Finset.mem_image, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨⟨d, l'⟩, ⟨hd, hl'⟩, rfl⟩ := h
    obtain ⟨h1, h2⟩ := of_mem_strs n l' hl'
    refine ⟨by simp [h1], ?_⟩
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hd
    · exact h2 e he

private lemma card_strs (b : ℕ) : ∀ n, (Normal.strs b n).card = b ^ n
  | 0 => by simp [Normal.strs]
  | n + 1 => by
    simp only [Normal.strs]
    rw [Finset.card_image_of_injective _ (by
      rintro ⟨a, l⟩ ⟨a', l'⟩ h
      simp only [List.cons.injEq] at h
      rw [h.1, h.2]), Finset.card_product, Finset.card_range, card_strs b n]
    ring

private lemma strs_add (b n m : ℕ) : Normal.strs b (n + m) =
    (Normal.strs b n ×ˢ Normal.strs b m).image (fun p => p.1 ++ p.2) := by
  ext l
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · intro h
    obtain ⟨hl, hd⟩ := of_mem_strs _ l h
    refine ⟨l.take n, l.drop n, ⟨mem_strs_of n _ (by simp; omega)
      (fun d hd' => hd d (List.mem_of_mem_take hd')), mem_strs_of m _ (by simp; omega)
      (fun d hd' => hd d (List.mem_of_mem_drop hd'))⟩, List.take_append_drop n l⟩
  · rintro ⟨u, v, ⟨hu, hv⟩, rfl⟩
    obtain ⟨hu1, hu2⟩ := of_mem_strs _ u hu
    obtain ⟨hv1, hv2⟩ := of_mem_strs _ v hv
    refine mem_strs_of _ _ (by simp [hu1, hv1]) ?_
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact hu2 d h
    · exact hv2 d h

private lemma sum_strs_add (b n m : ℕ) (g : List ℕ → ℝ) :
    ∑ l ∈ Normal.strs b (n + m), g l =
      ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m, g (u ++ v) := by
  rw [strs_add, Finset.sum_image, Finset.sum_product]
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at huv huv' h
  have l1 := (of_mem_strs _ u huv.1).1
  have l2 := (of_mem_strs _ u' huv'.1).1
  obtain ⟨e1, e2⟩ := List.append_inj h (by omega)
  rw [e1, e2]

private lemma Wd_add (s : ℕ → ℕ) (n m i : ℕ) : Wd s (n + m) i = Wd s n i ++ Wd s m (i + n) := by
  unfold Wd
  rw [List.ofFn_add]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp [Fin.natAdd, add_assoc]

/-! ## Exact and approximate counting identities -/

section counting

variable {b : ℕ} (s : ℕ → ℕ) (hs : ∀ n, s n < b)
include hs

private lemma Wd_mem (m i : ℕ) : Wd s m i ∈ Normal.strs b m := by
  apply mem_strs_of m _ (Wd_length s m i)
  intro d hd
  simp only [Wd, List.mem_ofFn] at hd
  obtain ⟨t, rfl⟩ := hd
  exact hs _

private lemma sum_fiber (S : Finset ℕ) (g : ℕ → ℕ) (m : ℕ) :
    ∑ v ∈ Normal.strs b m, (S.filter (fun i => Wd s m (g i) = v)).card = S.card :=
  (Finset.card_eq_sum_card_fiberwise (fun i _ => Wd_mem s hs m (g i))).symm

private lemma sum_count_strs (n N : ℕ) :
    ∑ u ∈ Normal.strs b n, Normal.count s u N = N := by
  calc ∑ u ∈ Normal.strs b n, Normal.count s u N
      = ∑ u ∈ Normal.strs b n, ((Finset.range N).filter (fun i => Wd s n (id i) = u)).card := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [count_eq, (of_mem_strs n u hu).1]
        rfl
    _ = N := by rw [sum_fiber s hs, Finset.card_range]

private lemma sum_count_right (n m : ℕ) (u : List ℕ) (hu : u ∈ Normal.strs b n) (N : ℕ) :
    ∑ v ∈ Normal.strs b m, Normal.count s (u ++ v) N = Normal.count s u N := by
  have hun := (of_mem_strs n u hu).1
  rw [count_eq s u, hun, ← sum_fiber s hs _ (· + n) m]
  apply Finset.sum_congr rfl
  intro v hv
  have hvm := (of_mem_strs m v hv).1
  rw [count_eq, Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [List.length_append, hun, hvm, Wd_add]
  constructor
  · intro h; exact List.append_inj h (by rw [Wd_length, hun])
  · rintro ⟨h1, h2⟩; rw [h1, h2]

private lemma sum_count_left (n m : ℕ) (v : List ℕ) (hv : v ∈ Normal.strs b m) (N : ℕ) :
    ∑ u ∈ Normal.strs b n, Normal.count s (u ++ v) N =
      ((Finset.range N).filter (fun i => Wd s m (i + n) = v)).card := by
  have hvm := (of_mem_strs m v hv).1
  rw [← sum_fiber s hs _ id n]
  apply Finset.sum_congr rfl
  intro u hu
  have hun := (of_mem_strs n u hu).1
  rw [count_eq, Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [List.length_append, hun, hvm, Wd_add]
  constructor
  · intro h; exact (List.append_inj h (by rw [Wd_length, hun])).symm
  · rintro ⟨h1, h2⟩; rw [← h1, ← h2]; rfl

end counting

/-- Shifting the positions by `n` changes a count by at most `n`. -/
private lemma shift_count (P : ℕ → Prop) [DecidablePred P] (n N : ℕ) :
    ((Finset.range N).filter (fun i => P (i + n))).card ≤
      ((Finset.range N).filter P).card + n ∧
    ((Finset.range N).filter P).card ≤
      ((Finset.range N).filter (fun i => P (i + n))).card + n := by
  set f : ℕ → ℕ := fun i => if P i then 1 else 0
  have hf : ∀ i, f i ≤ 1 := fun i => by simp only [f]; split_ifs <;> omega
  have hA : ((Finset.range N).filter (fun i => P (i + n))).card = ∑ i ∈ Finset.range N, f (n + i) := by
    rw [Finset.card_filter]; apply Finset.sum_congr rfl; intro i _; simp [f, add_comm]
  have hB : ((Finset.range N).filter P).card = ∑ i ∈ Finset.range N, f i := by
    rw [Finset.card_filter]
  have e1 := Finset.sum_range_add f n N
  have e2 := Finset.sum_range_add f N n
  rw [add_comm N n] at e2
  have b1 : ∑ i ∈ Finset.range n, f i ≤ n := by
    calc ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, 1 := Finset.sum_le_sum (fun i _ => hf i)
      _ = n := by simp
  have b2 : ∑ i ∈ Finset.range n, f (N + i) ≤ n := by
    calc ∑ i ∈ Finset.range n, f (N + i) ≤ ∑ i ∈ Finset.range n, 1 :=
          Finset.sum_le_sum (fun i _ => hf _)
      _ = n := by simp
  rw [hA, hB]
  omega

/-! ## Entropy: a shift-invariant word-frequency function bounded by `C b^{-n}` is uniform -/

private lemma term_sub (J a c : ℝ) (hJ : 0 ≤ J) (ha : J ≤ a) (hc : J ≤ c) :
    Real.negMulLog J ≤ -J * Real.log a - J * Real.log c + (a * c - J) := by
  rcases eq_or_lt_of_le hJ with h | h
  · subst h; simp only [Real.negMulLog_zero, neg_zero, zero_mul, sub_zero, zero_add]
    exact mul_nonneg (by linarith) (by linarith)
  · have ha' : 0 < a := lt_of_lt_of_le h ha
    have hc' : 0 < c := lt_of_lt_of_le h hc
    have hx : 0 < a * c / J := by positivity
    have hl := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by positivity) h.ne', Real.log_mul ha'.ne' hc'.ne'] at hl
    have e : a * c / J * J = a * c := by field_simp
    have := mul_le_mul_of_nonneg_left hl h.le
    rw [Real.negMulLog]
    nlinarith

private lemma term_up (f B : ℝ) (hB : 0 < B) (hf : 0 ≤ f) :
    Real.negMulLog f ≤ f * Real.log B + (1 / B - f) := by
  rcases eq_or_lt_of_le hf with h | h
  · subst h; simp; positivity
  · have hx : 0 < 1 / (B * f) := by positivity
    have hl := Real.log_le_sub_one_of_pos hx
    rw [one_div, Real.log_inv, Real.log_mul hB.ne' h.ne'] at hl
    have := mul_le_mul_of_nonneg_left hl h.le
    have e : f * (B * f)⁻¹ = 1 / B := by field_simp
    rw [Real.negMulLog]
    nlinarith

private lemma term_eq (f B : ℝ) (hB : 0 < B) (hf : 0 ≤ f)
    (h : Real.negMulLog f = f * Real.log B + (1 / B - f)) : f = 1 / B := by
  rcases eq_or_lt_of_le hf with h0 | h0
  · subst h0; simp at h; exact absurd h (by positivity)
  · by_contra hne
    have hx : 0 < 1 / (B * f) := by positivity
    have hx1 : 1 / (B * f) ≠ 1 := by
      intro h1; apply hne; field_simp at h1 ⊢; linarith
    have hl := Real.log_lt_sub_one_of_pos hx hx1
    rw [one_div, Real.log_inv, Real.log_mul hB.ne' h0.ne'] at hl
    have := mul_lt_mul_of_pos_left hl h0
    have e : f * (B * f)⁻¹ = 1 / B := by field_simp
    rw [Real.negMulLog] at h
    nlinarith

private lemma term_low (f C B : ℝ) (hC : 0 < C) (hB : 0 < B) (hf : 0 ≤ f) (hfC : f ≤ C / B) :
    f * (Real.log B - Real.log C) ≤ Real.negMulLog f := by
  rcases eq_or_lt_of_le hf with h | h
  · subst h; simp
  · have hl : Real.log f ≤ Real.log C - Real.log B := by
      rw [← Real.log_div hC.ne' hB.ne']; exact Real.log_le_log h hfC
    rw [Real.negMulLog]
    nlinarith

private lemma uniform_of_props (b : ℕ) (hb : 2 ≤ b) (F : List ℕ → ℝ) (C : ℝ)
    (P1 : ∀ u, 0 ≤ F u)
    (P2 : ∀ n, ∀ u ∈ Normal.strs b n, F u ≤ C / (b : ℝ) ^ n)
    (P3 : ∀ n, ∑ u ∈ Normal.strs b n, F u = 1)
    (P4 : ∀ n m, ∀ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m, F (u ++ v) = F u)
    (P5 : ∀ n m, ∀ v ∈ Normal.strs b m, ∑ u ∈ Normal.strs b n, F (u ++ v) = F v) :
    ∀ n, ∀ u ∈ Normal.strs b n, F u = 1 / (b : ℝ) ^ n := by
  set H : ℕ → ℝ := fun n => ∑ u ∈ Normal.strs b n, Real.negMulLog (F u) with hH
  have hb0 : (0 : ℝ) < b := by positivity
  have hcard : ∀ n, ((Normal.strs b n).card : ℝ) = (b : ℝ) ^ n := fun n => by
    rw [card_strs]; push_cast; ring
  -- `C > 0`
  have hCpos : 0 < C := by
    by_contra hC
    push Not at hC
    have h1 := P3 0
    have : ∑ u ∈ Normal.strs b 0, F u ≤ 0 :=
      Finset.sum_nonpos (fun u hu => (P2 0 u hu).trans (by simp; linarith))
    linarith
  -- E1
  have E1 : ∀ n : ℕ, (n : ℝ) * Real.log b - Real.log C ≤ H n := by
    intro n
    have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    calc (n : ℝ) * Real.log b - Real.log C
        = ∑ u ∈ Normal.strs b n, F u * (Real.log ((b : ℝ) ^ n) - Real.log C) := by
          rw [← Finset.sum_mul, P3, Real.log_pow]; ring
      _ ≤ H n := Finset.sum_le_sum (fun u hu => term_low _ _ _ hCpos hBn (P1 u) (P2 n u hu))
  -- E3
  have E3 : ∀ n : ℕ, H n ≤ (n : ℝ) * Real.log b := by
    intro n
    have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
    calc H n ≤ ∑ u ∈ Normal.strs b n, (F u * Real.log ((b : ℝ) ^ n) + (1 / (b : ℝ) ^ n - F u)) :=
          Finset.sum_le_sum (fun u _ => term_up _ _ hBn (P1 u))
      _ = (n : ℝ) * Real.log b := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, P3,
            Finset.sum_const, nsmul_eq_mul, hcard, Real.log_pow]
          field_simp; ring
  -- E2
  have E2 : ∀ n m, H (n + m) ≤ H n + H m := by
    intro n m
    have hJu : ∀ u ∈ Normal.strs b n, ∀ v ∈ Normal.strs b m, F (u ++ v) ≤ F u := by
      intro u hu v hv
      rw [← P4 n m u hu]
      exact Finset.single_le_sum (f := fun v => F (u ++ v)) (fun v _ => P1 _) hv
    have hJv : ∀ u ∈ Normal.strs b n, ∀ v ∈ Normal.strs b m, F (u ++ v) ≤ F v := by
      intro u hu v hv
      rw [← P5 n m v hv]
      exact Finset.single_le_sum (f := fun u => F (u ++ v)) (fun u _ => P1 _) hu
    have hHn : H n = ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m,
        -F (u ++ v) * Real.log (F u) := by
      simp only [hH]
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.sum_mul, Finset.sum_neg_distrib, P4 n m u hu, Real.negMulLog]
    have hHm : H m = ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m,
        -F (u ++ v) * Real.log (F v) := by
      rw [Finset.sum_comm]
      simp only [hH]
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_mul, Finset.sum_neg_distrib, P5 n m v hv, Real.negMulLog]
    have hHnm : H (n + m) = ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m,
        Real.negMulLog (F (u ++ v)) := by
      simp only [hH]; rw [sum_strs_add]
    have hprod : ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m, F u * F v = 1 := by
      rw [← Finset.sum_mul_sum, P3, P3]; ring
    have hJsum : ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m, F (u ++ v) = 1 := by
      rw [Finset.sum_congr rfl (fun u hu => P4 n m u hu), P3]
    calc H (n + m) ≤ ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m,
          (-F (u ++ v) * Real.log (F u) - F (u ++ v) * Real.log (F v) +
            (F u * F v - F (u ++ v))) := by
          rw [hHnm]
          apply Finset.sum_le_sum; intro u hu
          apply Finset.sum_le_sum; intro v hv
          exact term_sub _ _ _ (P1 _) (hJu u hu v hv) (hJv u hu v hv)
      _ = H n + H m + (∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m, F u * F v -
            ∑ u ∈ Normal.strs b n, ∑ v ∈ Normal.strs b m, F (u ++ v)) := by
          rw [hHn, hHm]
          simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro u _
          apply Finset.sum_congr rfl; intro v _
          ring
      _ = H n + H m := by rw [hprod, hJsum]; ring
  -- E4
  have Emul : ∀ n k, H (n * (k + 1)) ≤ (k + 1 : ℝ) * H n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      have := E2 (n * (k + 1)) n
      rw [show n * (k + 1) + n = n * (k + 1 + 1) by ring] at this
      push_cast
      linarith
  have E4 : ∀ n : ℕ, (n : ℝ) * Real.log b ≤ H n := by
    intro n
    by_contra hlt
    push Not at hlt
    have hgap : 0 < (n : ℝ) * Real.log b - H n := by linarith
    obtain ⟨k, hk⟩ := exists_nat_gt (Real.log C / ((n : ℝ) * Real.log b - H n))
    have h1 := E1 (n * (k + 1))
    have h2 := Emul n k
    push_cast at h1
    rw [div_lt_iff₀ hgap] at hk
    nlinarith
  -- E5
  intro n u hu
  have hBn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hsum : ∑ u ∈ Normal.strs b n, ((F u * Real.log ((b : ℝ) ^ n) + (1 / (b : ℝ) ^ n - F u)) -
      Real.negMulLog (F u)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have : ∑ u ∈ Normal.strs b n, (F u * Real.log ((b : ℝ) ^ n) + (1 / (b : ℝ) ^ n - F u)) =
        (n : ℝ) * Real.log b := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, P3,
        Finset.sum_const, nsmul_eq_mul, hcard, Real.log_pow]
      field_simp; ring
    rw [this]
    have := E3 n; have := E4 n
    simp only [hH] at *
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
    sub_nonneg.2 (term_up (F u) _ hBn (P1 u)))).1 hsum u hu
  exact term_eq _ _ hBn (P1 u) (by linarith)

private lemma digit_lt' (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (m : ℕ) : Normal.digit b x m < b := by
  unfold Normal.digit
  have h0 := Int.emod_nonneg ⌊x * (b : ℝ) ^ (m + 1)⌋ (show (b : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos ⌊x * (b : ℝ) ^ (m + 1)⌋ (show (0 : ℤ) < b by omega)
  omega

/-- The Pyatetskii-Shapiro criterion, proved via subsequential limits of word frequencies
and the uniqueness of the measure of maximal entropy. -/
private theorem ps_main (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (C : ℝ)
    (hC : ∀ w : List ℕ, (∀ d ∈ w, d < b) → ∀ᶠ N : ℕ in Filter.atTop,
      (Normal.count (Normal.digit b x) w N : ℝ) ≤ C * N / (b : ℝ) ^ w.length) :
    Normal.IsNormalReal b x := by
  unfold Normal.IsNormalReal Normal.IsNormalSeq
  set s := Normal.digit b x with hsdef
  have hs : ∀ n, s n < b := digit_lt' b hb x
  intro w hw
  set n := w.length
  by_contra hne
  obtain ⟨ε, hε, hfr⟩ : ∃ ε > 0, ∃ᶠ N in atTop,
      ε ≤ dist ((Normal.count s w N : ℝ) / N) ((b : ℝ) ^ n)⁻¹ := by
    rw [Metric.tendsto_atTop] at hne
    push Not at hne
    obtain ⟨ε, hε, h⟩ := hne
    exact ⟨ε, hε, Filter.frequently_atTop.2 h⟩
  obtain ⟨ψ0, hψ0, hP⟩ := Filter.extraction_of_frequently_atTop hfr
  set V : ℕ → List ℕ → ℝ := fun j u => (Normal.count s u (ψ0 j) : ℝ) / ψ0 j
  have hV : ∀ j, V j ∈ Set.pi Set.univ (fun _ : List ℕ => Set.Icc (0 : ℝ) 1) := by
    intro j u _
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos (ψ0 j) with h | h
    · simp [V, h]
    · exact div_le_one_of_le₀ (by exact_mod_cast count_le s u _) (by positivity)
  obtain ⟨F, _, φ, hφ, hlim⟩ := (isCompact_univ_pi (fun _ => isCompact_Icc)).tendsto_subseq hV
  rw [tendsto_pi_nhds] at hlim
  set ψ := ψ0 ∘ φ with hψdef
  have hψ : StrictMono ψ := hψ0.comp hφ
  have hlimF : ∀ u, Tendsto (fun j => (Normal.count s u (ψ j) : ℝ) / ψ j) atTop (𝓝 (F u)) :=
    fun u => hlim u
  have hψpos : ∀ᶠ j in atTop, (0 : ℝ) < ψ j := by
    filter_upwards [Filter.eventually_ge_atTop 1] with j hj
    have := hψ.id_le j
    exact_mod_cast (show 0 < ψ j by simp at this; omega)
  have hψtop : Tendsto (fun j => (ψ j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
  -- the five properties of `F`
  have P1 : ∀ u, 0 ≤ F u := fun u => ge_of_tendsto' (hlimF u) (fun j => by positivity)
  have P2 : ∀ m, ∀ u ∈ Normal.strs b m, F u ≤ C / (b : ℝ) ^ m := by
    intro m u hu
    obtain ⟨hl, hd⟩ := of_mem_strs m u hu
    have h1 := hψ.tendsto_atTop.eventually (hC u hd)
    refine le_of_tendsto (hlimF u) ?_
    filter_upwards [h1, hψpos] with j h hp
    rw [div_le_iff₀ hp]
    rw [hl] at h
    calc (Normal.count (Normal.digit b x) u (ψ j) : ℝ) ≤ C * (ψ j) / (b : ℝ) ^ m := h
      _ = C / (b : ℝ) ^ m * ψ j := by ring
  have P3 : ∀ m, ∑ u ∈ Normal.strs b m, F u = 1 := by
    intro m
    have h1 := tendsto_finsetSum (Normal.strs b m) (fun u _ => hlimF u)
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [hψpos] with j hp
    rw [← Finset.sum_div]
    have := sum_count_strs s hs m (ψ j)
    rw [show (∑ u ∈ Normal.strs b m, (Normal.count s u (ψ j) : ℝ)) = (ψ j : ℝ) by
      exact_mod_cast this]
    exact (div_self hp.ne').symm
  have P4 : ∀ m k, ∀ u ∈ Normal.strs b m, ∑ v ∈ Normal.strs b k, F (u ++ v) = F u := by
    intro m k u hu
    have h1 := tendsto_finsetSum (Normal.strs b k) (fun v _ => hlimF (u ++ v))
    refine tendsto_nhds_unique h1 ((hlimF u).congr' (Eventually.of_forall fun j => ?_))
    show (Normal.count s u (ψ j) : ℝ) / ψ j =
      ∑ v ∈ Normal.strs b k, (Normal.count s (u ++ v) (ψ j) : ℝ) / ψ j
    rw [← Finset.sum_div]
    have := sum_count_right s hs m k u hu (ψ j)
    rw [show (∑ v ∈ Normal.strs b k, (Normal.count s (u ++ v) (ψ j) : ℝ)) =
      (Normal.count s u (ψ j) : ℝ) by exact_mod_cast this]
  have P5 : ∀ m k, ∀ v ∈ Normal.strs b k, ∑ u ∈ Normal.strs b m, F (u ++ v) = F v := by
    intro m k v hv
    have hvk := (of_mem_strs k v hv).1
    have h1 := tendsto_finsetSum (Normal.strs b m) (fun u _ => hlimF (u ++ v))
    have h2 := (h1.sub (hlimF v))
    have h3 : Tendsto (fun j => ∑ u ∈ Normal.strs b m,
        (Normal.count s (u ++ v) (ψ j) : ℝ) / ψ j - (Normal.count s v (ψ j) : ℝ) / ψ j)
        atTop (𝓝 0) := by
      have hz : Tendsto (fun j => (m : ℝ) / ψ j) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hψtop
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [hψpos] with j hp
      rw [← Finset.sum_div, ← sub_div, norm_div, Real.norm_of_nonneg hp.le,
        div_le_div_iff_of_pos_right hp]
      have e1 := sum_count_left s hs m k v hv (ψ j)
      have e2 := count_eq s v (ψ j)
      rw [hvk] at e2
      obtain ⟨c1, c2⟩ := shift_count (fun i => Wd s k i = v) m (ψ j)
      rw [Real.norm_eq_abs, abs_le]
      have q1 : (∑ u ∈ Normal.strs b m, (Normal.count s (u ++ v) (ψ j) : ℝ)) =
          (((Finset.range (ψ j)).filter (fun i => Wd s k (i + m) = v)).card : ℝ) := by
        exact_mod_cast e1
      have q2 : (Normal.count s v (ψ j) : ℝ) =
          (((Finset.range (ψ j)).filter (fun i => Wd s k i = v)).card : ℝ) := by
        exact_mod_cast e2
      rw [q1, q2]
      have r1 : (((Finset.range (ψ j)).filter (fun i => Wd s k (i + m) = v)).card : ℝ) ≤
          (((Finset.range (ψ j)).filter (fun i => Wd s k i = v)).card : ℝ) + m := by
        exact_mod_cast c1
      have r2 : (((Finset.range (ψ j)).filter (fun i => Wd s k i = v)).card : ℝ) ≤
          (((Finset.range (ψ j)).filter (fun i => Wd s k (i + m) = v)).card : ℝ) + m := by
        exact_mod_cast c2
      constructor <;> linarith
    have := tendsto_nhds_unique h2 h3
    linarith
  have hunif := uniform_of_props b hb F C P1 P2 P3 P4 P5 n w (mem_strs_of n w rfl hw)
  -- contradiction with the choice of `ψ0`
  have hd : Tendsto (fun j => dist ((Normal.count s w (ψ j) : ℝ) / ψ j) ((b : ℝ) ^ n)⁻¹) atTop
      (𝓝 (dist (F w) ((b : ℝ) ^ n)⁻¹)) := (hlimF w).dist tendsto_const_nhds
  have hge := ge_of_tendsto' hd (fun j => hP (φ j))
  rw [hunif, one_div, dist_self] at hge
  linarith



/-- `Dv d b i n = d i b^(n-1) + ⋯ + d (i+n-1)`, the integer written by `n` digits from `i`. -/
private def Dv (d : ℕ → ℕ) (b i : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (b : ℤ) * Dv d b i n + d (i + n)

private lemma Dv_congr2 (d d' : ℕ → ℕ) (b i j : ℕ) :
    ∀ n, (∀ t < n, d (i + t) = d' (j + t)) → Dv d b i n = Dv d' b j n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Dv]
    rw [Dv_congr2 d d' b i j n (fun t ht => h t (by omega)), h n (by omega)]

private lemma Dv_inj (d d' : ℕ → ℕ) (b i j : ℕ) :
    ∀ n, (∀ t < n, d (i + t) < b) → (∀ t < n, d' (j + t) < b) →
      Dv d b i n = Dv d' b j n → ∀ t < n, d (i + t) = d' (j + t)
  | 0, _, _, _ => fun t ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, h1, h2, h => by
    simp only [Dv] at h
    have a1 : ((d (i + n) : ℕ) : ℤ) < b := by exact_mod_cast h1 n (by omega)
    have a2 : ((d' (j + n) : ℕ) : ℤ) < b := by exact_mod_cast h2 n (by omega)
    have a1' : (0 : ℤ) ≤ ((d (i + n) : ℕ) : ℤ) := by positivity
    have a2' : (0 : ℤ) ≤ ((d' (j + n) : ℕ) : ℤ) := by positivity
    have hXY : Dv d b i n = Dv d' b j n := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hl
      · have : (b : ℤ) * (Dv d b i n + 1) ≤ (b : ℤ) * Dv d' b j n :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
      · have : (b : ℤ) * (Dv d' b j n + 1) ≤ (b : ℤ) * Dv d b i n :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
    have hlast : d (i + n) = d' (j + n) := by
      rw [hXY] at h; exact_mod_cast (by linarith : ((d (i + n) : ℕ) : ℤ) = d' (j + n))
    intro t ht
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · exact Dv_inj d d' b i j n (fun t ht => h1 t (by omega)) (fun t ht => h2 t (by omega))
        hXY t ht
    · subst ht; exact hlast

/-- `⌊ξ b^(m+1)⌋ = b ⌊ξ b^m⌋ + digit m`. -/
private lemma floor_succ (ξ : ℝ) {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    ⌊ξ * (b : ℝ) ^ (m + 1)⌋ = (b : ℤ) * ⌊ξ * (b : ℝ) ^ m⌋ + (Normal.digit b ξ m : ℤ) := by
  set a := ⌊ξ * (b : ℝ) ^ m⌋ with ha
  set c := ⌊ξ * (b : ℝ) ^ (m + 1)⌋ with hc
  have hbpos : (0 : ℝ) < b := by positivity
  have h1 : (a : ℝ) ≤ ξ * (b : ℝ) ^ m := Int.floor_le _
  have h2 : ξ * (b : ℝ) ^ m < a + 1 := Int.lt_floor_add_one _
  have e : ξ * (b : ℝ) ^ (m + 1) = (ξ * (b : ℝ) ^ m) * b := by ring
  have hlo : (b : ℤ) * a ≤ c := by
    rw [hc, Int.le_floor, e]; push_cast; nlinarith
  have hhi : c < (b : ℤ) * a + b := by
    have : (c : ℝ) < (b : ℝ) * a + b := by
      calc (c : ℝ) ≤ ξ * (b : ℝ) ^ (m + 1) := Int.floor_le _
        _ < (b : ℝ) * a + b := by rw [e]; nlinarith
    exact_mod_cast this
  have hdig : (Normal.digit b ξ m : ℤ) = c % (b : ℤ) := by
    unfold Normal.digit
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  rw [hdig]
  have hr : c = (c - b * a) + b * a := by ring
  have hmod : c % (b : ℤ) = c - b * a := by
    rw [hr, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    ring
  rw [hmod]; ring

private lemma floor_add (ξ : ℝ) {b : ℕ} (hb : 2 ≤ b) (i : ℕ) :
    ∀ n, ⌊ξ * (b : ℝ) ^ (i + n)⌋ =
      (b : ℤ) ^ n * ⌊ξ * (b : ℝ) ^ i⌋ + Dv (Normal.digit b ξ) b i n
  | 0 => by simp [Dv]
  | n + 1 => by
    rw [show i + (n + 1) = (i + n) + 1 by omega, floor_succ ξ hb, floor_add ξ hb i n, Dv]
    ring

/-- The value of a word, most significant digit first. -/
private def valL (b : ℕ) (W : List ℕ) : ℤ := Dv (fun t => W.getD t 0) b 0 W.length

private lemma valL_inj {b k : ℕ} {W1 W2 : List ℕ} (h1 : W1 ∈ Normal.strs b k)
    (h2 : W2 ∈ Normal.strs b k) (h : valL b W1 = valL b W2) : W1 = W2 := by
  obtain ⟨l1, d1⟩ := of_mem_strs k W1 h1
  obtain ⟨l2, d2⟩ := of_mem_strs k W2 h2
  unfold valL at h
  rw [l1, l2] at h
  have key := Dv_inj (fun t => W1.getD t 0) (fun t => W2.getD t 0) b 0 0 k
    (fun t ht => by
      simp only [zero_add]; rw [List.getD_eq_getElem _ _ (by omega)]
      exact d1 _ (List.getElem_mem _))
    (fun t ht => by
      simp only [zero_add]; rw [List.getD_eq_getElem _ _ (by omega)]
      exact d2 _ (List.getElem_mem _)) h
  apply List.ext_getElem (by omega)
  intro t ht1 ht2
  have := key t (by omega)
  simp only [zero_add] at this
  rwa [List.getD_eq_getElem _ _ ht1, List.getD_eq_getElem _ _ ht2] at this

/-- The digit word of length `n` at position `i`. -/
private noncomputable def dw (b : ℕ) (x : ℝ) (n i : ℕ) : List ℕ :=
  List.ofFn (fun t : Fin n => Normal.digit b x (i + t))

/-- `E m = p ⌊x b^m⌋ - q ⌊z b^m⌋` lies strictly between `-|p|` and `q + |p|` when `q z = p x`. -/
private lemma E_bound (b : ℕ) (x z : ℝ) (p : ℤ) (hp : p ≠ 0) (q : ℕ) (hz : (q : ℝ) * z = p * x)
    (m : ℕ) :
    p * ⌊x * (b : ℝ) ^ m⌋ - q * ⌊z * (b : ℝ) ^ m⌋ ∈ Finset.Ioo (-|p|) (q + |p|) := by
  set X := x * (b : ℝ) ^ m
  set Z := z * (b : ℝ) ^ m
  have hZX : (q : ℝ) * Z = p * X := by simp only [X, Z]; rw [← mul_assoc, hz]; ring
  have l1 : ((⌊X⌋ : ℤ) : ℝ) ≤ X := Int.floor_le _
  have u1 : X < ((⌊X⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have l2 : ((⌊Z⌋ : ℤ) : ℝ) ≤ Z := Int.floor_le _
  have u2 : Z < ((⌊Z⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hE : ((p * ⌊X⌋ - q * ⌊Z⌋ : ℤ) : ℝ) =
      -(p : ℝ) * (X - ⌊X⌋) + q * (Z - ⌊Z⌋) := by
    push_cast; linarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hpa : (0 : ℝ) < |(p : ℝ)| := by rw [abs_pos]; exact_mod_cast hp
  have t1 : -(p : ℝ) * (X - ⌊X⌋) ≥ -(|(p : ℝ)| * (X - ⌊X⌋)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self (p : ℝ)) (show 0 ≤ X - ⌊X⌋ by linarith)
    linarith
  have t2 : -(p : ℝ) * (X - ⌊X⌋) ≤ |(p : ℝ)| * (X - ⌊X⌋) :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
  have t3 : |(p : ℝ)| * (X - ⌊X⌋) < |(p : ℝ)| := by
    have := mul_lt_mul_of_pos_left (show X - ⌊X⌋ < 1 by linarith) hpa
    linarith
  have t4 : (q : ℝ) * (Z - ⌊Z⌋) ≤ q := by
    have := mul_le_mul_of_nonneg_left (show Z - ⌊Z⌋ ≤ 1 by linarith) hq0
    linarith
  have t5 : (0 : ℝ) ≤ (q : ℝ) * (Z - ⌊Z⌋) := mul_nonneg hq0 (by linarith)
  have lo : ((-|p| : ℤ) : ℝ) < ((p * ⌊X⌋ - q * ⌊Z⌋ : ℤ) : ℝ) := by
    rw [hE]; push_cast; linarith
  have hi : ((p * ⌊X⌋ - q * ⌊Z⌋ : ℤ) : ℝ) < ((q + |p| : ℤ) : ℝ) := by
    rw [hE]; push_cast; linarith
  rw [Finset.mem_Ioo]
  exact ⟨by exact_mod_cast lo, by exact_mod_cast hi⟩

/-- The words `W` of length `|w|` whose occurrence in `x` is compatible with an occurrence of
`w` in `z = (p/q) x`. -/
private noncomputable def Tset (b : ℕ) (p : ℤ) (q : ℕ) (w : List ℕ) : Finset (List ℕ) :=
  (Normal.strs b w.length).filter (fun W => ∃ c ∈ Finset.Ioo (-|p|) ((q : ℤ) + |p|),
    c * (b : ℤ) ^ w.length + p * valL b W - q * valL b w ∈ Finset.Ioo (-|p|) ((q : ℤ) + |p|))

private lemma Tset_card (b : ℕ) (p : ℤ) (hp : p ≠ 0) (q : ℕ) (w : List ℕ) :
    (Tset b p q w).card ≤
      (Finset.Ioo (-|p|) ((q : ℤ) + |p|)).card * (Finset.Ioo (-|p|) ((q : ℤ) + |p|)).card := by
  set I := Finset.Ioo (-|p|) ((q : ℤ) + |p|)
  have hsub : Tset b p q w ⊆ I.biUnion (fun c => (Normal.strs b w.length).filter
      (fun W => c * (b : ℤ) ^ w.length + p * valL b W - q * valL b w ∈ I)) := by
    intro W hW
    rw [Tset, Finset.mem_filter] at hW
    obtain ⟨hWs, c, hc, hcW⟩ := hW
    exact Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_filter.2 ⟨hWs, hcW⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  refine (Finset.sum_le_sum (g := fun _ => I.card) ?_).trans
    (by rw [Finset.sum_const, smul_eq_mul])
  intro c _
  apply Finset.card_le_card_of_injOn
    (fun W => c * (b : ℤ) ^ w.length + p * valL b W - q * valL b w)
  · intro W hW
    exact (Finset.mem_filter.1 hW).2
  · intro W1 h1 W2 h2 h12
    simp only at h12
    have : p * valL b W1 = p * valL b W2 := by linarith
    exact valL_inj (Finset.mem_filter.1 h1).1 (Finset.mem_filter.1 h2).1
      (mul_left_cancel₀ hp this)

private lemma count_bound {b : ℕ} (hb : 2 ≤ b) (x z : ℝ) (p : ℤ) (hp : p ≠ 0) (q : ℕ)
    (hz : (q : ℝ) * z = p * x) (w : List ℕ) (N : ℕ) :
    Normal.count (Normal.digit b z) w N ≤
      ∑ W ∈ Tset b p q w, Normal.count (Normal.digit b x) W N := by
  unfold Normal.count
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnN, hzn⟩ := hn
  set k := w.length
  have hlen : (dw b x k n).length = k := by simp [dw]
  have hvx : valL b (dw b x k n) = Dv (Normal.digit b x) b n k := by
    unfold valL; rw [hlen]
    apply Dv_congr2
    intro t ht
    simp [dw, List.getD_eq_getElem?_getD, ht]
  have hvz : valL b w = Dv (Normal.digit b z) b n k := by
    unfold valL
    apply Dv_congr2
    intro t ht
    rw [zero_add, List.getD_eq_getElem _ _ ht]
    exact (hzn ⟨t, ht⟩).symm
  refine Finset.mem_biUnion.2 ⟨dw b x k n, ?_, Finset.mem_filter.2 ⟨hnN, ?_⟩⟩
  · rw [Tset, Finset.mem_filter]
    refine ⟨mem_strs_of k _ hlen ?_, _, E_bound b x z p hp q hz n, ?_⟩
    · intro d hd
      simp only [dw, List.mem_ofFn] at hd
      obtain ⟨t, rfl⟩ := hd
      exact digit_lt' b hb x _
    · have h := E_bound b x z p hp q hz (n + k)
      rw [floor_add x hb n k, floor_add z hb n k] at h
      rw [hvx, hvz]
      convert h using 1
      ring
  · rintro ⟨j, hj⟩
    simp only [List.get_eq_getElem]
    simp [dw]

theorem solution {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : Normal.IsNormalReal b x) (a : ℚ) (ha : a ≠ 0) :
    Normal.IsNormalReal b (x * (a : ℝ)) := by
  set p : ℤ := a.num with hpdef
  set q : ℕ := a.den with hqdef
  have hp : p ≠ 0 := Rat.num_ne_zero.2 ha
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast a.den_nz
  have hz : (q : ℝ) * (x * (a : ℝ)) = p * x := by
    rw [Rat.cast_def a]
    field_simp
    rw [hpdef, hqdef]
    ring
  set M : ℕ := (Finset.Ioo (-|p|) ((q : ℤ) + |p|)).card
  apply ps_main b hb _ (2 * (M : ℝ) ^ 2)
  intro w hw
  set k := w.length
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ∀ W ∈ Tset b p q w,
      (Normal.count (Normal.digit b x) W N : ℝ) ≤ 2 * N / (b : ℝ) ^ k := by
    rw [Filter.eventually_all_finset]
    intro W hW
    obtain ⟨hl, hd⟩ := of_mem_strs k W (Finset.mem_filter.1 hW).1
    have ht := hx W hd
    rw [hl] at ht
    have hpos : (0 : ℝ) < ((b : ℝ) ^ k)⁻¹ := by positivity
    filter_upwards [(tendsto_order.1 ht).2 (2 * ((b : ℝ) ^ k)⁻¹) (by linarith),
      Filter.eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have := (div_lt_iff₀ hNpos).1 hN
    calc (Normal.count (Normal.digit b x) W N : ℝ) ≤ 2 * ((b : ℝ) ^ k)⁻¹ * N := this.le
      _ = 2 * N / (b : ℝ) ^ k := by ring
  filter_upwards [hev] with N hN
  have hT := Tset_card b p hp q w
  calc (Normal.count (Normal.digit b (x * (a : ℝ))) w N : ℝ)
      ≤ ∑ W ∈ Tset b p q w, (Normal.count (Normal.digit b x) W N : ℝ) := by
        exact_mod_cast count_bound hb x _ p hp q hz w N
    _ ≤ ∑ W ∈ Tset b p q w, 2 * (N : ℝ) / (b : ℝ) ^ k := Finset.sum_le_sum hN
    _ = (Tset b p q w).card * (2 * (N : ℝ) / (b : ℝ) ^ k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M * M : ℕ) : ℝ) * (2 * (N : ℝ) / (b : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (by positivity)
    _ = 2 * (M : ℝ) ^ 2 * N / (b : ℝ) ^ k := by push_cast; ring

