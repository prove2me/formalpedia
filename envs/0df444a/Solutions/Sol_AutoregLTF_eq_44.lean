-- Prove2me | solution 1 for AutoregLTF.eq_44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.524831+00:00
-- url     : https://prove2.me/submissions/3ca4d713-d4cc-4607-b02c-32a22a96c841

import Mathlib
import Definitions.Def_AutoregLTF_gen16
import Definitions.Def_AutoregLTF_prompt
import Theorems.Thm_AutoregLTF_eq_39
import Theorems.Thm_AutoregLTF_lemma_1

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Eq44
open AutoregLTF

lemma zAt_step {d : ℕ} (P : ℕ) (hP : P + 1 ≤ d) (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (x : Fin d → Bool) (n : ℤ) (hn : 1 ≤ n) :
    zAt (wOf d P B a) x n = decide (0 ≤ -B + ∑ ℓ : Fin (P + 1),
      a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ)) := by
  set k : ℕ := (n + d - 1).toNat with hk
  have hkd : ¬ k < d := by omega
  have h1 : zAt (wOf d P B a) x n =
      decide (1 ≤ ∑ ℓ : Fin d, wOf d P B a ℓ * ((traj (wOf d P B a) x (k - 1 - ℓ.val)).toNat : ℚ)) := by
    unfold zAt
    rw [← hk, traj, dif_neg hkd]
  have hz : ∀ ℓ : ℕ, ℓ + 1 ≤ d → (zAt (wOf d P B a) x (n - (ℓ + 1))) =
      traj (wOf d P B a) x (k - 1 - ℓ) := by
    intro ℓ hℓ
    unfold zAt
    congr 1
    omega
  set c : ℕ → ℚ := fun ℓ => ((zAt (wOf d P B a) x (n - (ℓ + 1))).toNat : ℚ) with hc
  have h2 : ∑ ℓ : Fin d, wOf d P B a ℓ * ((traj (wOf d P B a) x (k - 1 - ℓ.val)).toNat : ℚ) =
      ∑ ℓ ∈ Finset.range d, (if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0) := by
    rw [Finset.sum_range (fun ℓ => (if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0))]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    have := ℓ.isLt
    simp only [wOf, hc]
    rw [hz ℓ.val (by omega)]
    by_cases h : ℓ.val ≤ P
    · simp [h]
    · simp [h]
  have h3 : ∑ ℓ ∈ Finset.range d, (if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0) =
      ∑ ℓ : Fin (P + 1), (a (ℓ.val + 1) : ℚ) / B * c ℓ.val := by
    rw [← Finset.sum_range_add_sum_Ico _ hP, Finset.sum_eq_zero (s := Finset.Ico (P + 1) d)]
    · rw [add_zero, Finset.sum_range (fun ℓ => if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0)]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      have := ℓ.isLt
      have : ℓ.val ≤ P := by omega
      simp [this]
    · intro ℓ hℓ
      rw [Finset.mem_Ico] at hℓ
      have : ¬ ℓ ≤ P := by omega
      simp [this]
  rw [h1, h2, h3]
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have h4 : ∑ ℓ : Fin (P + 1), (a (ℓ.val + 1) : ℚ) / B * c ℓ.val =
      ((∑ ℓ : Fin (P + 1), a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ) : ℤ) : ℚ) / B := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    simp only [hc]; ring
  rw [h4]
  apply decide_eq_decide.mpr
  rw [le_div_iff₀ hBq, one_mul]
  constructor
  · intro h
    have : (B : ℚ) ≤ ((∑ ℓ : Fin (P + 1), a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ) : ℤ) : ℚ) := h
    have := (Int.cast_le (R := ℚ)).mp this
    omega
  · intro h
    have : B ≤ ∑ ℓ : Fin (P + 1), a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ) := by omega
    exact_mod_cast this

lemma zAt_prompt {d : ℕ} (w : Fin d → ℚ) (x : Fin d → Bool) (n : ℤ) (h1 : 1 - (d : ℤ) ≤ n)
    (h2 : n ≤ 0) : zAt w x n = x ⟨(n + d - 1).toNat, by omega⟩ := by
  unfold zAt
  rw [traj, dif_pos (by omega)]

lemma any_congr' (l : List ℕ) (P Q : ℕ → Bool) (h : ∀ j ∈ l, P j = Q j) : l.any P = l.any Q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.any_cons, List.any_cons, h x (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma block_congr (m : ℕ) (f g : St) (r : ℕ)
    (hrow : ∀ j ∈ Finset.Icc 1 m, f.row j = g.row j) (htest : f.test = g.test)
    (hout : ∀ j ∈ Finset.Icc 1 m, f.out j = g.out j)
    (hptr : ∀ j ∈ Finset.Icc 1 (m + 1), f.ptr j = g.ptr j) : block m f r = block m g r := by
  have h1 := any_congr' (List.range' 1 m) (fun j => decide (r = piRow m j) && f.row j)
    (fun j => decide (r = piRow m j) && g.row j) (fun j hj => by
      rw [List.mem_range'] at hj
      rw [hrow j (by rw [Finset.mem_Icc]; omega)])
  have h2 := any_congr' (List.range' 1 m)
    (fun j => (decide (r = piOut m j) || decide (r = piOut m j + 1)) && f.out j)
    (fun j => (decide (r = piOut m j) || decide (r = piOut m j + 1)) && g.out j) (fun j hj => by
      rw [List.mem_range'] at hj
      rw [hout j (by rw [Finset.mem_Icc]; omega)])
  have h3 := any_congr' (List.range' 1 (m + 1))
    (fun j => (decide (r = piPtr m j) || decide (r = piPtr m j + 1)) && f.ptr j)
    (fun j => (decide (r = piPtr m j) || decide (r = piPtr m j + 1)) && g.ptr j) (fun j hj => by
      rw [List.mem_range'] at hj
      rw [hptr j (by rw [Finset.mem_Icc]; omega)])
  unfold block
  rw [h1, h2, h3, htest]

lemma block_out (m : ℕ) (f : St) (s : ℕ) (hs : s ∈ Finset.Icc 1 m) :
    block m f (piOut m s) = f.out s := by
  rw [Finset.mem_Icc] at hs
  have hp : p m = 378 * (m + 2) := rfl
  rw [Bool.eq_iff_iff]
  simp only [block, Bool.or_eq_true, List.any_eq_true, List.mem_range', Bool.and_eq_true]
  constructor
  · intro h'
    rcases h' with (((h | ⟨j, ⟨i, hi, hj⟩, h, -⟩) | ⟨h, -⟩) | ⟨j, ⟨i, hi, hj⟩, h, hf⟩) |
      ⟨j, ⟨i, hi, hj⟩, h, -⟩
    · have := of_decide_eq_true h; simp only [piOut] at this; omega
    · have := of_decide_eq_true h; simp only [piOut, piRow] at this; omega
    · rcases h with h | h <;> (have := of_decide_eq_true h; simp only [piOut, piTest] at this; omega)
    · rcases h with h | h
      · have := of_decide_eq_true h
        simp only [piOut] at this
        obtain rfl : j = s := by omega
        exact hf
      · have := of_decide_eq_true h; simp only [piOut] at this; omega
    · rcases h with h | h <;> (have := of_decide_eq_true h; simp only [piOut, piPtr] at this; omega)
  · intro h
    exact Or.inl (Or.inr ⟨s, ⟨s - 1, by omega, by omega⟩, Or.inl (by simp), h⟩)

lemma E_zero (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (i : ℕ) (hi : i ∈ Finset.Icc 1 m)
    (t : ℕ) (ht : t ≤ 1) (r : ℕ) :
    E m (fun _ => 0) i t r = E m (enc m lab) i t r := by
  have h := (AutoregLTF.lemma_1 m hm lab).2 (fun _ _ => false) i hi t ht
  have henc : enc m (fun _ _ => false) = fun _ => 0 := by
    funext j; simp [enc]
  rw [henc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact (block_congr m _ _ r h1 h2 h3 h4).symm

lemma prompt0_val {d : ℕ} (w : Fin d → ℚ) (m : ℕ) (θ : ℕ → ℤ) (i : ℕ) (n : ℤ)
    (h1 : 1 - (d : ℤ) ≤ n) (h2 : n ≤ 0) :
    zAt w (prompt0 m d θ i) n =
      if n ≤ -(p m : ℤ) then false else E m θ i 0 (n + p m - 1).toNat := by
  rw [zAt_prompt w _ n h1 h2]
  have : (((n + d - 1).toNat : ℕ) : ℤ) + 1 - d = n := by omega
  simp only [prompt0, this]

lemma zAt_strE (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (d : ℕ) (hd : p m + 1 ≤ d)
    (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m (enc m lab) i t) (p m + 1 + r) = E m (enc m lab) i (t + 1) r)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (n : ℤ) (h1 : 1 - (d : ℤ) ≤ n) (h2 : n ≤ p m) :
    zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i) n = strE m d i n := by
  by_cases hn : n ≤ 0
  · rw [prompt0_val _ _ _ _ _ h1 hn]
    by_cases hn2 : n ≤ -(p m : ℤ)
    · rw [if_pos hn2]
      simp [strE, hn2, show ¬ n < 1 - (d : ℤ) by omega]
    · rw [if_neg hn2]
      have : ¬ n < 1 - (d : ℤ) := by omega
      simp only [strE, this, if_false, hn2, hn, if_true]
      exact (E_zero m hm lab i hi 0 (by omega) _).symm
  · have h := (AutoregLTF.eq_39 m hm lab d hd B hB a ha i hi 1).2 (n - 1).toNat (by omega)
    have e : (((1 : ℕ) : ℤ) - 1) * p m + 1 + (((n - 1).toNat : ℕ) : ℤ) = n := by
      push_cast; omega
    rw [e] at h
    rw [h]
    have : ¬ n < 1 - (d : ℤ) := by omega
    have h3 : ¬ n ≤ -(p m : ℤ) := by omega
    have h4 : ¬ n ≤ 0 := hn
    simp only [strE, this, if_false, h3, h4, h2, if_true]
    exact (E_zero m hm lab i hi 1 le_rfl _).symm

lemma main_traj (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (d : ℕ) (hd : p m + 1 ≤ d)
    (T : ℕ) (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m (enc m lab) i t) (p m + 1 + r) = E m (enc m lab) i (t + 1) r)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (s : ℕ) (hrs0 : 0 ≤ rs m T s) (hrs1 : rs m T s < p m) :
    ∀ n : ℕ, zAt (wOf d (p m) B a) (prompt m d T i s) ((n : ℤ) + 1 - d) =
      zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i) (rs m T s + ((n : ℤ) + 1 - d)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    by_cases hnd : n < d
    · rw [zAt_prompt _ _ _ (by omega) (by omega)]
      rw [zAt_strE m hm lab d hd B hB a ha i hi _ (by omega) (by omega)]
      simp only [prompt]
      congr 2
      omega
    · rw [zAt_step (p m) hd B hB a _ _ (by omega),
        zAt_step (p m) hd B hB a _ _ (by omega)]
      refine decide_eq_decide.mpr ?_
      have : ∑ ℓ : Fin (p m + 1), a (ℓ.val + 1) *
          ((zAt (wOf d (p m) B a) (prompt m d T i s) ((n : ℤ) + 1 - d - (ℓ.val + 1))).toNat : ℤ) =
          ∑ ℓ : Fin (p m + 1), a (ℓ.val + 1) *
          ((zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i)
            (rs m T s + ((n : ℤ) + 1 - d) - (ℓ.val + 1))).toNat : ℤ) := by
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        have hl := ℓ.isLt
        have e1 : (n : ℤ) + 1 - d - (ℓ.val + 1) = ((n - (ℓ.val + 1) : ℕ) : ℤ) + 1 - d := by omega
        have e2 : rs m T s + ((n : ℤ) + 1 - d) - (ℓ.val + 1) =
            rs m T s + (((n - (ℓ.val + 1) : ℕ) : ℤ) + 1 - d) := by omega
        rw [e1, e2, ihn (n - (ℓ.val + 1)) (by omega)]
      rw [this]

end AutoregLTF.Dev.Eq44

namespace AutoregLTF
open AutoregLTF.Dev.Eq44 in
theorem chk_eq_44 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (d : ℕ) (hd : p m + 1 ≤ d)
    (T : ℕ) (hT : (m + 3) * p m ≤ T) (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m (enc m lab) i t) (p m + 1 + r) = E m (enc m lab) i (t + 1) r)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (s : ℕ) (hs : s ∈ Finset.Icc 1 m) :
    let t : ℕ := (1 + ((T : ℤ) + rs m T s - 1 - piOut m s) / (p m : ℤ)).toNat
    ltf d T (wOf d (p m) B a) (prompt m d T i s) = E m (enc m lab) i t (piOut m s) ∧
    E m (enc m lab) i t (piOut m s) = (state m (enc m lab) i t).out s ∧
    (state m (enc m lab) i t).out s = lab i s := by
  intro t
  have hP : p m = 378 * (m + 2) := rfl
  have hs' := Finset.mem_Icc.mp hs
  have hQ : piOut m s < p m := by simp only [piOut]; omega
  have hQ1 : (piOut m s : ℤ) + 1 < p m := by simp only [piOut]; omega
  have hPpos : (0 : ℤ) < p m := by omega
  have hrs0 : 0 ≤ rs m T s := Int.emod_nonneg _ (by omega)
  have hrs1 : rs m T s < p m := Int.emod_lt_of_pos _ hPpos
  have hdvd : (p m : ℤ) ∣ (T : ℤ) + rs m T s - 1 - piOut m s := by
    refine ⟨-(((piOut m s : ℤ) - T + 1) / (p m : ℤ)), ?_⟩
    have := Int.emod_def ((piOut m s : ℤ) - T + 1) (p m : ℤ)
    unfold rs
    linarith
  obtain ⟨k, hk⟩ : ∃ k, k = ((T : ℤ) + rs m T s - 1 - piOut m s) / (p m : ℤ) := ⟨_, rfl⟩
  have hPk : (p m : ℤ) * k = (T : ℤ) + rs m T s - 1 - piOut m s := by
    rw [hk]; exact Int.mul_ediv_cancel' hdvd
  have hT' : (((m : ℤ) + 3)) * p m ≤ T := by exact_mod_cast hT
  have hkm : (m : ℤ) + 2 ≤ k := by
    by_contra hcon
    have h1 : k ≤ (m : ℤ) + 1 := by omega
    have h2 : (p m : ℤ) * k ≤ (p m : ℤ) * ((m : ℤ) + 1) := mul_le_mul_of_nonneg_left h1 hPpos.le
    nlinarith
  have ht : (t : ℤ) = 1 + k := by
    show (((1 + (((T : ℤ) + rs m T s - 1 - piOut m s) / (p m : ℤ))).toNat : ℕ) : ℤ) = 1 + k
    rw [← hk]; omega
  have hmain := main_traj m hm lab d hd T B hB a ha i hi s hrs0 hrs1 (T + d - 1)
  have hl : ltf d T (wOf d (p m) B a) (prompt m d T i s) =
      zAt (wOf d (p m) B a) (prompt m d T i s) (((T + d - 1 : ℕ) : ℤ) + 1 - d) := by
    unfold ltf zAt
    congr 1
    omega
  refine ⟨?_, block_out m _ s hs, ?_⟩
  · rw [hl, hmain]
    have e : rs m T s + (((T + d - 1 : ℕ) : ℤ) + 1 - d) = ((t : ℤ) - 1) * p m + 1 + (piOut m s : ℕ) := by
      rw [ht]
      have : (((T + d - 1 : ℕ) : ℤ) + 1 - d) = T := by omega
      rw [this]
      nlinarith
    rw [e]
    exact (AutoregLTF.eq_39 m hm lab d hd B hB a ha i hi t).2 _ hQ
  · exact (AutoregLTF.lemma_1 m hm lab).1 i hi s hs t (by omega)

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_eq_44 := @AutoregLTF.chk_eq_44
