-- Prove2me | solution 1 for FuzzyExtractors.Hamming.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T04:47:26.674202+00:00
-- url     : https://prove2.me/submissions/ca02a2a0-29ef-4a96-8196-26d8002cd510

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
open scoped BigOperators ENNReal NNReal
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

noncomputable def guessingMass {M I : Type*} (P : PMF (M × I)) : ℝ≥0∞ :=
  ∑' i, ⨆ w, P (w, i)

noncomputable def guessing {M I : Type*} (P : PMF (M × I)) : ℝ :=
  (guessingMass P).toReal

end FuzzyHammingProof

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

variable {M I A B : Type*}

theorem guessingMass_le_one (P : PMF (M × I)) : guessingMass P ≤ 1 := by
  calc
    guessingMass P ≤ ∑' i, ∑' w, P (w,i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact iSup_le fun w => ENNReal.le_tsum w
    _ = ∑' p, P p := by rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    _ = 1 := P.tsum_coe

theorem guessingMass_ne_top (P : PMF (M × I)) : guessingMass P ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (guessingMass_le_one P) ENNReal.one_lt_top)

theorem guessing_pos (P : PMF (M × I)) : 0 < guessing P := by
  obtain ⟨⟨w,i⟩, hp⟩ := P.support_nonempty
  have hpos : 0 < guessingMass P := by
    apply lt_of_lt_of_le (P.apply_pos_iff _ |>.mpr hp)
    exact (le_iSup (fun w => P (w,i)) w).trans (ENNReal.le_tsum i)
  exact ENNReal.toReal_pos hpos.ne' (guessingMass_ne_top P)

theorem guessing_le_one (P : PMF (M × I)) : guessing P ≤ 1 := by
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (guessingMass_le_one P)).trans_eq
    ENNReal.toReal_one

theorem avgMinEntropy_eq_neg_log_guessing (P : PMF (M × I)) :
    avgMinEntropy P = -Real.logb 2 (guessing P) := rfl

theorem mass_summable (P : PMF A) : Summable fun a => (P a).toReal :=
  ENNReal.summable_toReal P.tsum_coe_ne_top

theorem mass_tsum (P : PMF A) : ∑' a, (P a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq P.apply_ne_top, P.tsum_coe, ENNReal.toReal_one]

theorem map_equiv_apply (P : PMF A) (e : A ≃ B) (b : B) :
    (P.map e) b = P (e.symm b) := by
  rw [PMF.map_apply]
  simpa only [Equiv.eq_symm_apply, eq_comm, if_true] using
    (tsum_eq_single (e.symm b) (fun a ha => if_neg ha) :
      (∑' a, if a = e.symm b then P a else 0) =
        if e.symm b = e.symm b then P (e.symm b) else 0)

theorem statDist_map_equiv (P Q : PMF A) (e : A ≃ B) :
    statDist (P.map e) (Q.map e) = statDist P Q := by
  unfold statDist
  simp only [map_equiv_apply]
  congr 1
  exact e.symm.tsum_eq (fun v => |(P v).toReal - (Q v).toReal|)

theorem statDist_summable (P Q : PMF A) :
    Summable fun a => |(P a).toReal - (Q a).toReal| :=
  ((mass_summable P).sub (mass_summable Q)).abs

theorem guessingMass_fiber_ne_top (P : PMF (M × I)) (i : I) :
    (⨆ w, P (w,i)) ≠ ∞ := by
  exact ne_of_lt ((lt_of_le_of_lt (ENNReal.le_tsum i)
    (lt_top_iff_ne_top.mpr (guessingMass_ne_top P))))

theorem guessing_tsum (P : PMF (M × I)) :
    guessing P = ∑' i, (⨆ w, P (w,i)).toReal :=
  ENNReal.tsum_toReal_eq (guessingMass_fiber_ne_top P)

theorem guessing_summable (P : PMF (M × I)) :
    Summable fun i => (⨆ w, P (w,i)).toReal :=
  ENNReal.summable_toReal (guessingMass_ne_top P)

end FuzzyHammingProof

open scoped BigOperators Classical

namespace FuzzyHammingProof

noncomputable def average {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

variable {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]

theorem average_equiv (e : A ≃ B) (f : B → ℝ) :
    average (fun a => f (e a)) = average f := by
  unfold average
  rw [e.sum_comp, Fintype.card_congr e]

theorem average_prod (f : A × B → ℝ) :
    average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ]
  rw [← Finset.sum_div]
  ring

theorem average_const [Nonempty A] (c : ℝ) : average (fun _ : A => c) = c := by
  have h : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average, h]

theorem average_add (f g : A → ℝ) : average (fun a => f a + g a) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_mul (c : ℝ) (f : A → ℝ) : average (fun a => c * f a) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

theorem average_sum (f : A → B → ℝ) :
    average (fun a => ∑ b, f a b) = ∑ b, average (fun a => f a b) := by
  simp only [average, Finset.sum_div]
  rw [Finset.sum_comm]

theorem average_mono {f g : A → ℝ} (h : ∀ a, f a ≤ g a) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

theorem average_nonneg {f : A → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ average f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

theorem average_eval [DecidableEq A] [Nonempty B] (a : A) (f : B → ℝ) :
    average (fun h : A → B => f (h a)) = average f := by
  let e := Equiv.funSplitAt a B
  have he := average_equiv e (fun p => f p.1)
  change average (fun h : A → B => f (h a)) = _ at he
  rw [he, average_prod]
  simp only [average_const]

theorem average_collision [DecidableEq A] [DecidableEq B] [Nonempty B]
    (a a' : A) (haa : a ≠ a') :
    average (fun h : A → B => if h a = h a' then (1:ℝ) else 0) =
      1 / Fintype.card B := by
  let e := Equiv.funSplitAt a B
  let a'' : {x : A // x ≠ a} := ⟨a', Ne.symm haa⟩
  have he := average_equiv e
    (fun p => if p.1 = p.2 a'' then (1:ℝ) else 0)
  change average (fun h : A → B => if h a = h a' then (1:ℝ) else 0) = _ at he
  rw [he, average_prod]
  change average (fun b : B => average (fun h : {x : A // x ≠ a} → B =>
    if b = h a'' then (1:ℝ) else 0)) = _
  have hev (b : B) := average_eval a'' (fun b' : B => if b = b' then (1:ℝ) else 0)
  simp_rw [hev]
  have hc (b : B) : average (fun b' : B => if b = b' then (1:ℝ) else 0) =
      1 / Fintype.card B := by simp [average]
  simp only [hc, average_const]

end FuzzyHammingProof

open scoped BigOperators Classical

namespace FuzzyHammingProof

variable {M B : Type*} [Fintype M] [Fintype B] [DecidableEq M] [DecidableEq B]
  [Nonempty B]

noncomputable def bucket (a : M → ℝ) (h : M → B) (y : B) : ℝ :=
  ∑ w, if h w = y then a w else 0

omit [DecidableEq M] [Nonempty B] in
theorem sum_bucket (a : M → ℝ) (h : M → B) : ∑ y, bucket a h y = ∑ w, a w := by
  simp only [bucket]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq M] [Nonempty B] in
theorem sum_bucket_sq (a : M → ℝ) (h : M → B) :
    ∑ y, (bucket a h y)^2 =
      ∑ w, ∑ v, (if h w = h v then (1:ℝ) else 0) * (a w * a v) := by
  simp only [bucket, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases he : h w = h v
  · simp [← he, mul_comm]
  · simp [he, Ne.symm he, ite_mul, mul_ite]

theorem collision_all (w v : M) :
    average (fun h : M → B => if h w = h v then (1:ℝ) else 0) =
      1 / Fintype.card B + (if w = v then (1:ℝ) - 1 / Fintype.card B else 0) := by
  by_cases h : w = v
  · subst v
    simp [average_const]
  · rw [average_collision w v h, if_neg h, add_zero]

theorem second_moment (a : M → ℝ) :
    average (fun h : M → B => ∑ y, (bucket a h y)^2) =
    (∑ w, a w)^2 / Fintype.card B +
      (1 - 1 / Fintype.card B) * ∑ w, (a w)^2 := by
  simp_rw [sum_bucket_sq, average_sum]
  have hh (w v : M) : average (fun h : M → B =>
      (if h w = h v then (1:ℝ) else 0) * (a w * a v)) =
      (1 / Fintype.card B + if w = v then (1:ℝ) - 1 / Fintype.card B else 0) *
        (a w * a v) := by
    simpa only [mul_comm] using
      (average_mul (a w * a v) (fun h : M → B => if h w = h v then (1:ℝ) else 0)).trans
        (congrArg (fun x : ℝ => (a w * a v) * x) (collision_all (B:=B) w v))
  simp_rw [hh, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem variance (a : M → ℝ) :
    average (fun h : M → B => ∑ y,
      (bucket a h y - (∑ w, a w) / Fintype.card B)^2) =
      (1 - 1 / Fintype.card B) * ∑ w, (a w)^2 := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp (h : M → B) : (∑ y,
      (bucket a h y - (∑ w, a w) / Fintype.card B)^2) =
      (∑ y, (bucket a h y)^2) - (∑ w, a w)^2 / Fintype.card B := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_bucket]
    field_simp
    ring
  simp_rw [hp]
  unfold average
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    sub_div]
  have hs := second_moment (B:=B) a
  unfold average at hs
  have hc : (Fintype.card (M → B) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_div_cancel_left₀ _ hc, hs]
  ring

end FuzzyHammingProof

open scoped BigOperators Classical

namespace FuzzyHammingProof

variable {M B : Type*} [Fintype M] [Fintype B] [DecidableEq M] [DecidableEq B]
  [Nonempty B]

noncomputable def hashL1 (a : M → ℝ) : ℝ :=
  average (fun h : M → B => ∑ y, |bucket a h y - (∑ w, a w) / Fintype.card B|)

omit [Nonempty B] in
theorem hashL1_nonneg (a : M → ℝ) : 0 ≤ hashL1 (B:=B) a :=
  average_nonneg fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem hashL1_sq (a : M → ℝ) (g : ℝ) (ha : ∀ w, 0 ≤ a w)
    (hag : ∀ w, a w ≤ g) :
    (hashL1 (B:=B) a)^2 ≤ (Fintype.card B : ℝ) * ((∑ w, a w) * g) := by
  let d : (M → B) × B → ℝ := fun p => bucket a p.1 p.2 -
    (∑ w, a w) / Fintype.card B
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ((M → B) × B))
    (fun _ => (1:ℝ)) (fun p => |d p|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type] at hs
  have hc : 0 < (Fintype.card (M → B) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hb : 0 ≤ (Fintype.card B : ℝ) := Nat.cast_nonneg _
  have hv := variance (B:=B) a
  change (∑ h, ∑ y, (d (h,y))^2) / (Fintype.card (M → B) : ℝ) = _ at hv
  have hsum : (∑ w, (a w)^2) ≤ (∑ w, a w) * g := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ => by nlinarith [mul_le_mul_of_nonneg_left (hag w) (ha w)]
  have hvar : (∑ h, ∑ y, (d (h,y))^2) / (Fintype.card (M → B) : ℝ) ≤
      (∑ w, a w) * g := by
    rw [hv]
    apply le_trans _ hsum
    have hn := Finset.sum_nonneg (s:=Finset.univ) (fun w _ => sq_nonneg (a w))
    have hi : 0 ≤ 1 / (Fintype.card B : ℝ) := by positivity
    nlinarith
  have hv' := (div_le_iff₀ hc).mp hvar
  have hm := mul_le_mul_of_nonneg_left hv' (mul_nonneg hc.le hb)
  unfold hashL1 average
  change ((∑ h, ∑ y, |d (h,y)|) / (Fintype.card (M → B) : ℝ))^2 ≤ _
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos hc)]
  nlinarith [hs]

theorem hashL1_le_twice (a : M → ℝ) (ha : ∀ w, 0 ≤ a w) :
    hashL1 (B:=B) a ≤ 2 * ∑ w, a w := by
  have hq : 0 ≤ ∑ w, a w := Finset.sum_nonneg fun w _ => ha w
  have hb : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply le_trans (average_mono (g:=fun _ : M → B => 2 * ∑ w, a w) ?_) (average_const _).le
  intro h
  have hnon (y : B) : 0 ≤ bucket a h y := by
    unfold bucket
    exact Finset.sum_nonneg fun w _ => by split_ifs; exact ha w; exact le_rfl
  calc
    ∑ y, |bucket a h y - (∑ w, a w) / Fintype.card B| ≤
        ∑ y, (bucket a h y + (∑ w, a w) / Fintype.card B) := by
      apply Finset.sum_le_sum
      intro y _
      have hd := div_nonneg hq (Nat.cast_nonneg (Fintype.card B) : (0:ℝ) ≤ _)
      exact abs_le.mpr ⟨by linarith [hnon y], by linarith [hnon y]⟩
    _ = 2 * ∑ w, a w := by
      rw [Finset.sum_add_distrib, sum_bucket]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring

end FuzzyHammingProof

open scoped BigOperators ENNReal Classical

namespace FuzzyHammingProof

variable {M I B : Type*} [Fintype M] [DecidableEq M]
  [Fintype B] [DecidableEq B] [Nonempty B]

theorem auxiliary_hash_bound (P : PMF (M × I)) :
    (∑' i, hashL1 (B:=B) (fun w => (P (w,i)).toReal)) ≤
      Real.sqrt ((Fintype.card B : ℝ) * guessing P) := by
  let q : I → ℝ := fun i => ∑ w, (P (w,i)).toReal
  let g : I → ℝ := fun i => (⨆ w, P (w,i)).toReal
  let D : I → ℝ := fun i => hashL1 (B:=B) (fun w => (P (w,i)).toReal)
  have hmass : Summable (fun p : I × M => (P (p.2,p.1)).toReal) :=
    (Equiv.prodComm I M).summable_iff.mpr (mass_summable P)
  have hqsum : Summable q := by
    simpa only [tsum_fintype] using
      (summable_prod_of_nonneg (fun p : I × M => ENNReal.toReal_nonneg)).mp hmass |>.2
  have hqtotal : ∑' i, q i = 1 := by
    change (∑' i, ∑ w, (P (w,i)).toReal) = 1
    have ht := hmass.tsum_prod
    simp only [tsum_fintype] at ht
    rw [← ht]
    exact ((Equiv.prodComm I M).tsum_eq (fun p => (P p).toReal)).trans (mass_tsum P)
  have hg : Summable g := guessing_summable P
  have hgtotal : ∑' i, g i = guessing P := (guessing_tsum P).symm
  have hqn (i : I) : 0 ≤ q i := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hgn (i : I) : 0 ≤ g i := ENNReal.toReal_nonneg
  have hDn (i : I) : 0 ≤ D i := hashL1_nonneg _
  have hsq (i : I) : D i ^ 2 ≤ q i * ((Fintype.card B : ℝ) * g i) := by
    have hi := hashL1_sq (B:=B) (fun w => (P (w,i)).toReal) (g i)
      (fun _ => ENNReal.toReal_nonneg) (fun w =>
        ENNReal.toReal_mono (guessingMass_fiber_ne_top P i) (le_iSup (fun w => P (w,i)) w))
    dsimp [D, q] at *
    nlinarith [hi]
  apply Real.tsum_le_of_sum_le hDn
  intro s
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i _ => hqn i) (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hgn i))
    (fun i _ => hsq i)
  have hqs : ∑ i ∈ s, q i ≤ 1 := (hqsum.sum_le_tsum s (fun i _ => hqn i)).trans_eq hqtotal
  have hgs : ∑ i ∈ s, g i ≤ guessing P :=
    (hg.sum_le_tsum s (fun i _ => hgn i)).trans_eq hgtotal
  rw [← Finset.mul_sum] at hcs
  have hb : 0 ≤ (Fintype.card B : ℝ) := Nat.cast_nonneg _
  have hgsn : 0 ≤ ∑ i ∈ s, g i := Finset.sum_nonneg fun i _ => hgn i
  have hm := mul_le_mul hqs (mul_le_mul_of_nonneg_left hgs hb)
    (mul_nonneg hb hgsn) (by norm_num : (0:ℝ) ≤ 1)
  have hs : (∑ i ∈ s, D i)^2 ≤ (Fintype.card B : ℝ) * guessing P :=
    hcs.trans (by simpa only [one_mul] using hm)
  exact Real.le_sqrt_of_sq_le hs

end FuzzyHammingProof

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

noncomputable section

theorem extract_mass_enn {M I : Type} [Fintype M] (ℓ : ℕ) (P : PMF (M × I))
    (y : Fin ℓ → Bool) (h : M → Fin ℓ → Bool) (i : I) :
    extractLawAux (fun (w : M) (f : M → Fin ℓ → Bool) => f w) P (y,h,i) =
      (∑ w, if h w = y then P (w,i) else 0) *
        (Fintype.card (M → Fin ℓ → Bool) : ℝ≥0∞)⁻¹ := by
  have hk (w : M) (j : I) :
      ((PMF.uniformOfFintype (M → Fin ℓ → Bool)).map fun f => (f w,f,j)) (y,h,i) =
      if i = j then (if y = h w then (Fintype.card (M → Fin ℓ → Bool) : ℝ≥0∞)⁻¹ else 0)
      else 0 := by
    rw [PMF.map_apply, tsum_eq_single h]
    · by_cases hij : i = j <;> simp [Prod.mk.injEq, hij]
    · intro f hf
      have hh : h ≠ f := Ne.symm hf
      simp [Prod.mk.injEq, hh]
  rw [extractLawAux, PMF.bind_apply, ENNReal.tsum_prod']
  simp_rw [hk, mul_ite, mul_zero]
  simp only [tsum_ite_eq', tsum_fintype]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  by_cases he : y = h w
  · simp [he]
  · simp [he, Ne.symm he]

theorem extract_mass_real {M I : Type} [Fintype M] (ℓ : ℕ) (P : PMF (M × I))
    (y : Fin ℓ → Bool) (h : M → Fin ℓ → Bool) (i : I) :
    (extractLawAux (fun (w : M) (f : M → Fin ℓ → Bool) => f w) P (y,h,i)).toReal =
      bucket (fun w => (P (w,i)).toReal) h y / Fintype.card (M → Fin ℓ → Bool) := by
  rw [extract_mass_enn, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (fun w _ => by split_ifs <;> simp [P.apply_ne_top])]
  simp only [bucket, apply_ite ENNReal.toReal, ENNReal.toReal_zero, div_eq_mul_inv]

theorem replacement_mass_enn {B X I : Type} [Fintype B] [Nonempty B]
    (Q : PMF (B × X × I)) (y : B) (h : X) (i : I) :
    (Q.bind fun a => (PMF.uniformOfFintype B).map fun u => (u,a.2.1,a.2.2)) (y,h,i) =
      (∑ b, Q (b,h,i)) * (Fintype.card B : ℝ≥0∞)⁻¹ := by
  have hk (p : X × I) :
      ((PMF.uniformOfFintype B).map fun u => (u,p.1,p.2)) (y,h,i) =
      if (h,i) = p then (Fintype.card B : ℝ≥0∞)⁻¹ else 0 := by
    rw [PMF.map_apply, tsum_eq_single y]
    · simp [Prod.mk.injEq]
    · intro u hu
      simp [Prod.mk.injEq, Ne.symm hu]
  rw [PMF.bind_apply, ENNReal.tsum_prod']
  simp_rw [hk, mul_ite, mul_zero]
  simp only [tsum_ite_eq', tsum_fintype, ← Finset.sum_mul]

theorem replacement_mass_real {M I : Type} [Fintype M] (ℓ : ℕ) (P : PMF (M × I))
    (y : Fin ℓ → Bool) (h : M → Fin ℓ → Bool) (i : I) :
    (((extractLawAux (fun (w : M) (f : M → Fin ℓ → Bool) => f w) P).bind
      fun a => (uniformBits ℓ).map fun u => (u,a.2.1,a.2.2)) (y,h,i)).toReal =
      (∑ w, (P (w,i)).toReal) / Fintype.card (Fin ℓ → Bool) /
        Fintype.card (M → Fin ℓ → Bool) := by
  rw [uniformBits, replacement_mass_enn, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _)]
  simp only [extract_mass_real, ← Finset.sum_div, sum_bucket]
  ring

def hashReorder {M B I : Type} : (I × ((M → B) × B)) ≃ (B × (M → B) × I) where
  toFun a := (a.2.2,a.2.1,a.1)
  invFun a := (a.2.2,a.2.1,a.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem hash_distance_eq {M I : Type} [Fintype M] (ℓ : ℕ) (P : PMF (M × I)) :
    statDist (extractLawAux (fun (w : M) (f : M → Fin ℓ → Bool) => f w) P)
      ((extractLawAux (fun (w : M) (f : M → Fin ℓ → Bool) => f w) P).bind
        fun a => (uniformBits ℓ).map fun u => (u,a.2.1,a.2.2)) =
      (1 / 2 : ℝ) * ∑' i, average (fun h : M → Fin ℓ → Bool =>
        ∑ y, |bucket (fun w => (P (w,i)).toReal) h y -
          (∑ w, (P (w,i)).toReal) / Fintype.card (Fin ℓ → Bool)|) := by
  let Q := extractLawAux (fun (w : M) (f : M → Fin ℓ → Bool) => f w) P
  let R := Q.bind fun a => (uniformBits ℓ).map fun u => (u,a.2.1,a.2.2)
  have hs := statDist_summable Q R
  change (1 / 2 : ℝ) * (∑' a, |(Q a).toReal - (R a).toReal|) = _
  congr 1
  rw [← (hashReorder (M:=M) (B:=Fin ℓ → Bool) (I:=I)).tsum_eq
    (fun a => |(Q a).toReal - (R a).toReal|)]
  have ht := (hs.comp_injective (hashReorder (M:=M) (B:=Fin ℓ → Bool) (I:=I)).injective).tsum_prod
  dsimp only [Function.comp_def] at ht
  rw [ht]
  apply tsum_congr
  intro i
  simp only [tsum_fintype, Fintype.sum_prod_type, hashReorder, Equiv.coe_fn_mk]
  change (∑ h, ∑ y, |(Q (y,h,i)).toReal - (R (y,h,i)).toReal|) = _
  dsimp only [Q, R]
  simp only [extract_mass_real, replacement_mass_real, ← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (Fintype.card (M → Fin ℓ → Bool)) : (0 : ℝ) ≤ _),
    ← Finset.sum_div, average]

end
end FuzzyHammingProof

open scoped BigOperators ENNReal Classical
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

theorem hash_security {M I : Type} [Fintype M]
    (ℓ : ℕ) (P : PMF (M × I)) :
    statDist (extractLawAux (fun (w : M) (h : M → Fin ℓ → Bool) => h w) P)
      ((extractLawAux (fun (w : M) (h : M → Fin ℓ → Bool) => h w) P).bind
        fun y => (uniformBits ℓ).map fun u => (u, y.2.1, y.2.2)) ≤
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Fin ℓ → Bool) : ℝ) * guessing P) := by
  rw [hash_distance_eq ℓ P]
  exact mul_le_mul_of_nonneg_left (auxiliary_hash_bound (B:=Fin ℓ → Bool) P) (by norm_num)

end FuzzyHammingProof

open scoped BigOperators ENNReal NNReal
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

noncomputable section

variable {F : Type} [DecidableEq F] [AddCommGroup F] {n : ℕ}

omit [AddCommGroup F] in
theorem code_unique (C : Finset (Fin n → F)) (t : ℕ)
    (hd : MinDistGe C (2 * t + 1)) : IsCode hammingDist C t := by
  intro y c hc c' hc' h h'
  by_contra hne
  have hl := hd c hc c' hc' hne
  have hu := hammingDist_triangle_left c c' y
  omega

theorem decode_eq {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ)
    (hcode : IsCode dis C t) (y c : M) (hc : c ∈ C) (hy : dis y c ≤ t) :
    decodeWithin dis C t y = c := by
  classical
  have he : ∃ a ∈ C, dis y a ≤ t := ⟨c, hc, hy⟩
  rw [decodeWithin, dif_pos he]
  exact hcode y _ he.choose_spec.1 c hc he.choose_spec.2 hy

theorem offset_correct (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ)
    (hd : MinDistGe C (2 * t + 1)) :
    SketchCorrect hammingDist t (codeOffsetSS C hC) (codeOffsetRec C t) := by
  classical
  intro w w' hw s hs
  obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hs
  have hc' : c ∈ C := (PMF.mem_support_uniformOfFinset_iff hC c).1 hc
  have he : hammingDist (w' - (w - c)) c = hammingDist w' w := by
    rw [hammingDist_eq_hammingNorm, hammingDist_eq_hammingNorm]
    congr 1
    abel
  have hrec := decode_eq hammingDist C t (code_unique C t hd) (w' - (w - c)) c hc'
    (by rw [he]; simpa only [hammingDist_comm] using hw)
  simp only [codeOffsetRec, hrec]
  congr 1
  abel

theorem offset_mass (C : Finset (Fin n → F)) (hC : C.Nonempty) (w s : Fin n → F) :
    codeOffsetSS C hC w s = if w - s ∈ C then (C.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [codeOffsetSS, PMF.map_apply]
  rw [tsum_eq_single (w - s)]
  · simp
  · intro c hc
    have hne : s ≠ w - c := by
      intro h
      apply hc
      rw [h]
      abel
    simp [hne]

theorem offset_joint_mass {I : Type} (C : Finset (Fin n → F)) (hC : C.Nonempty)
    (P : PMF ((Fin n → F) × I)) (w s : Fin n → F) (i : I) :
    withSketchAux (codeOffsetSS C hC) P (w, (s, i)) =
      P (w, i) * (if w - s ∈ C then (C.card : ℝ≥0∞)⁻¹ else 0) := by
  classical
  rw [withSketchAux, PMF.bind_apply, tsum_eq_single (w, i)]
  · simp only [PMF.map_apply, Prod.mk.injEq, true_and]
    rw [tsum_eq_single s]
    · simp [offset_mass]
    · intro s' hs'
      simp [Ne.symm hs']
  · rintro ⟨w', i'⟩ hne
    suffices hzero : ((codeOffsetSS C hC w').map fun a => (w', (a, i'))) (w, (s, i)) = 0 by
      simp [hzero]
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    have hn : (w, (s, i)) ≠ (w', (a, i')) := by
      intro h
      apply hne
      exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun x => x.2.2) h).symm
    simp [hn]

theorem offset_guessing [Fintype F] {I : Type} (C : Finset (Fin n → F)) (hC : C.Nonempty)
    (P : PMF ((Fin n → F) × I)) :
    guessing (withSketchAux (codeOffsetSS C hC) P) ≤
      ((Fintype.card (Fin n → F) : ℝ) / C.card) * guessing P := by
  classical
  have hpoint (s : Fin n → F) (i : I) :
      (⨆ w, withSketchAux (codeOffsetSS C hC) P (w, (s, i))) ≤
        (⨆ w, P (w, i)) * (C.card : ℝ≥0∞)⁻¹ := by
    refine iSup_le fun w => ?_
    rw [offset_joint_mass]
    split_ifs
    · exact mul_le_mul_left (le_iSup (fun w => P (w, i)) w) _
    · simp
  have hmass : guessingMass (withSketchAux (codeOffsetSS C hC) P) ≤
      (Fintype.card (Fin n → F) : ℝ≥0∞) * (guessingMass P * (C.card : ℝ≥0∞)⁻¹) := by
    unfold guessingMass
    rw [ENNReal.tsum_prod']
    calc
      _ ≤ ∑' s : Fin n → F, ∑' i : I, (⨆ w, P (w, i)) * (C.card : ℝ≥0∞)⁻¹ :=
        ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum (hpoint s)
      _ = _ := by simp only [ENNReal.tsum_mul_right, tsum_fintype, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
  have hK : (C.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  have htop : (Fintype.card (Fin n → F) : ℝ≥0∞) *
      (guessingMass P * (C.card : ℝ≥0∞)⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (guessingMass_ne_top P)
      (ENNReal.inv_ne_top.mpr hK))
  have hr := ENNReal.toReal_mono htop hmass
  simpa only [guessing, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hr

end
end FuzzyHammingProof

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

noncomputable section

def helperReorder {B X S I : Type} : (B × X × (S × I)) ≃ (B × (S × X) × I) where
  toFun a := (a.1, (a.2.2.1, a.2.1), a.2.2.2)
  invFun a := (a.1, a.2.1.2, (a.2.1.1, a.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem composition_correct {M S X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (dis : M → M → ℕ) (t : ℕ) (SS : M → PMF S) (Rec : M → S → PMF M)
    (Ext : M → X → (Fin ℓ → Bool)) (hcorrect : SketchCorrect dis t SS Rec) :
    ExtractorCorrect dis t (sketchExtGen SS Ext) (sketchExtRep Rec Ext) := by
  intro w w' hw rp hrp
  obtain ⟨s, hs, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 hrp
  obtain ⟨x, _, hxeq⟩ := (PMF.mem_support_map_iff _ _ _).1 h
  subst rp
  simp only [sketchExtRep, hcorrect w w' hw s hs, PMF.pure_map]

theorem composition_law {M S X I : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (SS : M → PMF S) (Ext : M → X → (Fin ℓ → Bool)) (P : PMF (M × I)) :
    (P.bind fun p => (sketchExtGen SS Ext p.1).map fun rp => (rp.1, rp.2, p.2)) =
      (extractLawAux Ext (withSketchAux SS P)).map helperReorder := by
  simp only [sketchExtGen, extractLawAux, withSketchAux, PMF.map_bind, PMF.bind_map,
    PMF.bind_bind, PMF.map_comp, Function.comp_def, helperReorder, Equiv.coe_fn_mk]

theorem composition_distance {M S X I : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (SS : M → PMF S) (Ext : M → X → (Fin ℓ → Bool)) (P : PMF (M × I)) :
    statDist
      (P.bind fun p => (sketchExtGen SS Ext p.1).map fun rp => (rp.1, rp.2, p.2))
      ((P.bind fun p => (sketchExtGen SS Ext p.1).map fun rp => (rp.1, rp.2, p.2)).bind
        fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)) =
    statDist (extractLawAux Ext (withSketchAux SS P))
      ((extractLawAux Ext (withSketchAux SS P)).bind
        fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)) := by
  rw [composition_law]
  have h (Q : PMF ((Fin ℓ → Bool) × X × (S × I))) :
      (Q.map helperReorder).bind (fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)) =
      (Q.bind fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)).map helperReorder := by
    simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      helperReorder, Equiv.coe_fn_mk]
  rw [h, statDist_map_equiv]

end
end FuzzyHammingProof

open scoped BigOperators ENNReal
open FuzzyExtractors.Hamming

namespace FuzzyHammingProof

theorem length_product_bound (q K g ε m : ℝ) (n ℓ : ℕ)
    (hq : 0 < q) (hK : 0 < K) (hg : 0 < g) (hε : 0 < ε)
    (hm : m ≤ -Real.logb 2 g)
    (hℓ : (ℓ : ℝ) ≤ m + Real.logb 2 K - (n : ℝ) * Real.logb 2 q
      - 2 * Real.logb 2 (1 / ε) + 2) :
    (2 : ℝ) ^ ℓ * (q ^ n / K) * g ≤ 4 * ε ^ 2 := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hp : 0 < (2 : ℝ) ^ ℓ * (q ^ n / K) * g :=
    mul_pos (mul_pos (pow_pos htwo _) (div_pos (pow_pos hq _) hK)) hg
  have hr : 0 < 4 * ε ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hε)
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hp hr).mp
  have hl : Real.logb 2 ((2 : ℝ) ^ ℓ * (q ^ n / K) * g) =
      (ℓ : ℝ) + (n : ℝ) * Real.logb 2 q - Real.logb 2 K + Real.logb 2 g := by
    rw [Real.logb_mul (mul_ne_zero (pow_ne_zero _ htwo.ne')
      (div_ne_zero (pow_ne_zero _ hq.ne') hK.ne')) hg.ne',
      Real.logb_mul (pow_ne_zero _ htwo.ne') (div_ne_zero (pow_ne_zero _ hq.ne') hK.ne'),
      Real.logb_div (pow_ne_zero _ hq.ne') hK.ne', Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    ring
  have hrlog : Real.logb 2 (4 * ε ^ 2) = 2 + 2 * Real.logb 2 ε := by
    rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hε.ne'),
      Real.logb_pow]
    have : Real.logb 2 (4 : ℝ) = 2 := by
      calc
        Real.logb 2 (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
        _ = 2 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; norm_num
    rw [this]
    norm_num
  have hi : Real.logb 2 (1 / ε) = -Real.logb 2 ε := by simp [one_div]
  rw [hl, hrlog]
  rw [hi] at hℓ
  linarith

theorem half_sqrt_le (x ε : ℝ) (hε : 0 < ε) (hx : x ≤ 4 * ε ^ 2) :
    (1 / 2 : ℝ) * Real.sqrt x ≤ ε := by
  have h : Real.sqrt x ≤ 2 * ε := (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  linarith

end FuzzyHammingProof

namespace FuzzyExtractors.Hamming

theorem theorem_5_2 {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F] {n : ℕ}
    (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ) (hdist : MinDistGe C (2 * t + 1))
    (m ε : ℝ) (hε : 0 < ε) (ℓ : ℕ)
    (hℓ : (ℓ : ℝ) ≤ m + Real.logb 2 C.card - (n : ℝ) * Real.logb 2 (Fintype.card F)
      - 2 * Real.logb 2 (1 / ε) + 2) :
    ∃ (P : Type) (Gen : (Fin n → F) → PMF ((Fin ℓ → Bool) × P))
      (Rep : (Fin n → F) → P → PMF (Fin ℓ → Bool)),
      IsAvgFuzzyExtractor hammingDist m ℓ t ε Gen Rep := by
  classical
  let M := Fin n → F
  let _ : DecidableEq M := Classical.decEq M
  let B := Fin ℓ → Bool
  let H := M → B
  let Ext : M → H → B := fun w h => h w
  refine ⟨M × H, sketchExtGen (codeOffsetSS C hC) Ext,
    sketchExtRep (codeOffsetRec C t) Ext, ?_⟩
  constructor
  · exact FuzzyHammingProof.composition_correct hammingDist t (codeOffsetSS C hC)
      (codeOffsetRec C t) Ext (FuzzyHammingProof.offset_correct C hC t hdist)
  · intro I WI hWI
    rw [FuzzyHammingProof.composition_distance]
    apply (FuzzyHammingProof.hash_security ℓ (withSketchAux (codeOffsetSS C hC) WI)).trans
    apply FuzzyHammingProof.half_sqrt_le _ ε hε
    have hle := FuzzyHammingProof.offset_guessing C hC WI
    have hmul := mul_le_mul_of_nonneg_left hle
      (Nat.cast_nonneg (Fintype.card (Fin ℓ → Bool)) :
        (0 : ℝ) ≤ (Fintype.card (Fin ℓ → Bool) : ℝ))
    have hscalar := FuzzyHammingProof.length_product_bound
      (Fintype.card F) C.card (FuzzyHammingProof.guessing WI) ε m n ℓ
      (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr hC.card_pos)
      (FuzzyHammingProof.guessing_pos WI) hε
      (by simpa only [FuzzyHammingProof.avgMinEntropy_eq_neg_log_guessing] using hWI) hℓ
    apply hmul.trans
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat, mul_assoc] using hscalar

end FuzzyExtractors.Hamming

open FuzzyExtractors.Hamming

theorem solution {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F] {n : ℕ}
    (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ) (hdist : MinDistGe C (2 * t + 1))
    (m ε : ℝ) (hε : 0 < ε) (ℓ : ℕ)
    (hℓ : (ℓ : ℝ) ≤ m + Real.logb 2 C.card - (n : ℝ) * Real.logb 2 (Fintype.card F)
      - 2 * Real.logb 2 (1 / ε) + 2) :
    ∃ (P : Type) (Gen : (Fin n → F) → PMF ((Fin ℓ → Bool) × P))
      (Rep : (Fin n → F) → P → PMF (Fin ℓ → Bool)),
      IsAvgFuzzyExtractor hammingDist m ℓ t ε Gen Rep := by
  exact FuzzyExtractors.Hamming.theorem_5_2 C hC t hdist m ε hε ℓ hℓ
