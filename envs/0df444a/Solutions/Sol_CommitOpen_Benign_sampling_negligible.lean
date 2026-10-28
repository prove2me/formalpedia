-- Prove2me | solution 1 for CommitOpen.Benign.sampling_negligible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:58:46.033288+00:00
-- url     : https://prove2.me/submissions/d45d1c35-f4f5-4e83-be89-d5194c6584f5

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign
open scoped ComplexOrder


lemma mgf_step {L : Type} [Fintype L] (w : L → ℝ) (hw0 : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (g : L → ℝ) (hg : ∀ l, |g l| ≤ 1) (hg0 : ∑ l, w l * g l = 0) (lam : ℝ) (hlam : |lam| ≤ 1) :
    ∑ l, w l * Real.exp (lam * g l) ≤ Real.exp (lam ^ 2) := by
  have h1 : ∀ l, Real.exp (lam * g l) ≤ 1 + lam * g l + lam ^ 2 := by
    intro l
    have hx : |lam * g l| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg lam, abs_nonneg (g l), hg l]
    have := Real.abs_exp_sub_one_sub_id_le hx
    have h2 : (lam * g l) ^ 2 ≤ lam ^ 2 := by
      rw [mul_pow]
      have : g l ^ 2 ≤ 1 := by
        have := hg l
        nlinarith [abs_nonneg (g l), sq_abs (g l)]
      nlinarith [sq_nonneg lam]
    have := (abs_le.mp this).2
    linarith
  calc ∑ l, w l * Real.exp (lam * g l) ≤ ∑ l, w l * (1 + lam * g l + lam ^ 2) :=
        Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (h1 l) (hw0 l))
    _ = 1 + lam ^ 2 := by
        have : ∀ l, w l * (1 + lam * g l + lam ^ 2) = w l * (1 + lam ^ 2) + lam * (w l * g l) := by
          intro l; ring
        simp_rw [this]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, ← Finset.mul_sum, hg0]
        ring
    _ ≤ Real.exp (lam ^ 2) := by
        have := Real.add_one_le_exp (lam ^ 2)
        linarith

lemma chernoff_gen {L : Type} [Fintype L] [DecidableEq L] {m : ℕ} (w : L → ℝ) (hw0 : ∀ l, 0 ≤ w l)
    (hw1 : ∑ l, w l = 1) (f : Fin m → L → ℝ)
    (hf : ∀ i l, |f i l - ∑ l', w l' * f i l'| ≤ 1) (lam : ℝ) (hlam : |lam| ≤ 1) (τ : ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        τ ≤ lam * (∑ i, f i (ω i) - ∑ i, ∑ l', w l' * f i l')),
      ∏ i, w (ω i) ≤ Real.exp (-τ + m * lam ^ 2) := by
  set μ : Fin m → ℝ := fun i => ∑ l', w l' * f i l' with hμ
  have hmgf : ∑ ω : Fin m → L, (∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))
      ≤ Real.exp (m * lam ^ 2) := by
    have h1 : ∀ ω : Fin m → L, (∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))
        = ∏ i, (w (ω i) * Real.exp (lam * (f i (ω i) - μ i))) := by
      intro ω
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    simp_rw [h1]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => (Finset.univ : Finset L))
      (fun i l => w l * Real.exp (lam * (f i l - μ i)))]
    calc ∏ i, ∑ l, w l * Real.exp (lam * (f i l - μ i))
        ≤ ∏ i : Fin m, Real.exp (lam ^ 2) := by
          apply Finset.prod_le_prod
          · intro i _
            exact Finset.sum_nonneg (fun l _ => mul_nonneg (hw0 l) (Real.exp_pos _).le)
          · intro i _
            apply mgf_step w hw0 hw1 (fun l => f i l - μ i) (hf i)
            · simp only [mul_sub, Finset.sum_sub_distrib, hμ]
              rw [← Finset.sum_mul, hw1]; ring
            · exact hlam
      _ = Real.exp (m * lam ^ 2) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]; simp
  have hprod_nn : ∀ ω : Fin m → L, 0 ≤ ∏ i, w (ω i) :=
    fun ω => Finset.prod_nonneg (fun i _ => hw0 _)
  calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        τ ≤ lam * (∑ i, f i (ω i) - ∑ i, ∑ l', w l' * f i l')), ∏ i, w (ω i)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        τ ≤ lam * (∑ i, f i (ω i) - ∑ i, ∑ l', w l' * f i l')),
          Real.exp (-τ) * ((∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hω' := (Finset.mem_filter.mp hω).2
        have : Real.exp τ ≤ Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i)) := Real.exp_le_exp.mpr hω'
        have h2 : Real.exp (-τ) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i)) ≥ 1 := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have := Real.exp_le_exp.mp this
          linarith
        calc ∏ i, w (ω i) = (∏ i, w (ω i)) * 1 := by ring
          _ ≤ (∏ i, w (ω i)) * (Real.exp (-τ) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))) :=
              mul_le_mul_of_nonneg_left h2 (hprod_nn ω)
          _ = _ := by ring
    _ ≤ ∑ ω : Fin m → L, Real.exp (-τ) * ((∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω _ _
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hprod_nn ω) (Real.exp_pos _).le)
    _ = Real.exp (-τ) * ∑ ω : Fin m → L, (∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-τ) * Real.exp (m * lam ^ 2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-τ + m * lam ^ 2) := by rw [← Real.exp_add]

lemma label_f_bound {L : Type} [Fintype L] [DecidableEq L] (w : L → ℝ) (hw0 : ∀ l, 0 ≤ w l)
    (hw1 : ∑ l, w l = 1) (l0 : L) (gi : ℝ) (hg : |gi| ≤ 1) (l : L) :
    |(if l = l0 then gi else 0) - ∑ l', w l' * (if l' = l0 then gi else 0)| ≤ 1 := by
  have hwl : w l0 ≤ 1 := by
    rw [← hw1]
    exact Finset.single_le_sum (fun l _ => hw0 l) (Finset.mem_univ l0)
  have h1 : ∑ l', w l' * (if l' = l0 then gi else 0) = w l0 * gi := by
    simp [Finset.sum_ite_eq']
  rw [h1]
  have := hw0 l0
  split_ifs
  · have e : gi - w l0 * gi = (1 - w l0) * gi := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg gi]
  · rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg (hw0 l0)]
    nlinarith [abs_nonneg gi]

lemma chernoff_label {L : Type} [Fintype L] [DecidableEq L] {m : ℕ} (hm : 0 < m) (w : L → ℝ)
    (hw0 : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (l0 : L) (g : Fin m → ℝ) (hg : ∀ i, |g i| ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 * m) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        w l0 * ∑ i, g i + t ≤ ∑ i, (if ω i = l0 then g i else 0)), ∏ i, w (ω i)
      ≤ Real.exp (-(t ^ 2 / (4 * m)))) ∧
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        ∑ i, (if ω i = l0 then g i else 0) ≤ w l0 * ∑ i, g i - t), ∏ i, w (ω i)
      ≤ Real.exp (-(t ^ 2 / (4 * m)))) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set f : Fin m → L → ℝ := fun i l => if l = l0 then g i else 0 with hf
  have hfb : ∀ i l, |f i l - ∑ l', w l' * f i l'| ≤ 1 := fun i l => label_f_bound w hw0 hw1 l0 (g i) (hg i) l
  have hM : ∑ i, ∑ l', w l' * f i l' = w l0 * ∑ i, g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [hf, Finset.sum_ite_eq']
  have hexp1 : -(t / (2 * m) * t) + m * (t / (2 * m)) ^ 2 = -(t ^ 2 / (4 * m)) := by
    field_simp; ring
  constructor
  · have hlam : |t / (2 * m)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]; linarith
    have := chernoff_gen w hw0 hw1 f hfb (t / (2 * m)) hlam (t / (2 * m) * t)
    rw [hM, hexp1] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      have : t ≤ ∑ i, f i (ω i) - w l0 * ∑ i, g i := by simp only [hf]; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · intro ω _ _
      exact Finset.prod_nonneg (fun i _ => hw0 _)
  · have hlam : |-(t / (2 * m))| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity), div_le_one (by positivity)]; linarith
    have := chernoff_gen w hw0 hw1 f hfb (-(t / (2 * m))) hlam (t / (2 * m) * t)
    rw [hM] at this
    have hexp2 : -(t / (2 * m) * t) + m * (-(t / (2 * m))) ^ 2 = -(t ^ 2 / (4 * m)) := by
      field_simp; ring
    rw [hexp2] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      have : ∑ i, f i (ω i) - w l0 * ∑ i, g i ≤ -t := by simp only [hf]; linarith
      nlinarith [div_nonneg ht0 (by positivity : (0:ℝ) ≤ 2 * m)]
    · intro ω _ _
      exact Finset.prod_nonneg (fun i _ => hw0 _)



noncomputable def fpm (m k j : ℕ) : ℝ := (m.choose j : ℝ) * (k : ℝ) ^ j * ((m - k : ℕ) : ℝ) ^ (m - j)

lemma fpm_step (m k j : ℕ) (hj : j < m) :
    ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (j + 1) = ((m : ℝ) - j) * k * fpm m k j := by
  unfold fpm
  have h1 : (m.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (m.choose j : ℝ) * ((m : ℝ) - j) := by
    have := Nat.choose_succ_right_eq m j
    have h2 : ((m.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((m.choose j * (m - j) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub hj.le] at h2
    exact h2
  have h3 : m - j = (m - (j + 1)) + 1 := by omega
  have h4 : ((m - k : ℕ) : ℝ) ^ (m - j) = ((m - k : ℕ) : ℝ) ^ (m - (j + 1)) * ((m - k : ℕ) : ℝ) := by
    rw [h3, pow_succ]
  rw [h4]
  calc ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * ((m.choose (j + 1) : ℝ) * (k : ℝ) ^ (j + 1) * ((m - k : ℕ) : ℝ) ^ (m - (j + 1)))
      = ((m.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) * (k : ℝ) ^ j * k * (((m - k : ℕ) : ℝ) ^ (m - (j + 1)) * ((m - k : ℕ) : ℝ)) := by ring
    _ = _ := by rw [h1]; ring

lemma fpm_le (m k : ℕ) (hk : k < m) (j : ℕ) (hj : j ≤ m) : fpm m k j ≤ fpm m k k := by
  have hmk : (0:ℝ) < ((m - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hk
  have hnn : ∀ j, 0 ≤ fpm m k j := fun j => by unfold fpm; positivity
  rcases le_total j k with h | h
  · -- j ≤ k : increasing up to k
    have key : ∀ d, d ≤ k → fpm m k (k - d) ≤ fpm m k k := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have hlt : k - (d + 1) < m := by omega
        have step := fpm_step m k (k - (d + 1)) hlt
        have e : k - (d + 1) + 1 = k - d := by omega
        rw [e] at step
        have h1 := ih (by omega)
        have hpos : 0 < ((k - (d + 1) : ℕ) + 1 : ℝ) * ((m - k : ℕ) : ℝ) := by positivity
        have hineq : (((k - (d + 1) : ℕ) : ℝ) + 1) * ((m - k : ℕ) : ℝ) ≤ ((m : ℝ) - ((k - (d + 1) : ℕ) : ℝ)) * k := by
          have hc : (((k - (d + 1) : ℕ) : ℝ)) + 1 ≤ k := by
            have : k - (d + 1) + 1 ≤ k := by omega
            exact_mod_cast this
          have hmk' : ((m - k : ℕ) : ℝ) = (m:ℝ) - k := by rw [Nat.cast_sub hk.le]
          rw [hmk']
          have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
          nlinarith [hc, hk0, (by exact_mod_cast hk : (k:ℝ) < m)]
        have hfn := hnn (k - (d + 1))
        have : fpm m k (k - (d + 1)) ≤ fpm m k (k - d) := by
          have : (((k - (d + 1) : ℕ) : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (k - (d + 1))
              ≤ (((k - (d + 1) : ℕ) : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (k - d) := by
            rw [step]
            exact mul_le_mul_of_nonneg_right hineq hfn
          exact le_of_mul_le_mul_left this hpos
        exact this.trans h1
    have := key (k - j) (by omega)
    have e : k - (k - j) = j := by omega
    rwa [e] at this
  · -- k ≤ j : decreasing after k
    induction j, h using Nat.le_induction with
    | base => exact le_rfl
    | succ j hkj ih =>
      have hjm : j < m := by omega
      have step := fpm_step m k j hjm
      have hpos : 0 < ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) := by positivity
      have hineq : ((m : ℝ) - j) * k ≤ ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) := by
        have hmk' : ((m - k : ℕ) : ℝ) = (m:ℝ) - k := by rw [Nat.cast_sub hk.le]
        rw [hmk']
        have hkj' : (k:ℝ) ≤ j := by exact_mod_cast hkj
        have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
        nlinarith [hkj', hk0]
      have : fpm m k (j + 1) ≤ fpm m k j := by
        have : ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (j + 1)
            ≤ ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k j := by
          rw [step]
          exact mul_le_mul_of_nonneg_right hineq (hnn j)
        exact le_of_mul_le_mul_left this hpos
      exact this.trans (ih (by omega))

lemma pmf_lower (m k : ℕ) (hk : k < m) :
    (1:ℝ) / (m + 1) ≤ (m.choose k : ℝ) * ((k:ℝ) / m) ^ k * (1 - (k:ℝ) / m) ^ (m - k) := by
  have hm : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsum : ∑ j ∈ Finset.range (m + 1), fpm m k j = (m : ℝ) ^ m := by
    have := add_pow (k : ℝ) (((m - k : ℕ) : ℝ)) m
    have e : (k : ℝ) + ((m - k : ℕ) : ℝ) = m := by
      rw [Nat.cast_sub hk.le]; ring
    rw [e] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro j _
    unfold fpm
    ring
  have hle : ∑ j ∈ Finset.range (m + 1), fpm m k j ≤ (m + 1 : ℕ) * fpm m k k := by
    calc ∑ j ∈ Finset.range (m + 1), fpm m k j ≤ ∑ j ∈ Finset.range (m + 1), fpm m k k :=
          Finset.sum_le_sum (fun j hj => fpm_le m k hk j (by simpa [Nat.lt_succ_iff] using hj))
      _ = _ := by simp
  rw [hsum] at hle
  have hmpos : (0:ℝ) < (m:ℝ) ^ m := by positivity
  have hf : (m.choose k : ℝ) * ((k:ℝ) / m) ^ k * (1 - (k:ℝ) / m) ^ (m - k) = fpm m k k / (m:ℝ) ^ m := by
    unfold fpm
    have e1 : (1 - (k:ℝ) / m) = ((m - k : ℕ) : ℝ) / m := by
      rw [Nat.cast_sub hk.le]; field_simp
    rw [e1, div_pow, div_pow]
    have : (m:ℝ) ^ m = (m:ℝ) ^ k * (m:ℝ) ^ (m - k) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    field_simp
  rw [hf, div_le_div_iff₀ (by positivity) hmpos]
  push_cast at hle
  linarith



/-- label weights -/
noncomputable def wlab (p : ℝ) : Fin 3 → ℝ := ![1 - p, p / 2, p / 2]

lemma wlab_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∀ l, 0 ≤ wlab p l := by
  intro l
  fin_cases l <;> simp [wlab] <;> linarith

lemma wlab_sum (p : ℝ) : ∑ l, wlab p l = 1 := by
  simp [wlab, Fin.sum_univ_three]; ring

/-- the labeling attached to a test -/
def omegaOf {m k : ℕ} (t : Test m k) : Fin m → Fin 3 :=
  fun i => if i ∈ t.1.2 then 2 else if i ∈ t.1.1 then 1 else 0

lemma omegaOf_eq_two {m k : ℕ} (t : Test m k) (i : Fin m) : omegaOf t i = 2 ↔ i ∈ t.1.2 := by
  unfold omegaOf
  by_cases a : i ∈ t.1.2 <;> by_cases b : i ∈ t.1.1 <;> simp [a, b]

lemma omegaOf_eq_zero {m k : ℕ} (t : Test m k) (i : Fin m) : omegaOf t i = 0 ↔ i ∉ t.1.1 := by
  unfold omegaOf
  have hs := t.2.2
  by_cases a : i ∈ t.1.2
  · have : i ∈ t.1.1 := hs a
    simp [a, this]
  · by_cases b : i ∈ t.1.1 <;> simp [a, b]

lemma omegaOf_injective {m k : ℕ} : Function.Injective (omegaOf (m := m) (k := k)) := by
  intro t t' h
  apply Subtype.ext
  apply Prod.ext
  · ext i
    have e1 := omegaOf_eq_zero t i
    have e2 := omegaOf_eq_zero t' i
    have h0 := congrFun h i
    rw [h0] at e1
    tauto
  · ext i
    have e1 := omegaOf_eq_two t i
    have e2 := omegaOf_eq_two t' i
    have h0 := congrFun h i
    rw [h0] at e1
    tauto

lemma prod_wlab {m k : ℕ} (p : ℝ) (t : Test m k) :
    ∏ i, wlab p (omegaOf t i) = (1 - p) ^ (m - k) * (p / 2) ^ k := by
  have h1 : ∀ i, wlab p (omegaOf t i) = if i ∈ t.1.1 then p / 2 else 1 - p := by
    intro i
    unfold omegaOf
    have hs := t.2.2
    by_cases a : i ∈ t.1.2 <;> by_cases b : i ∈ t.1.1
    · simp [a, b, wlab]
    · exact absurd (hs a) b
    · simp [a, b, wlab]
    · simp [a, b, wlab]
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc : t.1.1.card = k := t.2.1
  have : (Finset.univ.filter (fun i => i ∉ t.1.1)).card = m - k := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp [hc]
  have h2 : (Finset.univ.filter (fun i => i ∈ t.1.1)).card = k := by simpa using hc
  rw [h2, this]; ring

lemma ratio_alg (H0 n H1 N' r ε k : ℝ) (hn : 0 < n) (hN : 0 < N') (hε : 0 < ε)
    (h1 : H0 - r * n < ε * n / 2) (h2 : -(ε * k / 8) < H1 - r * N') (h3 : k / 4 < N') :
    H0 / n ≤ H1 / N' + ε := by
  have a1 : H0 / n < r + ε / 2 := by
    rw [div_lt_iff₀ hn]; nlinarith
  have a2 : r - ε / 2 ≤ H1 / N' := by
    rw [le_div_iff₀ hN]; nlinarith
  linarith

lemma sum_ite_omega {m k : ℕ} (t : Test m k) (g : Fin m → ℝ) :
    ∑ i, (if omegaOf t i = 0 then g i else 0) = ∑ i ∈ t.1.1ᶜ, g i := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp [omegaOf_eq_zero]

lemma sum_ite_omega2 {m k : ℕ} (t : Test m k) (g : Fin m → ℝ) :
    ∑ i, (if omegaOf t i = 2 then g i else 0) = ∑ i ∈ t.1.2, g i := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp [omegaOf_eq_two]

noncomputable def indd {m : ℕ} (x xhat : Fin m → Bool) (i : Fin m) : ℝ := if x i ≠ xhat i then 1 else 0

lemma hamming_real {m : ℕ} (S : Finset (Fin m)) (x xhat : Fin m → Bool) :
    (hammingOn S x xhat : ℝ) = ∑ i ∈ S, indd x xhat i := by
  unfold hammingOn indd
  rw [Finset.card_filter]
  push_cast
  rfl

lemma bad_to_events {m k : ℕ} (hk1 : 1 ≤ k) (hkm : k < m) (ε : ℝ) (hε : 0 < ε)
    (x xhat : Fin m → Bool) (t : Test m k) (ht : x ∉ goodSet ε xhat t) :
    (wlab ((k:ℝ) / m) 0 * ∑ i, (indd x xhat i - (∑ j, indd x xhat j) / m) + ε * ((m:ℝ) - k) / 2 ≤
        ∑ i, (if omegaOf t i = 0 then (indd x xhat i - (∑ j, indd x xhat j) / m) else 0)) ∨
    (∑ i, (if omegaOf t i = 2 then (indd x xhat i - (∑ j, indd x xhat j) / m) else 0) ≤
        wlab ((k:ℝ) / m) 2 * ∑ i, (indd x xhat i - (∑ j, indd x xhat j) / m) - ε * k / 8) ∨
    (∑ i, (if omegaOf t i = 2 then (1:ℝ) else 0) ≤
        wlab ((k:ℝ) / m) 2 * ∑ i : Fin m, (1:ℝ) - (k:ℝ) / 4) := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  have hm : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsg : ∑ i, (indd x xhat i - (∑ j, indd x xhat j) / m) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hsg, sum_ite_omega, mul_zero, zero_add] at hA
  rw [hsg, sum_ite_omega2, mul_zero, zero_sub] at hB
  rw [sum_ite_omega2] at hC
  have hw2 : wlab ((k:ℝ) / m) 2 = (k:ℝ) / m / 2 := by simp [wlab]
  rw [hw2] at hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hC
  have hcT : t.1.1.card = k := t.2.1
  have hcn : (t.1.1ᶜ.card : ℝ) = (m:ℝ) - k := by
    rw [Finset.card_compl, hcT, Fintype.card_fin, Nat.cast_sub hkm.le]
  have hsum1 : ∑ i ∈ t.1.1ᶜ, (indd x xhat i - (∑ j, indd x xhat j) / m)
      = (hammingOn t.1.1ᶜ x xhat : ℝ) - (∑ j, indd x xhat j) / m * (t.1.1ᶜ.card : ℝ) := by
    rw [Finset.sum_sub_distrib, hamming_real]
    simp
    ring
  have hsum2 : ∑ i ∈ t.1.2, (indd x xhat i - (∑ j, indd x xhat j) / m)
      = (hammingOn t.1.2 x xhat : ℝ) - (∑ j, indd x xhat j) / m * (t.1.2.card : ℝ) := by
    rw [Finset.sum_sub_distrib, hamming_real]
    simp
    ring
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
  have hN : (k:ℝ) / 4 < (t.1.2.card : ℝ) := by
    have : (k:ℝ) / m / 2 * m = k / 2 := by field_simp
    rw [this] at hC
    linarith
  have hkmR : (k:ℝ) < m := by exact_mod_cast hkm
  have hn : (0:ℝ) < (t.1.1ᶜ.card : ℝ) := by rw [hcn]; linarith
  have key := ratio_alg (hammingOn t.1.1ᶜ x xhat) (t.1.1ᶜ.card) (hammingOn t.1.2 x xhat) (t.1.2.card)
    ((∑ j, indd x xhat j) / m) ε k hn (by linarith) hε
    (by rw [hsum1, hcn] at hA; rw [hcn]; linarith)
    (by rw [hsum2] at hB; linarith) hN
  apply ht
  simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold relHamming
  exact key



lemma gen_exp (θ T c m : ℝ) (hm : 0 < m) (hθ : 0 ≤ θ) (hT : θ * m ≤ T) (hc : c ≤ θ ^ 2 / 4) :
    c * m ≤ T ^ 2 / (4 * m) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : (θ * m) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hT 2
  nlinarith [mul_pos hm hm]

lemma sum_filter_or_le {α : Type} [Fintype α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] [DecidablePred (fun a => P a ∨ Q a ∨ R a)] :
    ∑ a ∈ Finset.univ.filter (fun a => P a ∨ Q a ∨ R a), f a ≤
      ∑ a ∈ Finset.univ.filter P, f a + ∑ a ∈ Finset.univ.filter Q, f a
        + ∑ a ∈ Finset.univ.filter R, f a := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have := hf a
  by_cases hP : P a <;> by_cases hQ : Q a <;> by_cases hR : R a <;> simp [hP, hQ, hR, this]

theorem samp_main (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (hm : 2 / α ≤ m) (x xhat : Fin m → Bool) :
    ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
        testProb m ⌊α * m⌋₊ t ≤
      (m + 1) * (3 * Real.exp (-((ε * min (1 - α) α) ^ 2 / 1024 * m))) := by
  classical
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have hαm : 2 ≤ α * m := by
    have := (div_le_iff₀ hα0).mp hm
    linarith
  set k : ℕ := ⌊α * m⌋₊ with hk
  have hkle : (k:ℝ) ≤ α * m := Nat.floor_le (by positivity)
  have hklt : α * m < k + 1 := Nat.lt_floor_add_one _
  have hkge : α * m / 2 ≤ k := by linarith
  have hk1R : (1:ℝ) ≤ k := by linarith
  have hk1 : 1 ≤ k := by exact_mod_cast hk1R
  have hkmR : (k:ℝ) < m := by nlinarith
  have hkm : k < m := by exact_mod_cast hkmR
  set p : ℝ := (k:ℝ) / m with hp
  have hp0 : 0 < p := div_pos (by linarith) hmpos
  have hp1 : p < 1 := (div_lt_one hmpos).mpr hkmR
  set g : Fin m → ℝ := fun i => indd x xhat i - (∑ j, indd x xhat j) / m with hg
  have hind01 : ∀ i, 0 ≤ indd x xhat i ∧ indd x xhat i ≤ 1 := by
    intro i; unfold indd; split_ifs <;> simp
  have hr01 : 0 ≤ (∑ j, indd x xhat j) / m ∧ (∑ j, indd x xhat j) / m ≤ 1 := by
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hind01 i).1)) hmpos.le
    · rw [div_le_one hmpos]
      calc ∑ j, indd x xhat j ≤ ∑ j : Fin m, (1:ℝ) := Finset.sum_le_sum (fun i _ => (hind01 i).2)
        _ = m := by simp
  have hgb : ∀ i, |g i| ≤ 1 := by
    intro i
    simp only [hg]
    rw [abs_le]
    constructor <;> linarith [(hind01 i).1, (hind01 i).2, hr01.1, hr01.2]
  have hw0 := wlab_nonneg hp0.le hp1.le
  have hw1 := wlab_sum p
  set tA : ℝ := ε * ((m:ℝ) - k) / 2 with htA
  set tB : ℝ := ε * k / 8 with htB
  set tC : ℝ := (k:ℝ) / 4 with htC
  have hA := (chernoff_label hm0 (wlab p) hw0 hw1 0 g hgb tA (by rw [htA]; nlinarith)
    (by rw [htA]; nlinarith)).1
  have hB := (chernoff_label hm0 (wlab p) hw0 hw1 2 g hgb tB (by rw [htB]; positivity)
    (by rw [htB]; nlinarith)).2
  have hC := (chernoff_label hm0 (wlab p) hw0 hw1 2 (fun _ => (1:ℝ)) (fun _ => by simp) tC
    (by rw [htC]; positivity) (by rw [htC]; nlinarith)).2
  set c₀ : ℝ := (ε * min (1 - α) α) ^ 2 / 1024 with hc₀
  have hδ1 : min (1 - α) α ≤ 1 - α := min_le_left _ _
  have hδ2 : min (1 - α) α ≤ α := min_le_right _ _
  have hδ0 : 0 ≤ min (1 - α) α := le_min (by linarith) hα0.le
  set δ : ℝ := min (1 - α) α with hδ
  have hδm1 : δ * m ≤ (m:ℝ) - k := by
    have := mul_le_mul_of_nonneg_right hδ1 hmpos.le
    linarith
  have hδm2 : δ * m / 2 ≤ k := by
    have := mul_le_mul_of_nonneg_right hδ2 hmpos.le
    linarith
  have hεδ : (0:ℝ) ≤ (ε * δ) ^ 2 := sq_nonneg _
  have hexpA : c₀ * m ≤ tA ^ 2 / (4 * m) := by
    apply gen_exp (ε * δ / 2) _ _ _ hmpos (by positivity)
    · rw [htA]
      have := mul_le_mul_of_nonneg_left hδm1 hε0.le
      linarith
    · rw [hc₀]
      linarith
  have hexpB : c₀ * m ≤ tB ^ 2 / (4 * m) := by
    apply gen_exp (ε * δ / 16) _ _ _ hmpos (by positivity)
    · rw [htB]
      have := mul_le_mul_of_nonneg_left hδm2 hε0.le
      linarith
    · rw [hc₀]
      have : (ε * δ / 16) ^ 2 / 4 = (ε * δ) ^ 2 / 1024 := by ring
      linarith
  have hexpC : c₀ * m ≤ tC ^ 2 / (4 * m) := by
    apply gen_exp (δ / 8) _ _ _ hmpos (by positivity)
    · rw [htC]
      linarith
    · rw [hc₀]
      have h6 : (ε * δ) ^ 2 ≤ δ ^ 2 := by
        rw [mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg δ) (pow_le_one₀ hε0.le hε1)
      have : (δ / 8) ^ 2 / 4 = δ ^ 2 / 256 := by ring
      linarith
  have hSA := hA.trans (Real.exp_le_exp.mpr (neg_le_neg hexpA))
  have hSB := hB.trans (Real.exp_le_exp.mpr (neg_le_neg hexpB))
  have hSC := hC.trans (Real.exp_le_exp.mpr (neg_le_neg hexpC))
  set wtf : (Fin m → Fin 3) → ℝ := fun ω => ∏ i, wlab p (ω i) with hwtf
  have hwnn : ∀ ω, 0 ≤ wtf ω := fun ω => Finset.prod_nonneg (fun i _ => hw0 _)
  set bad := Finset.univ.filter (fun t : Test m k => x ∉ goodSet ε xhat t) with hbad
  have h1p : 0 < 1 - p := by linarith
  set q : ℝ := (1 - p) ^ (m - k) * (p / 2) ^ k with hq
  have hqpos : 0 < q := by positivity
  have hmain : q * bad.card ≤ 3 * Real.exp (-(c₀ * m)) := by
    calc q * bad.card = ∑ t ∈ bad, wtf (omegaOf t) := by
          rw [Finset.sum_congr rfl (fun t _ => prod_wlab p t)]
          simp [hq, mul_comm]
      _ = ∑ ω ∈ bad.image omegaOf, wtf ω :=
          (Finset.sum_image (fun a _ b _ h => omegaOf_injective h)).symm
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin 3 =>
            (wlab p 0 * ∑ i, g i + tA ≤ ∑ i, (if ω i = 0 then g i else 0)) ∨
            (∑ i, (if ω i = 2 then g i else 0) ≤ wlab p 2 * ∑ i, g i - tB) ∨
            (∑ i, (if ω i = 2 then (1:ℝ) else 0) ≤ wlab p 2 * ∑ i : Fin m, (1:ℝ) - tC)), wtf ω := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hω
            have ht' : x ∉ goodSet ε xhat t := (Finset.mem_filter.mp ht).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact bad_to_events hk1 hkm ε hε0 x xhat t ht'
          · intro ω _ _
            exact hwnn ω
      _ ≤ _ := sum_filter_or_le wtf hwnn _ _ _
      _ ≤ 3 * Real.exp (-(c₀ * m)) := by linarith
  have hL : 1 / ((m:ℝ) + 1) ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := pmf_lower m k hkm
  have hCpos : (0:ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkm.le
  set Z : ℝ := (m.choose k : ℝ) * 2 ^ k with hZ
  have hZpos : 0 < Z := by positivity
  have hqZ : q * Z = (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
    rw [hq, hZ, div_pow]
    field_simp
  have hE0 : 0 ≤ 3 * Real.exp (-(c₀ * m)) := by positivity
  have hsum : ∑ t ∈ bad, testProb m k t = bad.card * Z⁻¹ := by
    calc ∑ t ∈ bad, testProb m k t = ∑ t ∈ bad, Z⁻¹ := Finset.sum_congr rfl (fun t _ => rfl)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum, ← div_eq_mul_inv, div_le_iff₀ hZpos]
  have hmp1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hone : (1:ℝ) ≤ ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) * ((m:ℝ) + 1) :=
    (div_le_iff₀ hmp1).mp hL
  have hkey : q * bad.card ≤ q * (((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m))) * Z) := by
    calc q * bad.card ≤ 3 * Real.exp (-(c₀ * m)) := hmain
      _ = (3 * Real.exp (-(c₀ * m))) * 1 := by ring
      _ ≤ (3 * Real.exp (-(c₀ * m))) * (((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) * ((m:ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hone hE0
      _ = q * (((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m))) * Z) := by rw [← hqZ]; ring
  exact le_of_mul_le_mul_left hkey hqpos


lemma exp_decay_negl (c₀ : ℝ) (hc₀ : 0 < c₀) (c : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 3 * ((m:ℝ) + 1) * Real.exp (-(c₀ * m)) ≤ ((m:ℝ) ^ c)⁻¹ ∧ 1 ≤ m := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (c + 1) * Real.exp (-x)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (c + 1)
  have h2 : Filter.Tendsto (fun m : ℕ => c₀ * (m:ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc₀ tendsto_natCast_atTop_atTop
  have h3 := h1.comp h2
  have h4 : Filter.Tendsto (fun m : ℕ => (m:ℝ) ^ (c + 1) * Real.exp (-(c₀ * m))) Filter.atTop (nhds 0) := by
    have := h3.div_const (c₀ ^ (c + 1))
    simp only [zero_div] at this
    refine this.congr (fun m => ?_)
    simp only [Function.comp]
    rw [mul_pow]
    field_simp
  have h5 := h4.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 6))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h5
  refine ⟨max N 1, fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨?_, hm1⟩
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hmpos : (0:ℝ) < m := by linarith
  have := hN m hmN
  rw [← one_div, le_div_iff₀ (pow_pos hmpos c)]
  have hexp := (Real.exp_pos (-(c₀ * m))).le
  calc 3 * ((m:ℝ) + 1) * Real.exp (-(c₀ * m)) * (m:ℝ) ^ c
      ≤ 3 * (2 * (m:ℝ)) * Real.exp (-(c₀ * m)) * (m:ℝ) ^ c := by
        have : (m:ℝ) + 1 ≤ 2 * m := by linarith
        have h0 : 0 ≤ Real.exp (-(c₀ * m)) * (m:ℝ) ^ c := mul_nonneg hexp (pow_pos hmpos c).le
        nlinarith
    _ = 6 * ((m:ℝ) ^ (c + 1) * Real.exp (-(c₀ * m))) := by ring
    _ ≤ 1 := by linarith


theorem sampling_aux (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (x xhat : Fin m → Bool),
        ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
          testProb m ⌊α * m⌋₊ t ≤ ν m := by
  classical
  set ε₁ : ℝ := min ε 1 with hε₁
  have hε10 : 0 < ε₁ := lt_min hε one_pos
  have hε11 : ε₁ ≤ 1 := min_le_right _ _
  have hε1ε : ε₁ ≤ ε := min_le_left _ _
  set δ : ℝ := min (1 - α) α with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) hα0
  set c₀ : ℝ := (ε₁ * δ) ^ 2 / 1024 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  let ν : ℕ → ℝ := fun m =>
    if 2 / α ≤ (m:ℝ) then ((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m)))
    else ∑ t : Test m ⌊α * m⌋₊, testProb m ⌊α * m⌋₊ t
  refine ⟨ν, ?_, ?_⟩
  · intro c
    obtain ⟨N, hN⟩ := exp_decay_negl c₀ hc₀pos c
    refine ⟨max N ⌈2 / α⌉₊, fun m hm => ?_⟩
    have hmN : N ≤ m := le_trans (le_max_left _ _) hm
    have hm2 : 2 / α ≤ (m:ℝ) := by
      have : ⌈2 / α⌉₊ ≤ m := le_trans (le_max_right _ _) hm
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
    obtain ⟨h1, h2⟩ := hN m hmN
    simp only [ν, if_pos hm2]
    rw [abs_of_nonneg (by positivity)]
    calc ((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m))) = 3 * ((m:ℝ) + 1) * Real.exp (-(c₀ * m)) := by ring
      _ ≤ _ := h1
  · intro m x xhat
    by_cases hm : 2 / α ≤ (m:ℝ)
    · simp only [ν, if_pos hm]
      calc ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
            testProb m ⌊α * m⌋₊ t
          ≤ ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε₁ xhat t),
            testProb m ⌊α * m⌋₊ t := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
              intro hx
              apply ht
              simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              linarith
            · intro t _ _
              unfold testProb; positivity
        _ ≤ _ := samp_main α ε₁ hα0 hα1 hε10 hε11 m hm x xhat
    · simp only [ν, if_neg hm]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro t _ _
      unfold testProb; positivity

end CommitOpen.Benign

open CommitOpen.Benign

theorem solution (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (x xhat : Fin m → Bool),
        ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
          testProb m ⌊α * m⌋₊ t ≤ ν m :=
  sampling_aux α ε hα0 hα1 hε
