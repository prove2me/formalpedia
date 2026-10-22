-- Prove2me | solution 1 for FracPackCover.General.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:00:00.673591+00:00
-- url     : https://prove2.me/submissions/e8ea439c-8109-4241-9417-42e96eef76df

import Mathlib
import Definitions.Def_FracPackCover_General_Improve



namespace FracPackCover.General

open FracPackCover.Covering in
theorem rowVal_conv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x xt : Fin n → ℝ) (σ : ℝ) (i : Fin m) :
    rowVal A ((1 - σ) • x + σ • xt) i = (1 - σ) * rowVal A x i + σ * rowVal A xt i := by
  unfold rowVal
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; ring

open FracPackCover.Covering in
theorem lam_le_rho {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (P : Set (Fin n → ℝ)) (ρ : ℝ)
    (hW : WidthBound A b d P ρ) (x : Fin n → ℝ) (hx : x ∈ P) : lam A b d x ≤ ρ := by
  unfold lam
  apply Finset.sup'_le
  intro i _
  have := hW x hx i
  rw [div_le_iff₀ (hd i)]
  exact le_trans (le_abs_self _) this

open FracPackCover.Covering in
theorem potential_ge_exp {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (hα : 0 < α) (x : Fin n → ℝ) :
    Real.exp (α * lam A b d x) ≤ potential A b d α x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m))
    (fun i => (rowVal A x i - b i) / d i)
  have : lam A b d x = (rowVal A x i - b i) / d i := hi
  rw [this]
  unfold potential
  have h1 : Real.exp (α * ((rowVal A x i - b i) / d i)) = Real.exp (α * (rowVal A x i - b i) / d i) := by
    congr 1; ring
  rw [h1]
  exact Finset.single_le_sum (f := fun i => Real.exp (α * (rowVal A x i - b i) / d i))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

theorem potential_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (α : ℝ)
    (x : Fin n → ℝ) : 0 ≤ potential A b d α x :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

open FracPackCover.Covering in
theorem lemma43_core {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P)
    (α : ℝ) (hα : 0 < α)
    (xt : Fin n → ℝ) (hxt : xt ∈ P)
    (hnG2 : ¬ G2 A b d x (lam A b d x) (dualVec A b d α x)
      (lagr A b (dualVec A b d α x) xt))
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ lam A b d x / (24 * α * ρ ^ 2)) :
    α * σ * lam A b d x * potential A b d α x / 30 ≤
      potential A b d α x - potential A b d α ((1 - σ) • x + σ • xt) := by
  set l := lam A b d x with hl
  have hlρ : l ≤ ρ := lam_le_rho A b d hd P ρ hW x hx
  have hσ' : σ * (24 * α * ρ ^ 2) ≤ l := by
    rw [le_div_iff₀ (by positivity)] at hσ; exact hσ
  have hl0 : 0 ≤ l := by
    have : 0 ≤ σ * (24 * α * ρ ^ 2) := by positivity
    linarith
  set r : Fin m → ℝ := fun i => (rowVal A x i - b i) / d i with hr
  set rt : Fin m → ℝ := fun i => (rowVal A xt i - b i) / d i with hrt
  have hr1 : ∀ i, |r i| ≤ ρ := by
    intro i
    have := hW x hx i
    simp only [hr]
    rw [abs_div, abs_of_pos (hd i), div_le_iff₀ (hd i)]; exact this
  have hrt1 : ∀ i, |rt i| ≤ ρ := by
    intro i
    have := hW xt hxt i
    simp only [hrt]
    rw [abs_div, abs_of_pos (hd i), div_le_iff₀ (hd i)]; exact this
  have hασ0 : 0 ≤ α * σ := by positivity
  have hkey : α * σ * (24 * ρ) ≤ 1 := by
    have h1 : (α * σ * (24 * ρ)) * ρ ≤ 1 * ρ := by nlinarith
    exact le_of_mul_le_mul_right h1 hρ
  set t : Fin m → ℝ := fun i => α * σ * (rt i - r i) with ht
  have htb : ∀ i, |t i| ≤ α * σ * (2 * ρ) := by
    intro i
    simp only [ht]
    rw [abs_mul, abs_of_nonneg hασ0]
    apply mul_le_mul_of_nonneg_left _ hασ0
    calc |rt i - r i| ≤ |rt i| + |r i| := abs_sub _ _
      _ ≤ 2 * ρ := by linarith [hr1 i, hrt1 i]
  have htb1 : ∀ i, |t i| ≤ 1 := by
    intro i
    have := htb i
    have : α * σ * (2 * ρ) ≤ 1 := by nlinarith
    linarith [htb i]
  have hexp : ∀ i, Real.exp (α * ((rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i)) ≤
      Real.exp (α * r i) * (1 + t i + t i ^ 2) := by
    intro i
    have h1 : α * ((rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i) = α * r i + t i := by
      rw [rowVal_conv]
      simp only [ht, hr, hrt]
      field_simp
      ring
    rw [h1, Real.exp_add]
    have := Real.abs_exp_sub_one_sub_id_le (htb1 i)
    have h2 : Real.exp (t i) ≤ 1 + t i + t i ^ 2 := by
      have := (abs_le.mp this).2; linarith
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hpot : potential A b d α ((1 - σ) • x + σ • xt) ≤
      ∑ i, Real.exp (α * r i) * (1 + t i + t i ^ 2) := by
    unfold potential
    apply Finset.sum_le_sum
    intro i _
    have := hexp i
    have h5 : α * (rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i =
        α * ((rowVal A ((1 - σ) • x + σ • xt) i - b i) / d i) := by ring
    rw [h5]; exact this
  have hΦ : potential A b d α x = ∑ i, Real.exp (α * r i) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    simp only [hr]; congr 1; ring
  -- linear term
  have hlin : ∑ i, Real.exp (α * r i) * t i =
      α * σ * (lagr A b (dualVec A b d α x) xt - lagr A b (dualVec A b d α x) x) := by
    unfold lagr
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have := (hd i).ne'
    simp only [ht, hr, hrt, dualVec]
    field_simp
  have hsumyd : ∑ i, dualVec A b d α x i * d i = potential A b d α x := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    have := (hd i).ne'
    simp only [dualVec]
    field_simp
  have hquad : ∑ i, Real.exp (α * r i) * t i ^ 2 ≤
      (α * σ * (2 * ρ)) ^ 2 * potential A b d α x := by
    rw [hΦ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have : t i ^ 2 ≤ (α * σ * (2 * ρ)) ^ 2 := by
      rw [← sq_abs (t i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (htb i) 2
    nlinarith [Real.exp_pos (α * r i)]
  have hnG := not_le.mp hnG2
  unfold G2 at hnG
  rw [hsumyd] at hnG
  have hsq : (α * σ * (2 * ρ)) ^ 2 ≤ α * σ * l / 6 := by
    have : (α * σ * (2 * ρ)) ^ 2 = (α * σ) * (4 * σ * α * ρ ^ 2) := by ring
    rw [this]
    nlinarith
  have hΦ0 := potential_nonneg A b d α x
  have hsplit : ∑ i, Real.exp (α * r i) * (1 + t i + t i ^ 2) =
      potential A b d α x + ∑ i, Real.exp (α * r i) * t i + ∑ i, Real.exp (α * r i) * t i ^ 2 := by
    rw [hΦ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hsplit] at hpot
  rw [hlin] at hpot
  have h3 : (α * σ * (2 * ρ)) ^ 2 * potential A b d α x ≤ α * σ * l / 6 * potential A b d α x :=
    mul_le_mul_of_nonneg_right hsq hΦ0
  have h4 : α * σ * (l / 5 * potential A b d α x) ≤
      α * σ * (lagr A b (dualVec A b d α x) x - lagr A b (dualVec A b d α x) xt) :=
    mul_le_mul_of_nonneg_left hnG.le hασ0
  nlinarith

open FracPackCover.Covering in
theorem improveLoop_aux {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (lam0 α σ c Φ0 : ℝ) (K : ℕ) (hΦ0 : 0 ≤ Φ0) (hα : 0 < α) (hlam0 : 0 < lam0)
    (hσdef : σ = lam0 / (48 * α * ρ ^ 2)) (hσ1 : σ ≤ 1)
    (hcdef : c = α * σ * lam0 / 60) (hc1 : c ≤ 1)
    (hK : Φ0 * (1 - c) ^ K < Real.exp (α * lam0 / 2)) :
    ∀ (k : ℕ) (x : Fin n → ℝ) (j : ℕ), x ∈ P → potential A b d α x ≤ Φ0 * (1 - c) ^ j →
      j ≤ K → K + 1 ≤ j + k →
      (improveLoop A b d orc lam0 α σ k x).exit ≠ ImproveExit.outOfFuel ∧
      (improveLoop A b d orc lam0 α σ k x).calls + j ≤ K := by
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hασ0 : 0 ≤ α * σ := by positivity
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  intro k
  induction k with
  | zero => intro x j _ _ hjK hk; omega
  | succ k ih =>
    intro x j hx hΦ hjK hk
    by_cases hlt : lam A b d x < lam0 / 2
    · rw [improveLoop, if_pos hlt]
      refine ⟨by simp, by simpa using hjK⟩
    · rw [improveLoop, if_neg hlt]
      have hlam : lam0 / 2 ≤ lam A b d x := not_lt.mp hlt
      have hjK' : j < K := by
        by_contra h
        have hj : K ≤ j := not_lt.mp h
        have h1 : (1 - c) ^ j ≤ (1 - c) ^ K := pow_le_pow_of_le_one (by linarith) (by linarith) hj
        have h2 := potential_ge_exp A b d hd α hα x
        have h3 : Real.exp (α * lam0 / 2) ≤ Real.exp (α * lam A b d x) := by
          apply Real.exp_le_exp.mpr; nlinarith
        have h4 : Φ0 * (1 - c) ^ j ≤ Φ0 * (1 - c) ^ K := by
          apply mul_le_mul_of_nonneg_left h1
          exact hΦ0
        linarith
      set y := dualVec A b d α x with hy
      have hy0 : (0 : Fin m → ℝ) ≤ y := by
        intro i
        simp only [hy, dualVec, Pi.zero_apply]
        have := hd i
        positivity
      have hxt : orc y ∈ P := (horc y hy0).1
      by_cases hg : G2 A b d x (lam A b d x) y (lagr A b y (orc y))
      · rw [if_pos hg]
        refine ⟨by simp, ?_⟩
        simp only; omega
      · rw [if_neg hg]
        have hσ' : σ ≤ lam A b d x / (24 * α * ρ ^ 2) := by
          rw [hσdef]
          have : lam0 / (48 * α * ρ ^ 2) = (lam0 / 2) / (24 * α * ρ ^ 2) := by ring
          rw [this]
          gcongr
        have key := lemma43_core A b d P hP hd ρ hρ hW x hx α hα (orc y) hxt hg σ hσ0 hσ'
        have hx' : (1 - σ) • x + σ • orc y ∈ P :=
          hP hx hxt (by linarith) hσ0 (by ring)
        have hΦn := potential_nonneg A b d α x
        have hdec : potential A b d α ((1 - σ) • x + σ • orc y) ≤
            (1 - c) * potential A b d α x := by
          have h5 : 0 ≤ α * σ * potential A b d α x * (lam A b d x - lam0 / 2) := by
            apply mul_nonneg (by positivity) (by linarith)
          rw [hcdef]
          nlinarith
        have hΦ' : potential A b d α ((1 - σ) • x + σ • orc y) ≤ Φ0 * (1 - c) ^ (j + 1) := by
          calc _ ≤ (1 - c) * potential A b d α x := hdec
            _ ≤ (1 - c) * (Φ0 * (1 - c) ^ j) :=
                mul_le_mul_of_nonneg_left hΦ (by linarith)
            _ = Φ0 * (1 - c) ^ (j + 1) := by ring
        obtain ⟨h1, h2⟩ := ih _ (j + 1) hx' hΦ' (by omega) (by omega)
        refine ⟨h1, ?_⟩
        simp only
        omega

open FracPackCover.Covering in
theorem thm44_core {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (hlam : 0 < lam A b d x0) (fuel : ℕ)
    (hfuel : 2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0)
      ≤ (fuel : ℝ)) :
    (improveGeneral A b d ρ orc fuel x0).exit ≠ ImproveExit.outOfFuel ∧
      ((improveGeneral A b d ρ orc fuel x0).calls : ℝ) ≤
        2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0) := by
  set l0 := lam A b d x0 with hl0
  have hl0ρ : l0 ≤ ρ := lam_le_rho A b d hd P ρ hW x0 hx0
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by linarith
  set L := Real.log (12 * m * ρ / l0) with hL
  have hratio : 12 ≤ 12 * (m : ℝ) * ρ / l0 := by
    rw [le_div_iff₀ hlam]; nlinarith
  have hlog12 : 11 / 12 ≤ Real.log 12 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (12 : ℝ)) (by norm_num)
    norm_num at this ⊢; linarith
  have hL1 : 11 / 12 ≤ L := le_trans hlog12 (Real.log_le_log (by norm_num) hratio)
  have hLpos : 0 < L := by linarith
  have hlogm : Real.log m ≤ L := by
    apply Real.log_le_log hmpos
    rw [le_div_iff₀ hlam]; nlinarith
  set α := 4 / l0 * L with hαdef
  have hαpos : 0 < α := by positivity
  have hαl : α * l0 = 4 * L := by rw [hαdef]; field_simp
  have hαal : alphaGen m ρ l0 = α := rfl
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = l0 / (48 * α * ρ ^ 2) := ⟨_, rfl⟩
  have hIG : improveGeneral A b d ρ orc fuel x0 = improveLoop A b d orc l0 α σ fuel x0 := by
    rw [hσdef]; rfl
  have hαρ : 3 ≤ α * ρ := by nlinarith [mul_le_mul_of_nonneg_left hl0ρ hαpos.le]
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, div_le_one (by positivity)]
    nlinarith
  have hασ : α * σ = l0 / (48 * ρ ^ 2) := by
    rw [hσdef]; field_simp
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = α * σ * l0 / 60 := ⟨_, rfl⟩
  have hc : c = l0 ^ 2 / (2880 * ρ ^ 2) := by
    rw [hcdef, hασ]; field_simp; ring
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]; nlinarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 8640 * ρ ^ 2 / l0 ^ 2 * L := ⟨_, rfl⟩
  rw [← hRdef] at hfuel ⊢
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hcR : c * R = 3 * L := by
    rw [hRdef, hc]; field_simp; ring
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌊R⌋₊ + 1 := ⟨_, rfl⟩
  have hKR : R < K := by
    rw [hKdef]; push_cast; exact Nat.lt_floor_add_one R
  have hKR' : (K : ℝ) ≤ R + 1 := by
    rw [hKdef]; push_cast; linarith [Nat.floor_le hR0]
  obtain ⟨Φ0, hΦ0def⟩ : ∃ Φ0 : ℝ, Φ0 = m * Real.exp (α * l0) := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ0 := by rw [hΦ0def]; positivity
  have e1 : (1 - c) ^ K ≤ Real.exp (-((K : ℝ) * c)) := by
    rw [show -((K : ℝ) * c) = K * (-c) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-c)]) K
  have e2 : Φ0 * Real.exp (-((K : ℝ) * c)) < Real.exp (α * l0 / 2) := by
    have eq : Φ0 * Real.exp (-((K : ℝ) * c)) =
        Real.exp (Real.log m + α * l0 + -((K : ℝ) * c)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hmpos, hΦ0def]
    rw [eq]
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_left hKR hcpos]
  have hK : Φ0 * (1 - c) ^ K < Real.exp (α * l0 / 2) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left e1 hΦ0) e2
  have hpot0 : potential A b d α x0 ≤ Φ0 * (1 - c) ^ 0 := by
    rw [pow_zero, mul_one, hΦ0def]
    unfold potential
    calc ∑ i, Real.exp (α * (rowVal A x0 i - b i) / d i) ≤ ∑ _i : Fin m, Real.exp (α * l0) := by
          apply Finset.sum_le_sum
          intro i _
          apply Real.exp_le_exp.mpr
          have h1 : (rowVal A x0 i - b i) / d i ≤ l0 :=
            Finset.le_sup' (fun i => (rowVal A x0 i - b i) / d i) (Finset.mem_univ i)
          have : α * (rowVal A x0 i - b i) / d i = α * ((rowVal A x0 i - b i) / d i) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h1 hαpos.le
      _ = m * Real.exp (α * l0) := by simp
  have hfuelK : K + 1 ≤ fuel := by
    have : (K : ℝ) + 1 ≤ fuel := by linarith
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := improveLoop_aux A b d P hP hd ρ hρ hW orc horc l0 α σ c Φ0 K hΦ0 hαpos hlam
    hσdef hσ1 hcdef hc1 hK fuel x0 0 hx0 hpot0 (Nat.zero_le _) (by omega)
  rw [hIG]
  refine ⟨h1, ?_⟩
  have : (improveLoop A b d orc l0 α σ fuel x0).calls ≤ K := by omega
  have h3 : ((improveLoop A b d orc l0 α σ fuel x0).calls : ℝ) ≤ K := by exact_mod_cast this
  linarith

end FracPackCover.General

open FracPackCover.General


theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (hlam : 0 < lam A b d x0) (fuel : ℕ)
    (hfuel : 2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0)
      ≤ (fuel : ℝ)) :
    (improveGeneral A b d ρ orc fuel x0).exit ≠ ImproveExit.outOfFuel ∧
      ((improveGeneral A b d ρ orc fuel x0).calls : ℝ) ≤
        2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0) := by
  exact thm44_core A b d P hP hd ρ hρ hW orc horc x0 hx0 hlam fuel hfuel
