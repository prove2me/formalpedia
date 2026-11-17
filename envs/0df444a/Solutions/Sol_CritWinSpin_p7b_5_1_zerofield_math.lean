-- Prove2me | solution 1 for CritWinSpin.p7b_5_1_zerofield_math
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T10:20:29.642472+00:00
-- url     : https://prove2.me/submissions/36561e20-4c87-4768-bf48-789a6a7b5684

import Mathlib
import Definitions.Def_CritWinSpin_BinarySource

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

/-- Pairing map `(t, Y) ↦ (t, t ⊙ Y)` from `Bool × BinCfg n` to `BinCfg (n + 1)`. -/
def p7b51z_pair {n : ℕ} (p : Bool × BinCfg n) : BinCfg (n + 1) :=
  Fin.cons p.1 (fun i => p.1 == p.2 i)

/-- Inverse of `p7b51z_pair`: `(y 0, hatProd y)`. -/
def p7b51z_unpair {n : ℕ} (y : BinCfg (n + 1)) : Bool × BinCfg n :=
  (y 0, hatProd y)

lemma p7b51z_pair_left_inv {n : ℕ} (p : Bool × BinCfg n) :
    p7b51z_unpair (p7b51z_pair p) = p := by
  rcases p with ⟨t, Y⟩
  ext1
  · rfl
  · funext i
    simp [p7b51z_unpair, p7b51z_pair, hatProd]

lemma p7b51z_pair_right_inv {n : ℕ} (y : BinCfg (n + 1)) :
    p7b51z_pair (p7b51z_unpair y) = y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [p7b51z_pair, p7b51z_unpair]
  · intro j
    simp [p7b51z_pair, p7b51z_unpair, hatProd]

/-- Explicit equivalence `Bool × BinCfg n ≃ BinCfg (n + 1)`. -/
def p7b51z_equiv (n : ℕ) : Bool × BinCfg n ≃ BinCfg (n + 1) where
  toFun := p7b51z_pair
  invFun := p7b51z_unpair
  left_inv := p7b51z_pair_left_inv
  right_inv := p7b51z_pair_right_inv

lemma p7b51z_spinOf_beq (a b : Bool) : spinOf (a == b) = spinOf a * spinOf b := by
  cases a <;> cases b <;> simp [spinOf]

lemma p7b51z_spinOf_sq (a : Bool) : spinOf a * spinOf a = 1 := by
  cases a <;> simp [spinOf]

lemma p7b51z_hatInst_symm {n : ℕ} (M : Inst n) (hSym : M.1.IsSymm) : (hatInst M).1.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply]
  refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
  · simp [hatInst]
  · intro j'; simp [hatInst]
  · intro i'; simp [hatInst]
  · intro i' j'
    have hij := congrFun (congrFun hSym i') j'
    simpa [hatInst, Matrix.transpose_apply] using hij.symm

lemma p7b51z_hatInst_diag {n : ℕ} (M : Inst n) (hDiag : ∀ i, M.1 i i = 0) :
    ∀ i, (hatInst M).1 i i = 0 := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simp [hatInst]
  · intro i'
    simpa [hatInst] using hDiag i'

lemma p7b51z_hatInst_width {n : ℕ} (M : Inst n) (w : ℕ) (hw : 1 ≤ w)
    (hW : width (castM M.1) (castV M.2) ≤ (n : ℝ) ^ w) :
    width (castM (hatInst M).1) (castV (hatInst M).2) ≤ ((n + 1 : ℕ) : ℝ) ^ (w + 1) := by
  unfold width
  apply ciSup_le
  intro i
  have hW_nonneg : 0 ≤ width (castM M.1) (castV M.2) := by
    by_cases hn0 : n = 0
    · subst hn0; simp [width]
    · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
      unfold width
      exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, Nat.pos_of_ne_zero hn0⟩ (by positivity)
  have hrow : ∀ i' : Fin n,
      |(M.2 i' : ℝ)| + ∑ j' : Fin n, |(M.1 i' j' : ℝ)| ≤ width (castM M.1) (castV M.2) := by
    intro i'
    simpa [width, castM, castV] using
      le_ciSup (Finite.bddAbove_range (fun i => |castV M.2 i| + ∑ j, |castM M.1 i j|)) i'
  refine Fin.cases ?_ ?_ i
  · simp only [castM, castV, hatInst, Matrix.map_apply, Matrix.of_apply, Fin.cases_zero,
      Rat.cast_zero, abs_zero, zero_add, Fin.sum_univ_succ]
    have hsum_le : ∑ j' : Fin n, |(M.2 j' : ℝ)| ≤ (n : ℝ) * width (castM M.1) (castV M.2) := by
      calc
        ∑ j' : Fin n, |(M.2 j' : ℝ)|
            ≤ ∑ j' : Fin n, (|(M.2 j' : ℝ)| + ∑ k' : Fin n, |(M.1 j' k' : ℝ)|) :=
          Finset.sum_le_sum fun j' _ => le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        _ ≤ ∑ _j' : Fin n, width (castM M.1) (castV M.2) := Finset.sum_le_sum fun j' _ => hrow j'
        _ = (n : ℝ) * width (castM M.1) (castV M.2) := by simp
    have hn1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    calc
      ∑ j' : Fin n, |(M.2 j' : ℝ)| ≤ (n : ℝ) * width (castM M.1) (castV M.2) := hsum_le
      _ ≤ (n : ℝ) * (n : ℝ) ^ w := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ (w + 1) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (w + 1) := by gcongr
  · intro i'
    simp only [castM, castV, hatInst, Matrix.map_apply, Matrix.of_apply, Fin.cases_succ,
      Rat.cast_zero, abs_zero, zero_add, Fin.sum_univ_succ, Fin.cases_zero]
    have hrow' := hrow i'
    by_cases hn0 : n = 0
    · exact Fin.elim0 (hn0 ▸ i')
    · have hn1_le : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
      have hpow : (n : ℝ) ^ w ≤ (n : ℝ) ^ (w + 1) := by
        calc
          (n : ℝ) ^ w = (n : ℝ) ^ w * 1 := (mul_one _).symm
          _ ≤ (n : ℝ) ^ w * (n : ℝ) := mul_le_mul_of_nonneg_left hn1_le (by positivity)
          _ = (n : ℝ) ^ (w + 1) := by ring
      have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      calc
        |(M.2 i' : ℝ)| + ∑ j' : Fin n, |(M.1 i' j' : ℝ)| ≤ width (castM M.1) (castV M.2) := hrow'
        _ ≤ (n : ℝ) ^ w := hW
        _ ≤ (n : ℝ) ^ (w + 1) := hpow
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ (w + 1) := by gcongr

lemma p7b51z_energy_hatInst {n : ℕ} (M : Inst n) (y : BinCfg (n + 1)) :
    energy (castM (hatInst M).1) (castV (hatInst M).2) (binVec y) =
      energy (castM M.1) (castV M.2) (binVec (hatProd y)) := by
  unfold energy binVec
  simp only [castM, castV, hatInst, Matrix.map_apply, Matrix.of_apply, Rat.cast_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Rat.cast_zero, zero_mul, Fin.sum_univ_succ, Fin.cases_succ,
    Fin.cons_succ]
  have hlin0 : ∑ x : Fin n, (M.2 x : ℝ) * spinOf (y 0) * spinOf (y x.succ) =
      ∑ x : Fin n, (M.2 x : ℝ) * spinOf (hatProd y x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hatProd, p7b51z_spinOf_beq, mul_assoc]
  have hrow0 : ∀ i' : Fin n,
      (M.2 i' : ℝ) * spinOf (y i'.succ) * spinOf (y 0) +
        ∑ j' : Fin n, (M.1 i' j' : ℝ) * spinOf (y i'.succ) * spinOf (y j'.succ) =
      (M.2 i' : ℝ) * spinOf (hatProd y i') +
        ∑ j' : Fin n, (M.1 i' j' : ℝ) * spinOf (hatProd y i') * spinOf (hatProd y j') := by
    intro i'
    congr 1
    · simp only [hatProd, p7b51z_spinOf_beq]; ring
    · refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [hatProd, p7b51z_spinOf_beq]
      have hsq : spinOf (y 0) * spinOf (y 0) = 1 := p7b51z_spinOf_sq (y 0)
      calc
        (M.1 i' j' : ℝ) * spinOf (y i'.succ) * spinOf (y j'.succ)
            = (M.1 i' j' : ℝ) * (spinOf (y 0) * spinOf (y 0)) * spinOf (y i'.succ) * spinOf (y j'.succ) := by
          rw [hsq, mul_one]
        _ = (M.1 i' j' : ℝ) * (spinOf (y 0) * spinOf (y i'.succ)) * (spinOf (y 0) * spinOf (y j'.succ)) := by
          ring
  simp only [zero_add, hlin0]
  rw [Finset.sum_congr rfl fun i' _ => hrow0 i', Finset.sum_add_distrib]
  ring

lemma p7b51z_muH_hatInst {n : ℕ} (M : Inst n) (y : BinCfg (n + 1)) :
    muH (castM (hatInst M).1) (castV (hatInst M).2) y =
      (1 / 2 : ℝ) * muH (castM M.1) (castV M.2) (hatProd y) := by
  unfold muH
  rw [p7b51z_energy_hatInst]
  have hZ : ∑ y' : BinCfg (n + 1),
      Real.exp (energy (castM (hatInst M).1) (castV (hatInst M).2) (binVec y')) =
      2 * ∑ Y : BinCfg n, Real.exp (energy (castM M.1) (castV M.2) (binVec Y)) := by
    rw [← (p7b51z_equiv n).sum_comp]
    simp only [p7b51z_equiv, Equiv.coe_fn_mk, p7b51z_energy_hatInst]
    have hhp : ∀ p : Bool × BinCfg n, hatProd (p7b51z_pair p) = p.2 := fun p => by
      simpa [p7b51z_unpair] using congrArg Prod.snd (p7b51z_pair_left_inv p)
    simp only [hhp]
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Bool.univ_eq]
  rw [hZ]
  ring

lemma p7b51z_unifOn_hat {n : ℕ} (Ω : Finset (BinCfg n)) (y : BinCfg (n + 1)) :
    unifOn (Finset.univ.filter fun y' : BinCfg (n + 1) => hatProd y' ∈ Ω) y =
      (1 / 2 : ℝ) * unifOn Ω (hatProd y) := by
  classical
  let Ωhat : Finset (BinCfg (n + 1)) := Finset.univ.filter fun y' => hatProd y' ∈ Ω
  have hcard : Ωhat.card = 2 * Ω.card := by
    have hbij : Ωhat.card = (Finset.univ ×ˢ Ω : Finset (Bool × BinCfg n)).card := by
      refine Finset.card_bij (fun y' _ => p7b51z_unpair y') ?_ ?_ ?_
      · intro y' hy'
        simp only [Ωhat, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
        simp [p7b51z_unpair, hy']
      · intro y₁ _ y₂ _ h
        exact (p7b51z_equiv n).symm.injective h
      · intro p hp
        simp only [Finset.mem_product, Finset.mem_univ, true_and] at hp
        refine ⟨p7b51z_pair p, ?_, p7b51z_pair_left_inv p⟩
        simp only [Ωhat, Finset.mem_filter, Finset.mem_univ, true_and]
        have : hatProd (p7b51z_pair p) = p.2 := congrArg Prod.snd (p7b51z_pair_left_inv p)
        rw [this]
        exact hp
    rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  unfold unifOn
  have hmem : (y ∈ Ωhat) ↔ (hatProd y ∈ Ω) := by simp [Ωhat]
  by_cases hy : hatProd y ∈ Ω
  · rw [if_pos (hmem.mpr hy), if_pos hy, hcard]
    push_cast
    ring
  · rw [if_neg (mt hmem.mp hy), if_neg hy, mul_zero]

lemma p7b51z_half_sum_cons_unifOn {n : ℕ} (Ω : Finset (BinCfg n)) (y : BinCfg (n + 1)) :
    (1 / 2 : ℝ) * ∑ t : Bool, ∑ Y : BinCfg n, unifOn Ω Y *
        (if (Fin.cons t (fun i => t == Y i) : BinCfg (n + 1)) = y then (1 : ℝ) else 0) =
      unifOn (Finset.univ.filter fun y' : BinCfg (n + 1) => hatProd y' ∈ Ω) y := by
  have hsum : ∑ t : Bool, ∑ Y : BinCfg n, unifOn Ω Y *
        (if (Fin.cons t (fun i => t == Y i) : BinCfg (n + 1)) = y then (1 : ℝ) else 0) =
      unifOn Ω (hatProd y) := by
    rw [← Fintype.sum_prod_type']
    have hinj : ∀ p : Bool × BinCfg n,
        (Fin.cons p.1 (fun i => p.1 == p.2 i) = y) ↔ p = p7b51z_unpair y := by
      intro p
      change p7b51z_pair p = y ↔ p = p7b51z_unpair y
      exact (p7b51z_equiv n).apply_eq_iff_eq_symm_apply
    trans ∑ p : Bool × BinCfg n, if p = p7b51z_unpair y then unifOn Ω p.2 else 0
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p = p7b51z_unpair y
      · have h1 : (Fin.cons p.1 fun i => p.1 == p.2 i) = y := (hinj p).mpr hp
        rw [if_pos h1, if_pos hp, mul_one]
      · have h1 : (Fin.cons p.1 fun i => p.1 == p.2 i) ≠ y := fun h => hp ((hinj p).mp h)
        rw [if_neg h1, if_neg hp, mul_zero]
    · rw [Finset.sum_eq_single (p7b51z_unpair y)
        (fun p _ hp => if_neg hp) (fun h => absurd (Finset.mem_univ _) h)]
      simp [p7b51z_unpair]
  rw [hsum, p7b51z_unifOn_hat]

lemma p7b51z_tvDist_hat {n : ℕ} (p q : BinCfg n → ℝ) :
    tvDist (fun y : BinCfg (n + 1) => (1 / 2 : ℝ) * p (hatProd y))
        (fun y : BinCfg (n + 1) => (1 / 2 : ℝ) * q (hatProd y)) =
      tvDist p q := by
  unfold tvDist
  rw [← (p7b51z_equiv n).sum_comp]
  simp only [p7b51z_equiv, Equiv.coe_fn_mk]
  have hhp : ∀ x : Bool × BinCfg n, hatProd (p7b51z_pair x) = x.2 := fun x =>
    congrArg Prod.snd (p7b51z_pair_left_inv x)
  simp only [hhp, Fintype.sum_prod_type]
  have hterm : ∀ Y : BinCfg n, |(1 / 2 : ℝ) * p Y - (1 / 2 : ℝ) * q Y| = (1 / 2 : ℝ) * |p Y - q Y| := by
    intro Y
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat,
    ← Finset.mul_sum]
  ring

lemma p7b51z_prodLaw_hat_equiv {n T : ℕ} (p q : BinCfg n → ℝ) :
    tvDist (prodLaw (fun y : BinCfg (n + 1) => (1 / 2 : ℝ) * p (hatProd y)) (T := T))
        (prodLaw (fun y : BinCfg (n + 1) => (1 / 2 : ℝ) * q (hatProd y)) (T := T)) =
      tvDist (prodLaw p (T := T)) (prodLaw q (T := T)) := by
  let eT : (Fin T → Bool) × (Fin T → BinCfg n) ≃ (Fin T → BinCfg (n + 1)) :=
    { toFun := fun (ts, Ys) t => p7b51z_pair (ts t, Ys t)
      invFun := fun Fs => (fun t => (p7b51z_unpair (Fs t)).1, fun t => (p7b51z_unpair (Fs t)).2)
      left_inv := fun (ts, Ys) => by
        ext t <;> simp [p7b51z_pair_left_inv]
      right_inv := fun Fs => by
        funext t
        exact p7b51z_pair_right_inv (Fs t) }
  unfold tvDist
  rw [← eT.sum_comp, Fintype.sum_prod_type]
  have hhp : ∀ ts : Fin T → Bool, ∀ Ys : Fin T → BinCfg n, ∀ t : Fin T,
      hatProd (eT (ts, Ys) t) = Ys t := fun ts Ys t =>
    congrArg Prod.snd (p7b51z_pair_left_inv (ts t, Ys t))
  have hprod : ∀ (r : BinCfg n → ℝ) (ts : Fin T → Bool) (Ys : Fin T → BinCfg n),
      prodLaw (fun y : BinCfg (n + 1) => (1 / 2 : ℝ) * r (hatProd y)) (eT (ts, Ys)) =
        (1 / 2 : ℝ) ^ T * prodLaw r Ys := by
    intro r ts Ys
    unfold prodLaw
    calc
      ∏ t : Fin T, (1 / 2 : ℝ) * r (hatProd (eT (ts, Ys) t))
          = ∏ t : Fin T, (1 / 2 : ℝ) * r (Ys t) :=
        Finset.prod_congr rfl fun t _ => by rw [hhp ts Ys t]
      _ = (∏ _t : Fin T, (1 / 2 : ℝ)) * (∏ t : Fin T, r (Ys t)) := Finset.prod_mul_distrib
      _ = (1 / 2 : ℝ) ^ T * prodLaw r Ys := by simp [prodLaw]
  have hsum : ∑ ts : Fin T → Bool, ∑ Ys : Fin T → BinCfg n,
        |prodLaw (fun y => (1 / 2 : ℝ) * p (hatProd y)) (eT (ts, Ys)) -
          prodLaw (fun y => (1 / 2 : ℝ) * q (hatProd y)) (eT (ts, Ys))| =
      ∑ Ys : Fin T → BinCfg n, |prodLaw p Ys - prodLaw q Ys| := by
    simp_rw [hprod p, hprod q, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ T)]
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (1 / 2 : ℝ) ^ T * ((2 : ℝ) ^ T * ∑ Ys : Fin T → BinCfg n, |prodLaw p Ys - prodLaw q Ys|) =
        ∑ Ys : Fin T → BinCfg n, |prodLaw p Ys - prodLaw q Ys| := by
      have : (1 / 2 : ℝ) ^ T * (2 : ℝ) ^ T = 1 := by
        rw [← mul_pow]; norm_num
      rw [← mul_assoc, this, one_mul]
    exact hpow
  rw [hsum]

lemma p7b51z_hat_stat_part2_aux (n d n₀ : ℕ) (H : Inst n)
    (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (hstat :
      let μ := muH (castM H.1) (castV H.2)
      let V := unifOn Ω
      tvDist μ V ≤ Real.exp (-((n₀ : ℝ) ^ 2)) ∧
      (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw V (T := T)) (prodLaw μ (T := T)) ≤
        (T : ℝ) * Real.exp (-((n₀ : ℝ) ^ 2))) ∧
      (∀ m₀ : Fin d → Bool, ∑ y, V y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
      (∀ (T : ℕ) (i : Fin T)
        (pred : ({j : Fin T // j ≠ i} → BinCfg n) → (Fin d → Bool) → ℝ),
        (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
        ∑ Fs : Fin T → BinCfg n, prodLaw V Fs * pred (fun j => Fs j) (Ψ (Fs i)) =
          1 / (2 : ℝ) ^ d) ∧
      (∀ T : ℕ, ∑ Fs : Fin T → BinCfg n, prodLaw V Fs *
          (open Classical in if Function.Injective (fun t => Ψ (Fs t)) then (0 : ℝ) else 1) ≤
        (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) :
    let μhat := muH (castM (hatInst H).1) (castV (hatInst H).2)
    let Vhat := unifOn (Finset.univ.filter fun y : BinCfg (n + 1) => hatProd y ∈ Ω)
    let Ψhat := fun y : BinCfg (n + 1) => Ψ (hatProd y)
    tvDist μhat Vhat ≤ Real.exp (-((n₀ : ℝ) ^ 2)) ∧
    (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw Vhat (T := T)) (prodLaw μhat (T := T)) ≤
      (T : ℝ) * Real.exp (-((n₀ : ℝ) ^ 2))) ∧
    (∀ m₀ : Fin d → Bool, ∑ y, Vhat y * (if Ψhat y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
    (∀ (T : ℕ) (i : Fin T)
      (pred : ({j : Fin T // j ≠ i} → BinCfg (n + 1)) → (Fin d → Bool) → ℝ),
      (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
      ∑ Fs : Fin T → BinCfg (n + 1), prodLaw Vhat Fs * pred (fun j => Fs j) (Ψhat (Fs i)) =
        1 / (2 : ℝ) ^ d) ∧
    (∀ T : ℕ, ∑ Fs : Fin T → BinCfg (n + 1), prodLaw Vhat Fs *
        (open Classical in if Function.Injective (fun t => Ψhat (Fs t)) then (0 : ℝ) else 1) ≤
      (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d)) := by
  have hμ_eq : muH (castM (hatInst H).1) (castV (hatInst H).2) =
      fun y => (1 / 2 : ℝ) * muH (castM H.1) (castV H.2) (hatProd y) :=
    funext (p7b51z_muH_hatInst H)
  have hV_eq : unifOn (Finset.univ.filter fun y : BinCfg (n + 1) => hatProd y ∈ Ω) =
      fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y) :=
    funext (p7b51z_unifOn_hat Ω)
  dsimp only
  rw [hμ_eq, hV_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [p7b51z_tvDist_hat]
    exact hstat.1
  · intro T hT
    rw [p7b51z_prodLaw_hat_equiv]
    exact hstat.2.1 T hT
  · intro m₀
    rw [← (p7b51z_equiv n).sum_comp]
    simp only [p7b51z_equiv, Equiv.coe_fn_mk]
    have hhp : ∀ p : Bool × BinCfg n, hatProd (p7b51z_pair p) = p.2 := fun p =>
      congrArg Prod.snd (p7b51z_pair_left_inv p)
    simp only [hhp, Fintype.sum_prod_type]
    have hinner : ∀ _t : Bool,
        ∑ Y : BinCfg n, ((1 / 2 : ℝ) * unifOn Ω Y) *
            (if Ψ Y = m₀ then (1 : ℝ) else 0) =
          (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ d) := fun _t => by
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [hstat.2.2.1 m₀]
    rw [Finset.sum_congr rfl fun t _ => hinner t]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_ofNat]
    ring
  · intro T i pred hnn hsum1
    let eT : (Fin T → Bool) × (Fin T → BinCfg n) ≃ (Fin T → BinCfg (n + 1)) :=
      { toFun := fun (ts, Ys) t => p7b51z_pair (ts t, Ys t)
        invFun := fun Fs => (fun t => (p7b51z_unpair (Fs t)).1, fun t => (p7b51z_unpair (Fs t)).2)
        left_inv := fun (ts, Ys) => by ext t <;> simp [p7b51z_pair_left_inv]
        right_inv := fun Fs => by funext t; exact p7b51z_pair_right_inv (Fs t) }
    rw [← eT.sum_comp, Fintype.sum_prod_type]
    have hinner : ∀ ts : Fin T → Bool,
        ∑ Ys : Fin T → BinCfg n,
            prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) *
              pred (fun j => eT (ts, Ys) j) (Ψ (hatProd (eT (ts, Ys) i))) =
          (1 / 2 : ℝ) ^ T * (1 / (2 : ℝ) ^ d) := by
      intro ts
      have hhp : ∀ Ys : Fin T → BinCfg n, ∀ t : Fin T, hatProd (eT (ts, Ys) t) = Ys t :=
        fun Ys t => congrArg Prod.snd (p7b51z_pair_left_inv (ts t, Ys t))
      have hprod : ∀ Ys : Fin T → BinCfg n,
          prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) =
            (1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Ys := by
        intro Ys
        unfold prodLaw
        calc
          ∏ t : Fin T, (1 / 2 : ℝ) * unifOn Ω (hatProd (eT (ts, Ys) t))
              = ∏ t : Fin T, (1 / 2 : ℝ) * unifOn Ω (Ys t) :=
            Finset.prod_congr rfl fun t _ => by rw [hhp Ys t]
          _ = (∏ _t : Fin T, (1 / 2 : ℝ)) * (∏ t : Fin T, unifOn Ω (Ys t)) :=
            Finset.prod_mul_distrib
          _ = (1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Ys := by simp [prodLaw]
      let pred_ts : ({j : Fin T // j ≠ i} → BinCfg n) → (Fin d → Bool) → ℝ :=
        fun x m => pred (fun j => p7b51z_pair (ts j.1, x j)) m
      have hpred := hstat.2.2.2.1 T i pred_ts
        (fun x m => hnn _ m) (fun x => hsum1 _)
      calc
        ∑ Ys : Fin T → BinCfg n,
            prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) *
              pred (fun j => eT (ts, Ys) j) (Ψ (hatProd (eT (ts, Ys) i)))
            = ∑ Ys : Fin T → BinCfg n,
                ((1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Ys) *
                  pred_ts (fun j => Ys j) (Ψ (Ys i)) := by
          refine Finset.sum_congr rfl fun Ys _ => ?_
          rw [hprod Ys, hhp Ys i]
          rfl
        _ = (1 / 2 : ℝ) ^ T * ∑ Ys : Fin T → BinCfg n,
              prodLaw (unifOn Ω) Ys *
                pred_ts (fun j => Ys j) (Ψ (Ys i)) := by
          simp_rw [mul_assoc, ← Finset.mul_sum]
        _ = (1 / 2 : ℝ) ^ T * (1 / (2 : ℝ) ^ d) := by rw [hpred]
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hpow : (2 : ℝ) ^ T * ((1 / 2 : ℝ) ^ T * (1 / (2 : ℝ) ^ d)) = 1 / (2 : ℝ) ^ d := by
      have : (2 : ℝ) ^ T * (1 / 2 : ℝ) ^ T = 1 := by rw [← mul_pow]; norm_num
      rw [← mul_assoc, this, one_mul]
    exact hpow
  · intro T
    let eT : (Fin T → Bool) × (Fin T → BinCfg n) ≃ (Fin T → BinCfg (n + 1)) :=
      { toFun := fun (ts, Ys) t => p7b51z_pair (ts t, Ys t)
        invFun := fun Fs => (fun t => (p7b51z_unpair (Fs t)).1, fun t => (p7b51z_unpair (Fs t)).2)
        left_inv := fun (ts, Ys) => by ext t <;> simp [p7b51z_pair_left_inv]
        right_inv := fun Fs => by funext t; exact p7b51z_pair_right_inv (Fs t) }
    rw [← eT.sum_comp, Fintype.sum_prod_type]
    have hinner : ∀ ts : Fin T → Bool,
        ∑ Ys : Fin T → BinCfg n,
            prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) *
              (open Classical in if Function.Injective (fun t => Ψ (hatProd (eT (ts, Ys) t)))
                then (0 : ℝ) else 1) ≤
          (1 / 2 : ℝ) ^ T * ((T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d)) := by
      intro ts
      have hhp : ∀ Ys : Fin T → BinCfg n, ∀ t : Fin T, hatProd (eT (ts, Ys) t) = Ys t :=
        fun Ys t => congrArg Prod.snd (p7b51z_pair_left_inv (ts t, Ys t))
      have hprod : ∀ Ys : Fin T → BinCfg n,
          prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) =
            (1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Ys := by
        intro Ys
        unfold prodLaw
        calc
          ∏ t : Fin T, (1 / 2 : ℝ) * unifOn Ω (hatProd (eT (ts, Ys) t))
              = ∏ t : Fin T, (1 / 2 : ℝ) * unifOn Ω (Ys t) :=
            Finset.prod_congr rfl fun t _ => by rw [hhp Ys t]
          _ = (∏ _t : Fin T, (1 / 2 : ℝ)) * (∏ t : Fin T, unifOn Ω (Ys t)) :=
            Finset.prod_mul_distrib
          _ = (1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Ys := by simp [prodLaw]
      calc
        ∑ Ys : Fin T → BinCfg n,
            prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) *
              (open Classical in if Function.Injective (fun t => Ψ (hatProd (eT (ts, Ys) t)))
                then (0 : ℝ) else 1)
            = (1 / 2 : ℝ) ^ T * ∑ Ys : Fin T → BinCfg n,
                prodLaw (unifOn Ω) Ys *
                  (open Classical in if Function.Injective (fun t => Ψ (Ys t))
                    then (0 : ℝ) else 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun Ys _ => ?_
          rw [hprod Ys]
          have hinj_eq : (fun t => Ψ (hatProd (eT (ts, Ys) t))) =
              fun t => Ψ (Ys t) := funext fun t => by rw [hhp Ys t]
          rw [hinj_eq, mul_assoc]
        _ ≤ (1 / 2 : ℝ) ^ T * ((T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d)) :=
          mul_le_mul_of_nonneg_left (hstat.2.2.2.2 T) (by positivity)
    calc
      ∑ ts : Fin T → Bool, ∑ Ys : Fin T → BinCfg n,
          prodLaw (fun y => (1 / 2 : ℝ) * unifOn Ω (hatProd y)) (eT (ts, Ys)) *
            (open Classical in if Function.Injective (fun t => Ψ (hatProd (eT (ts, Ys) t)))
              then (0 : ℝ) else 1)
          ≤ ∑ _ts : Fin T → Bool, (1 / 2 : ℝ) ^ T * ((T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d)) :=
        Finset.sum_le_sum fun ts _ => hinner ts
      _ = (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        have : (2 : ℝ) ^ T * (1 / 2 : ℝ) ^ T = 1 := by rw [← mul_pow]; norm_num
        rw [← mul_assoc, this, one_mul]

lemma p7b51z_hat_stat_part2 {F : BilinearFamily} (src : BinarySource F)
    (d : ℕ) (desc : Str) (key : WatersKey F desc d)
    (hstat :
      let μ := muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)
      let V := unifOn (src.omega d desc key)
      let Ψ := src.psi d desc key
      tvDist μ V ≤ Real.exp (-((src.n0 d : ℝ) ^ 2)) ∧
      (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw V (T := T)) (prodLaw μ (T := T)) ≤
        (T : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2))) ∧
      (∀ m₀ : Fin d → Bool, ∑ y, V y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
      (∀ (T : ℕ) (i : Fin T)
        (pred : ({j : Fin T // j ≠ i} → BinCfg (src.n d)) → (Fin d → Bool) → ℝ),
        (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
        ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs * pred (fun j => Fs j) (Ψ (Fs i)) =
          1 / (2 : ℝ) ^ d) ∧
      (∀ T : ℕ, ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs *
          (open Classical in if Function.Injective (fun t => Ψ (Fs t)) then (0 : ℝ) else 1) ≤
        (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) :
    let μhat := muH (castM ((hatSource src).ham d desc key).1) (castV ((hatSource src).ham d desc key).2)
    let Vhat := unifOn ((hatSource src).omega d desc key)
    let Ψhat := (hatSource src).psi d desc key
    tvDist μhat Vhat ≤ Real.exp (-(((hatSource src).n0 d : ℝ) ^ 2)) ∧
    (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw Vhat (T := T)) (prodLaw μhat (T := T)) ≤
      (T : ℝ) * Real.exp (-(((hatSource src).n0 d : ℝ) ^ 2))) ∧
    (∀ m₀ : Fin d → Bool, ∑ y, Vhat y * (if Ψhat y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
    (∀ (T : ℕ) (i : Fin T)
      (pred : ({j : Fin T // j ≠ i} → BinCfg ((hatSource src).n d)) → (Fin d → Bool) → ℝ),
      (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
      ∑ Fs : Fin T → BinCfg ((hatSource src).n d), prodLaw Vhat Fs * pred (fun j => Fs j) (Ψhat (Fs i)) =
        1 / (2 : ℝ) ^ d) ∧
    (∀ T : ℕ, ∑ Fs : Fin T → BinCfg ((hatSource src).n d), prodLaw Vhat Fs *
        (open Classical in if Function.Injective (fun t => Ψhat (Fs t)) then (0 : ℝ) else 1) ≤
      (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d)) :=
  p7b51z_hat_stat_part2_aux (src.n d) d (src.n0 d) (src.ham d desc key)
    (src.omega d desc key) (src.psi d desc key) hstat

lemma p7b51z_hat_forgeProb_desc (F : BilinearFamily) (n d : ℕ) (desc : Str) (key : WatersKey F desc d)
    (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool) (A B_wrap : PPT) (T : ℕ)
    (hwrap : ∀ Fs : Fin T → BinCfg n,
      (1 / (2 : ℝ) ^ T) * ∑ ts : Fin T → Bool,
        A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
            List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
          (fun s => ∃ y_hat : BinCfg (n + 1), s = List.ofFn y_hat ∧
            hatProd y_hat ∈ Ω ∧
            ∀ t, Ψ (hatProd y_hat) ≠ Ψ (Fs t)) ≤
      B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
        (fun s => ∃ y : BinCfg n, s = List.ofFn y ∧ y ∈ Ω ∧
          ∀ t, Ψ y ≠ Ψ (Fs t))) :
    ∑ Fs : Fin T → BinCfg (n + 1),
        prodLaw (unifOn (Finset.univ.filter fun y : BinCfg (n + 1) => hatProd y ∈ Ω)) Fs *
          A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
            (fun s => ∃ y : BinCfg (n + 1), s = List.ofFn y ∧
              y ∈ Finset.univ.filter (fun y => hatProd y ∈ Ω) ∧
              ∀ t, Ψ (hatProd y) ≠ Ψ (hatProd (Fs t))) ≤
      ∑ Fs : Fin T → BinCfg n,
        prodLaw (unifOn Ω) Fs *
          B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
            (fun s => ∃ y : BinCfg n, s = List.ofFn y ∧ y ∈ Ω ∧ ∀ t, Ψ y ≠ Ψ (Fs t)) := by
  let eT : (Fin T → Bool) × (Fin T → BinCfg n) ≃ (Fin T → BinCfg (n + 1)) :=
    { toFun := fun (ts, Ys) t => p7b51z_pair (ts t, Ys t)
      invFun := fun Fs => (fun t => (p7b51z_unpair (Fs t)).1, fun t => (p7b51z_unpair (Fs t)).2)
      left_inv := fun (ts, Ys) => by ext t <;> simp [p7b51z_pair_left_inv]
      right_inv := fun Fs => by funext t; exact p7b51z_pair_right_inv (Fs t) }
  rw [← eT.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro Fs _
  have hhp : ∀ ts : Fin T → Bool, ∀ t : Fin T, hatProd (eT (ts, Fs) t) = Fs t := fun ts t =>
    congrArg Prod.snd (p7b51z_pair_left_inv (ts t, Fs t))
  have hprod : ∀ ts : Fin T → Bool,
      prodLaw (unifOn (Finset.univ.filter fun y => hatProd y ∈ Ω)) (eT (ts, Fs)) =
        (1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Fs := by
    intro ts
    unfold prodLaw
    calc
      ∏ t : Fin T, unifOn (Finset.univ.filter fun y => hatProd y ∈ Ω) (eT (ts, Fs) t)
          = ∏ t : Fin T, (1 / 2 : ℝ) * unifOn Ω (Fs t) := by
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [p7b51z_unifOn_hat, hhp ts t]
      _ = (1 / 2 : ℝ) ^ T * prodLaw (unifOn Ω) Fs := by
        rw [Finset.prod_mul_distrib]
        simp [prodLaw]
  have hterm : ∀ ts : Fin T → Bool,
      prodLaw (unifOn (Finset.univ.filter fun y => hatProd y ∈ Ω)) (eT (ts, Fs)) *
          A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (eT (ts, Fs) t)))
            (fun s => ∃ y : BinCfg (n + 1), s = List.ofFn y ∧
              y ∈ Finset.univ.filter (fun y => hatProd y ∈ Ω) ∧
              ∀ t, Ψ (hatProd y) ≠ Ψ (hatProd (eT (ts, Fs) t))) =
        prodLaw (unifOn Ω) Fs * ((1 / 2 : ℝ) ^ T *
          A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
              List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
            (fun s => ∃ y_hat : BinCfg (n + 1), s = List.ofFn y_hat ∧
              hatProd y_hat ∈ Ω ∧
              ∀ t, Ψ (hatProd y_hat) ≠ Ψ (Fs t))) := by
    intro ts
    rw [hprod ts]
    have hpsi : ∀ y_hat : BinCfg (n + 1),
        (∀ t : Fin T, Ψ (hatProd y_hat) ≠ Ψ (hatProd (eT (ts, Fs) t))) ↔
        (∀ t : Fin T, Ψ (hatProd y_hat) ≠ Ψ (Fs t)) := by
      intro y_hat
      refine forall_congr' fun t => ?_
      rw [hhp ts t]
    have hmem : ∀ y_hat : BinCfg (n + 1),
        y_hat ∈ Finset.univ.filter (fun y => hatProd y ∈ Ω) ↔ hatProd y_hat ∈ Ω := by
      intro y_hat; simp
    have hprob : A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (eT (ts, Fs) t)))
        (fun s => ∃ y : BinCfg (n + 1), s = List.ofFn y ∧
          y ∈ Finset.univ.filter (fun y => hatProd y ∈ Ω) ∧
          ∀ t, Ψ (hatProd y) ≠ Ψ (hatProd (eT (ts, Fs) t))) =
        A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
            List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
          (fun s => ∃ y_hat : BinCfg (n + 1), s = List.ofFn y_hat ∧
            hatProd y_hat ∈ Ω ∧
            ∀ t, Ψ (hatProd y_hat) ≠ Ψ (Fs t)) := by
      congr 1
      ext s
      simp only [hpsi, hmem]
    rw [hprob]
    ring
  rw [Finset.sum_congr rfl (fun ts _ => hterm ts), ← Finset.mul_sum, ← Finset.mul_sum]
  rw [one_div_pow]
  exact mul_le_mul_of_nonneg_left (hwrap Fs) (by unfold prodLaw unifOn; positivity)

lemma p7b51z_hat_forgeProb_le {F : BilinearFamily} (src : BinarySource F)
    (A B_wrap : PPT) (T d : ℕ)
    (hwrap : ∀ (desc : Str) (key : WatersKey F desc d) (Fs : Fin T → BinCfg (src.n d)),
      (1 / (2 : ℝ) ^ T) * ∑ ts : Fin T → Bool,
        A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
            List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
          (fun s => ∃ y_hat : BinCfg (src.n d + 1), s = List.ofFn y_hat ∧
            hatProd y_hat ∈ src.omega d desc key ∧
            ∀ t, src.psi d desc key (hatProd y_hat) ≠ src.psi d desc key (Fs t)) ≤
      B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
        (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
          ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t))) :
    forgeProb (hatSource src) A T d ≤ forgeProb src B_wrap T d := by
  unfold forgeProb keygenAvg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro key _
  dsimp only
  exact p7b51z_hat_forgeProb_desc F (src.n d) d (F.gen.alg (tupleCode [List.ofFn ω, unary d])) key
    (src.omega d (F.gen.alg (tupleCode [List.ofFn ω, unary d])) key)
    (src.psi d (F.gen.alg (tupleCode [List.ofFn ω, unary d])) key)
    A B_wrap T (hwrap (F.gen.alg (tupleCode [List.ofFn ω, unary d])) key)

lemma p7b51z_waters_genLaw {F : BilinearFamily} (C : WatersCircuit F) (d : ℕ) (desc : Str)
    (key : WatersKey F desc d) (hq : (F.q desc).Prime)
    (hinj : ∀ m₁ m₂ r₁ r₂,
      C.evalCfg d desc key m₁ (expo r₁) (signS2 key m₁ (expo r₁)) =
        C.evalCfg d desc key m₂ (expo r₂) (signS2 key m₂ (expo r₂)) →
      m₁ = m₂ ∧ r₁ = r₂) :
    ∀ y : BinCfg (C.n0 d), C.genLaw d desc key y = unifOn (C.omega d desc key) y := by
  classical
  have hqpos : 0 < F.q desc := hq.pos
  let _inst : NeZero (F.q desc) := ⟨hq.ne_zero⟩
  have hexpo_surj : ∀ z : ZMod (F.q desc), ∃! r : Fin (F.q desc), expo r = z := by
    intro z
    refine ⟨⟨z.val, ZMod.val_lt z⟩, ?_, ?_⟩
    · simp [expo]
    · intro r hr
      ext
      have := congrArg ZMod.val hr
      simpa [expo, ZMod.val_natCast, Nat.mod_eq_of_lt r.isLt] using this
  have hvalid_char : ∀ m s₁ s₂, IsValidSig key m s₁ s₂ ↔
      ∃ r : Fin (F.q desc), s₁ = expo r ∧ s₂ = signS2 key m (expo r) := by
    intro m s₁ s₂
    constructor
    · intro h
      obtain ⟨r, hr, _⟩ := hexpo_surj s₁
      refine ⟨r, hr.symm, ?_⟩
      simpa [IsValidSig, signS2, hr] using h.symm
    · rintro ⟨r, rfl, rfl⟩
      rfl
  have hcard : (C.omega d desc key).card = 2 ^ d * F.q desc := by
    let f : (Fin d → Bool) × Fin (F.q desc) → BinCfg (C.n0 d) :=
      fun p => C.evalCfg d desc key p.1 (expo p.2) (signS2 key p.1 (expo p.2))
    have homega_eq : C.omega d desc key = Finset.univ.image f := by
      ext y
      simp only [WatersCircuit.omega, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, f]
      constructor
      · rintro ⟨m, s₁, s₂, hsig, rfl⟩
        obtain ⟨r, hs₁, hs₂⟩ := (hvalid_char m s₁ s₂).mp hsig
        exact ⟨(m, r), by rw [hs₁, hs₂]⟩
      · rintro ⟨⟨m, r⟩, rfl⟩
        exact ⟨m, expo r, signS2 key m (expo r), (hvalid_char m _ _).mpr ⟨r, rfl, rfl⟩, rfl⟩
    have hinj_f : Function.Injective f := by
      rintro ⟨m₁, r₁⟩ ⟨m₂, r₂⟩ heq
      obtain ⟨hm, hr⟩ := hinj m₁ m₂ r₁ r₂ heq
      exact Prod.ext hm hr
    rw [homega_eq, Finset.card_image_of_injective _ hinj_f]
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  intro y
  unfold WatersCircuit.genLaw unifOn
  by_cases hy : y ∈ C.omega d desc key
  · rw [if_pos hy, hcard]
    simp only [WatersCircuit.omega, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with ⟨m₀, s₁₀, s₂₀, hsig₀, hy_eq⟩
    obtain ⟨r₀, hs₁₀, hs₂₀⟩ := (hvalid_char m₀ s₁₀ s₂₀).mp hsig₀
    have hy0 : y = C.evalCfg d desc key m₀ (expo r₀) (signS2 key m₀ (expo r₀)) := by
      rw [hy_eq, hs₁₀, hs₂₀]
    rw [← Fintype.sum_prod_type']
    have huniq : ∀ p : (Fin d → Bool) × Fin (F.q desc),
        (C.evalCfg d desc key p.1 (expo p.2) (signS2 key p.1 (expo p.2)) = y) ↔ p = (m₀, r₀) := by
      intro p
      constructor
      · intro hp
        rw [hy0] at hp
        obtain ⟨hm, hr⟩ := hinj p.1 m₀ p.2 r₀ hp
        exact Prod.ext hm hr
      · rintro rfl; exact hy0.symm
    have hsum1 : ∑ p : (Fin d → Bool) × Fin (F.q desc),
        (if C.evalCfg d desc key p.1 (expo p.2) (signS2 key p.1 (expo p.2)) = y then (1 : ℝ) else 0) = 1 := by
      trans ∑ p : (Fin d → Bool) × Fin (F.q desc), (if p = (m₀, r₀) then (1 : ℝ) else 0)
      · exact Finset.sum_congr rfl fun p _ => if_congr (huniq p) rfl rfl
      · simp
    rw [hsum1, mul_one]
    push_cast
    rfl
  · rw [if_neg hy]
    have hzero : ∀ m : Fin d → Bool, ∀ r : Fin (F.q desc),
        C.evalCfg d desc key m (expo r) (signS2 key m (expo r)) ≠ y := by
      intro m r hEq
      apply hy
      simp only [WatersCircuit.omega, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨m, expo r, signS2 key m (expo r), (hvalid_char m _ _).mpr ⟨r, rfl, rfl⟩, hEq.symm⟩
    simp [hzero]

theorem p7b51_zerofield_math_core :
    (∀ {n : ℕ} (M : Inst n) (w : ℕ), 1 ≤ w →
      M.1.IsSymm → (∀ i, M.1 i i = 0) → width (castM M.1) (castV M.2) ≤ (n : ℝ) ^ w →
      (hatInst M).1.IsSymm ∧ (∀ i, (hatInst M).1 i i = 0) ∧
      width (castM (hatInst M).1) (castV (hatInst M).2) ≤ ((n + 1 : ℕ) : ℝ) ^ (w + 1)) ∧
    (∀ {n : ℕ} (Ω : Finset (BinCfg n)) (y : BinCfg (n + 1)),
      (1 / 2 : ℝ) * ∑ t : Bool, ∑ Y : BinCfg n, unifOn Ω Y *
          (if (Fin.cons t (fun i => t == Y i) : BinCfg (n + 1)) = y then (1 : ℝ) else 0) =
        unifOn (Finset.univ.filter fun y' : BinCfg (n + 1) => hatProd y' ∈ Ω) y) ∧
    (∀ (F : BilinearFamily) (src : BinarySource F) (d : ℕ) (desc : Str) (key : WatersKey F desc d),
      (let μ := muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)
       let V := unifOn (src.omega d desc key)
       let Ψ := src.psi d desc key
       tvDist μ V ≤ Real.exp (-((src.n0 d : ℝ) ^ 2)) ∧
       (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw V (T := T)) (prodLaw μ (T := T)) ≤
         (T : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2))) ∧
       (∀ m₀ : Fin d → Bool, ∑ y, V y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
       (∀ (T : ℕ) (i : Fin T)
         (pred : ({j : Fin T // j ≠ i} → BinCfg (src.n d)) → (Fin d → Bool) → ℝ),
         (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
         ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs * pred (fun j => Fs j) (Ψ (Fs i)) =
           1 / (2 : ℝ) ^ d) ∧
       (∀ T : ℕ, ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs *
           (open Classical in if Function.Injective (fun t => Ψ (Fs t)) then (0 : ℝ) else 1) ≤
         (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) →
      let μhat := muH (castM ((hatSource src).ham d desc key).1) (castV ((hatSource src).ham d desc key).2)
      let Vhat := unifOn ((hatSource src).omega d desc key)
      let Ψhat := (hatSource src).psi d desc key
      tvDist μhat Vhat ≤ Real.exp (-(((hatSource src).n0 d : ℝ) ^ 2)) ∧
      (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw Vhat (T := T)) (prodLaw μhat (T := T)) ≤
        (T : ℝ) * Real.exp (-(((hatSource src).n0 d : ℝ) ^ 2))) ∧
      (∀ m₀ : Fin d → Bool, ∑ y, Vhat y * (if Ψhat y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
      (∀ (T : ℕ) (i : Fin T)
        (pred : ({j : Fin T // j ≠ i} → BinCfg ((hatSource src).n d)) → (Fin d → Bool) → ℝ),
        (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
        ∑ Fs : Fin T → BinCfg ((hatSource src).n d), prodLaw Vhat Fs * pred (fun j => Fs j) (Ψhat (Fs i)) =
          1 / (2 : ℝ) ^ d) ∧
      (∀ T : ℕ, ∑ Fs : Fin T → BinCfg ((hatSource src).n d), prodLaw Vhat Fs *
          (open Classical in if Function.Injective (fun t => Ψhat (Fs t)) then (0 : ℝ) else 1) ≤
        (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) ∧
    (∀ (F : BilinearFamily) (src : BinarySource F) (A B_wrap : PPT) (T d : ℕ),
      (∀ (desc : Str) (key : WatersKey F desc d) (Fs : Fin T → BinCfg (src.n d)),
        (1 / (2 : ℝ) ^ T) * ∑ ts : Fin T → Bool,
          A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
              List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
            (fun s => ∃ y_hat : BinCfg (src.n d + 1), s = List.ofFn y_hat ∧
              hatProd y_hat ∈ src.omega d desc key ∧
              ∀ t, src.psi d desc key (hatProd y_hat) ≠ src.psi d desc key (Fs t)) ≤
        B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
          (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
            ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t))) →
      forgeProb (hatSource src) A T d ≤ forgeProb src B_wrap T d) ∧
    (∀ (F : BilinearFamily) (C : WatersCircuit F) (d : ℕ) (desc : Str) (key : WatersKey F desc d),
      (F.q desc).Prime →
      (∀ m₁ m₂ r₁ r₂,
        C.evalCfg d desc key m₁ (expo r₁) (signS2 key m₁ (expo r₁)) =
          C.evalCfg d desc key m₂ (expo r₂) (signS2 key m₂ (expo r₂)) →
        m₁ = m₂ ∧ r₁ = r₂) →
      ∀ y : BinCfg (C.n0 d), C.genLaw d desc key y = unifOn (C.omega d desc key) y) := by
  refine ⟨fun M w hw hSym hDiag hW =>
      ⟨p7b51z_hatInst_symm M hSym, p7b51z_hatInst_diag M hDiag, p7b51z_hatInst_width M w hw hW⟩,
    @p7b51z_half_sum_cons_unifOn, @p7b51z_hat_stat_part2, @p7b51z_hat_forgeProb_le,
    @p7b51z_waters_genLaw⟩

end CritWinSpin

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
open scoped BigOperators

theorem solution :
    (∀ {n : ℕ} (M : Inst n) (w : ℕ), 1 ≤ w →
      M.1.IsSymm → (∀ i, M.1 i i = 0) → width (castM M.1) (castV M.2) ≤ (n : ℝ) ^ w →
      (hatInst M).1.IsSymm ∧ (∀ i, (hatInst M).1 i i = 0) ∧
      width (castM (hatInst M).1) (castV (hatInst M).2) ≤ ((n + 1 : ℕ) : ℝ) ^ (w + 1)) ∧
    (∀ {n : ℕ} (Ω : Finset (BinCfg n)) (y : BinCfg (n + 1)),
      (1 / 2 : ℝ) * ∑ t : Bool, ∑ Y : BinCfg n, unifOn Ω Y *
          (if (Fin.cons t (fun i => t == Y i) : BinCfg (n + 1)) = y then (1 : ℝ) else 0) =
        unifOn (Finset.univ.filter fun y' : BinCfg (n + 1) => hatProd y' ∈ Ω) y) ∧
    (∀ (F : BilinearFamily) (src : BinarySource F) (d : ℕ) (desc : Str) (key : WatersKey F desc d),
      (let μ := muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)
       let V := unifOn (src.omega d desc key)
       let Ψ := src.psi d desc key
       tvDist μ V ≤ Real.exp (-((src.n0 d : ℝ) ^ 2)) ∧
       (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw V (T := T)) (prodLaw μ (T := T)) ≤
         (T : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2))) ∧
       (∀ m₀ : Fin d → Bool, ∑ y, V y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
       (∀ (T : ℕ) (i : Fin T)
         (pred : ({j : Fin T // j ≠ i} → BinCfg (src.n d)) → (Fin d → Bool) → ℝ),
         (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
         ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs * pred (fun j => Fs j) (Ψ (Fs i)) =
           1 / (2 : ℝ) ^ d) ∧
       (∀ T : ℕ, ∑ Fs : Fin T → BinCfg (src.n d), prodLaw V Fs *
           (open Classical in if Function.Injective (fun t => Ψ (Fs t)) then (0 : ℝ) else 1) ≤
         (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) →
      let μhat := muH (castM ((hatSource src).ham d desc key).1) (castV ((hatSource src).ham d desc key).2)
      let Vhat := unifOn ((hatSource src).omega d desc key)
      let Ψhat := (hatSource src).psi d desc key
      tvDist μhat Vhat ≤ Real.exp (-(((hatSource src).n0 d : ℝ) ^ 2)) ∧
      (∀ T : ℕ, 1 ≤ T → tvDist (prodLaw Vhat (T := T)) (prodLaw μhat (T := T)) ≤
        (T : ℝ) * Real.exp (-(((hatSource src).n0 d : ℝ) ^ 2))) ∧
      (∀ m₀ : Fin d → Bool, ∑ y, Vhat y * (if Ψhat y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d) ∧
      (∀ (T : ℕ) (i : Fin T)
        (pred : ({j : Fin T // j ≠ i} → BinCfg ((hatSource src).n d)) → (Fin d → Bool) → ℝ),
        (∀ x m, 0 ≤ pred x m) → (∀ x, ∑ m, pred x m = 1) →
        ∑ Fs : Fin T → BinCfg ((hatSource src).n d), prodLaw Vhat Fs * pred (fun j => Fs j) (Ψhat (Fs i)) =
          1 / (2 : ℝ) ^ d) ∧
      (∀ T : ℕ, ∑ Fs : Fin T → BinCfg ((hatSource src).n d), prodLaw Vhat Fs *
          (open Classical in if Function.Injective (fun t => Ψhat (Fs t)) then (0 : ℝ) else 1) ≤
        (T.choose 2 : ℝ) * (1 / (2 : ℝ) ^ d))) ∧
    (∀ (F : BilinearFamily) (src : BinarySource F) (A B_wrap : PPT) (T d : ℕ),
      (∀ (desc : Str) (key : WatersKey F desc d) (Fs : Fin T → BinCfg (src.n d)),
        (1 / (2 : ℝ) ^ T) * ∑ ts : Fin T → Bool,
          A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
              List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
            (fun s => ∃ y_hat : BinCfg (src.n d + 1), s = List.ofFn y_hat ∧
              hatProd y_hat ∈ src.omega d desc key ∧
              ∀ t, src.psi d desc key (hatProd y_hat) ≠ src.psi d desc key (Fs t)) ≤
        B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
          (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
            ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t))) →
      forgeProb (hatSource src) A T d ≤ forgeProb src B_wrap T d) ∧
    (∀ (F : BilinearFamily) (C : WatersCircuit F) (d : ℕ) (desc : Str) (key : WatersKey F desc d),
      (F.q desc).Prime →
      (∀ m₁ m₂ r₁ r₂,
        C.evalCfg d desc key m₁ (expo r₁) (signS2 key m₁ (expo r₁)) =
          C.evalCfg d desc key m₂ (expo r₂) (signS2 key m₂ (expo r₂)) →
        m₁ = m₂ ∧ r₁ = r₂) →
      ∀ y : BinCfg (C.n0 d), C.genLaw d desc key y = unifOn (C.omega d desc key) y) :=
  p7b51_zerofield_math_core
