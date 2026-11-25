-- Prove2me | solution 1 for DetDLP.collision_variance_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:23:34.795825+00:00
-- url     : https://prove2.me/submissions/4a67ea0d-12ed-4172-9b4e-b2c41945ac4a

import Mathlib
import Definitions.Def_DetDLP_FactorBase

namespace DetDLP.AffineHash
open Finset
open scoped BigOperators

abbrev Seed (p : ℕ) := Fin (p-1) × Fin p

def slope {p : ℕ} (a : Fin (p-1)) : ZMod p := (a.val + 1 : ℕ)

def value {p : ℕ} (s : Seed p) (x : ZMod p) : ZMod p :=
  slope s.1 * x + (s.2.val : ZMod p)

theorem value_val {p : ℕ} [NeZero p] (s : Seed p) (x : ZMod p) :
    (value s x).val = ((s.1.val+1)*x.val+s.2.val)%p := by
  rw [← ZMod.val_natCast]
  congr 1
  simp [value, slope]

private theorem slope_val {p : ℕ} (a : Fin (p-1)) : (slope a).val = a.val + 1 :=
  ZMod.val_natCast_of_lt (by have := a.isLt; omega)

private theorem slope_ne_zero {p : ℕ} (a : Fin (p-1)) : slope a ≠ 0 := by
  intro h
  have e := congrArg ZMod.val h
  rw [slope_val, ZMod.val_zero] at e
  omega

private theorem slope_injective (p : ℕ) : Function.Injective (@slope p) := by
  intro a b h
  have e := congrArg ZMod.val h
  rw [slope_val, slope_val] at e
  exact Fin.ext (by omega)

private def onePointEquiv {p T : ℕ} [NeZero p] (hT : T ≤ p) (x : ZMod p) :
    {s : Seed p // (value s x).val < T} ≃ Fin (p-1) × Fin T where
  toFun s := (s.val.1, ⟨(value s.val x).val, s.property⟩)
  invFun r := ⟨(r.1, ⟨((r.2.val : ZMod p) - slope r.1 * x).val, ZMod.val_lt _⟩), by
    simpa [value, ZMod.val_natCast_of_lt (show r.2.val < p by have := r.2.isLt; omega)]
      using r.2.isLt⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [value, ZMod.val_natCast_of_lt s.val.2.isLt]
  right_inv r := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [value, ZMod.val_natCast_of_lt (show r.2.val < p by have := r.2.isLt; omega)]

theorem onePointCount {p T : ℕ} [NeZero p] (hT : T ≤ p) (x : ZMod p) :
    (univ.filter fun s : Seed p => (value s x).val < T).card = (p-1)*T := by
  have e := Fintype.card_congr (onePointEquiv hT x)
  rw [Fintype.card_of_subtype (univ.filter fun s : Seed p => (value s x).val < T) (by simp)] at e
  simpa using e

theorem twoPointCount {p T : ℕ} [Fact p.Prime] {x y : ZMod p} (hxy : x ≠ y) :
    (univ.filter fun s : Seed p => (value s x).val < T ∧ (value s y).val < T).card ≤
      T*T - T := by
  let good := univ.filter fun s : Seed p => (value s x).val < T ∧ (value s y).val < T
  let toPair (s : Seed p) : ℕ × ℕ := ((value s x).val, (value s y).val)
  have hmap : Set.MapsTo toPair (good : Set (Seed p)) ((range T).offDiag : Finset _) := by
    intro s hs
    obtain ⟨hx, hy⟩ := (mem_filter.mp hs).2
    apply mem_offDiag.mpr
    refine ⟨mem_range.mpr hx, mem_range.mpr hy, ?_⟩
    intro h
    have he : value s x = value s y := by
      simpa [toPair] using congrArg (fun n : ℕ => (n : ZMod p)) h
    exact hxy (mul_left_cancel₀ (slope_ne_zero s.1) (add_right_cancel he))
  have hinj : Function.Injective toPair := by
    intro s t h
    have e₁ : value s x = value t x := by
      simpa [toPair] using congrArg (fun z : ℕ × ℕ => (z.1 : ZMod p)) h
    have e₂ : value s y = value t y := by
      simpa [toPair] using congrArg (fun z : ℕ × ℕ => (z.2 : ZMod p)) h
    dsimp [value] at e₁ e₂
    have e : (slope s.1 - slope t.1) * (x-y) = 0 := by linear_combination e₁ - e₂
    have ha := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr hxy))
    refine Prod.ext (slope_injective _ ha) (Fin.ext ?_)
    rw [ha] at e₁
    have hb := congrArg ZMod.val (add_left_cancel e₁)
    simpa [ZMod.val_natCast_of_lt s.2.isLt, ZMod.val_natCast_of_lt t.2.isLt] using hb
  simpa [offDiag_card] using card_le_card_of_injOn toPair hmap hinj.injOn


def hit {p : ℕ} (T : ℕ) (x : ZMod p) (s : Seed p) : ℝ :=
  if (value s x).val < T then 1 else 0

theorem oneMean {p T : ℕ} [hp : Fact p.Prime] (hT : T ≤ p) (x : ZMod p) :
    (𝔼 s, hit T x s) = (T : ℝ)/p := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [hit, sum_boole, onePointCount hT, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hp' : 0 < ((p-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p-1 by have := hp.out.one_lt; omega)
  field_simp

theorem twoMean {p T : ℕ} [hp : Fact p.Prime] (hT : T ≤ p) {x y : ZMod p} (hxy : x ≠ y) :
    (𝔼 s, hit T x s * hit T y s) ≤ ((T : ℝ)/p)^2 := by
  have hind (s : Seed p) : hit T x s * hit T y s =
      (if (value s x).val < T ∧ (value s y).val < T then 1 else 0) := by
    unfold hit
    split_ifs <;> simp_all
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [hind]
  rw [sum_boole, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hp1 : 1 ≤ p := hp.out.one_le
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hp'' : 0 < ((p-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p-1 by have := hp.out.one_lt; omega)
  have hcount := twoPointCount (T := T) hxy
  have hnon : T ≤ T*T := Nat.le_mul_self T
  apply (div_le_iff₀ (show 0 < (( (p-1)*p : ℕ) : ℝ) by push_cast; positivity)).mpr
  calc
    _ ≤ ((T*T-T : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ _ := by
      rw [Nat.cast_sub hnon, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
      have hTp : (T : ℝ) ≤ p := by exact_mod_cast hT
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hTp) (Nat.cast_nonneg (α := ℝ) T)]

end DetDLP.AffineHash

open Finset
open scoped BigOperators
namespace DetDLP.Moment

theorem single_block {A S : Type*} [Fintype S] [DecidableEq A] (D : Finset A)
    (I : A → S → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (B : A → Finset A) (hB : ∀ a ∈ D, (B a).card ≤ 2)
    (h1 : ∀ a ∈ D, (𝔼 s, I a s) = θ)
    (h2 : ∀ a ∈ D, ∀ b ∈ D, (𝔼 s, I a s * I b s) ≤
      θ^2 + (if b ∈ B a then θ else 0)) :
    (𝔼 s, ∑ a ∈ D, I a s) = D.card * θ ∧
    (𝔼 s, (∑ a ∈ D, I a s)^2) ≤ (D.card * θ)^2 + 2*(D.card*θ) := by
  constructor
  · rw [expect_sum_comm]
    calc
      _ = ∑ _a ∈ D, θ := sum_congr rfl (fun a ha => h1 a ha)
      _ = _ := by simp
  · calc
      _ = ∑ a ∈ D, ∑ b ∈ D, 𝔼 s, I a s * I b s := by
        simp_rw [sq, sum_mul, mul_sum, expect_sum_comm]
      _ ≤ ∑ _a ∈ D, ((D.card : ℝ)*θ^2 + 2*θ) := by
        apply sum_le_sum
        intro a ha
        calc
          _ ≤ ∑ b ∈ D, (θ^2 + if b ∈ B a then θ else 0) :=
            sum_le_sum (fun b hb => h2 a ha b hb)
          _ = (D.card : ℝ)*θ^2 + ((D.filter fun b => b ∈ B a).card : ℝ)*θ := by
            rw [sum_add_distrib, ← sum_filter]
            simp
          _ ≤ _ := by
            have h := card_le_card (show (D.filter fun b => b ∈ B a) ⊆ B a from
              fun b hb => (mem_filter.mp hb).2)
            gcongr
            exact_mod_cast h.trans (hB a ha)
      _ = _ := by simp; ring

theorem independent_blocks {S : Type*} [Fintype S] [Nonempty S] (X : S → ℝ) (q : ℝ)
    (hq : 0 < q) (h1 : (𝔼 s, X s) = q) (h2 : (𝔼 s, (X s)^2) ≤ q^2+2*q) (m : ℕ) :
    (𝔼 s : Fin m → S, ((∏ i, X (s i)) - q^m)^2) ≤ (q^m)^2*((1+2/q)^m-1) := by
  have ind (f : S → ℝ) : (𝔼 s : Fin m → S, ∏ i, f (s i)) = (𝔼 i, f i)^m := by
    simpa using (expect_pow univ f m).symm
  have hm : (𝔼 s : Fin m → S, ∏ i, X (s i)) = q^m := (ind X).trans (by rw [h1])
  have hm2 : (𝔼 s : Fin m → S, (∏ i, X (s i)) ^ 2) ≤ (q^2+2*q)^m := by
    simp_rw [← prod_pow]
    rw [ind (fun s => (X s)^2)]
    exact pow_le_pow_left₀ (Finset.expect_nonneg fun _ _ => sq_nonneg _) h2 _
  have hv : (𝔼 s : Fin m → S, ((∏ i, X (s i))-q^m)^2) =
      (𝔼 s : Fin m → S, (∏ i, X (s i))^2) - (q^m)^2 := by
    simp_rw [sub_sq, expect_add_distrib, expect_sub_distrib, ← expect_mul, ← mul_expect,
      Fintype.expect_const, hm]
    ring
  rw [hv]
  have hfactor : q^2+2*q=q^2*(1+2/q) := by field_simp <;> ring
  rw [hfactor, mul_pow, pow_right_comm q 2 m] at hm2
  linarith

end DetDLP.Moment

open Finset
open scoped BigOperators

namespace DetDLP.Moment

private theorem twoSeeds {S : Type*} [Fintype S] (f : S → S → ℝ) :
    (𝔼 s : Bool → S, f (s false) (s true)) = 𝔼 a, 𝔼 b, f a b := by
  calc
    _ = 𝔼 u : S × S, f u.1 u.2 :=
      Fintype.expect_equiv (Equiv.boolArrowEquivProd S) _ _ (fun _ => rfl)
    _ = _ := by simpa using (expect_product' (univ : Finset S) univ f)

theorem evalBool {S : Type*} [Fintype S] [Nonempty S] (b : Bool) (f : S → ℝ) :
    (𝔼 s : Bool → S, f (s b)) = 𝔼 a, f a := by
  cases b
  · simpa [Fintype.expect_const] using (twoSeeds fun a (_ : S) => f a)
  · simpa [Fintype.expect_const] using (twoSeeds fun (_ : S) b => f b)

theorem evalBool_pair {S : Type*} [Fintype S] {b c : Bool} (h : b ≠ c) (f g : S → ℝ) :
    (𝔼 s : Bool → S, f (s b)*g (s c)) = (𝔼 a, f a) * (𝔼 a, g a) := by
  cases b <;> cases c
  · contradiction
  · exact (twoSeeds fun a b => f a * g b).trans (Fintype.expect_mul_expect _ _).symm
  · simpa [mul_comm] using (twoSeeds fun a b => g a * f b).trans (Fintype.expect_mul_expect _ _).symm
  · contradiction
end DetDLP.Moment

namespace DetDLP.Moment

theorem threshold_valid {p n m g : ℕ} (hp : 0 < p) (hm : 2 ≤ m)
    (hn : 4096*m ≤ n) (hg : g ≤ n+1) :
    hashThreshold p n m g ≤ p ∧ 0 < qBlk p n (hashThreshold p n m g) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 8192 ≤ (n : ℝ) := by exact_mod_cast (show 8192 ≤ n by omega)
  have hg' : (g : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hg
  have m0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpow : 16*(g : ℝ) ≤ (n : ℝ)^m := by
    apply le_trans _ (pow_le_pow_right₀ (by linarith : 1 ≤ (n : ℝ)) hm)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)-17 by linarith) hn0.le]
  have root_le : (16*(g : ℝ))^((1 : ℝ)/m) ≤ n := by
    calc
      _ ≤ ((n : ℝ)^m)^((1 : ℝ)/m) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
      _ = (n : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; simp [m0.ne']
  have hstar : qStar m g ≤ n := max_le hn (Nat.ceil_le.mpr root_le)
  have hspos : 0 < (qStar m g : ℝ) := by
    exact_mod_cast (show 0 < qStar m g from lt_of_lt_of_le (by omega : 0 < 4096*m) (le_max_left _ _))
  constructor
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hn0).mpr
    gcongr
  · unfold qBlk hashThreshold
    have ht := (Nat.le_ceil ((p : ℝ) * (qStar m g : ℝ)/n))
    positivity
end DetDLP.Moment

namespace DetDLP.Moment
open Finset AffineHash
open scoped BigOperators

private def curveHit {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} (T : ℕ) :
    E.toAffine.Point → (Bool → Seed p) → ℝ
  | .zero, _ => 0
  | .some x y _, s => hit T x (s (decide (y.val % 2 = 1)))

private theorem curveMean {p T : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}
    (hT : T ≤ p) (a : E.toAffine.Point) (ha : a ≠ 0) :
    (𝔼 s, curveHit T a s) = (T : ℝ)/p := by
  letI : NeZero (p-1) := ⟨by have := (Fact.out : p.Prime).one_lt; omega⟩
  cases a with
  | zero => contradiction
  | some x y hy => exact (evalBool _ _).trans (oneMean hT x)

private theorem curveJoint {p T : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)}
    (hT : T ≤ p) (a b : E.toAffine.Point) (ha : a ≠ 0) (hb : b ≠ 0) :
    (𝔼 s, curveHit T a s * curveHit T b s) ≤
      ((T : ℝ)/p)^2 + (if b ∈ ({a, -a} : Finset _) then (T : ℝ)/p else 0) := by
  letI : NeZero (p-1) := ⟨by have := (Fact.out : p.Prime).one_lt; omega⟩
  cases a with
  | zero => contradiction
  | some x y hy =>
    cases b with
    | zero => contradiction
    | some z w hw =>
      let ε := decide (y.val % 2 = 1)
      let δ := decide (w.val % 2 = 1)
      let P : E.toAffine.Point := .some x y hy
      let Q : E.toAffine.Point := .some z w hw
      change (𝔼 s : Bool → Seed p, hit T x (s ε) * hit T z (s δ)) ≤
        ((T : ℝ)/p)^2 + (if Q ∈ ({P, -P} : Finset _) then (T : ℝ)/p else 0)
      by_cases hbad : Q ∈ ({P, -P} : Finset _)
      · rw [if_pos hbad]
        have hle : (𝔼 s : Bool → Seed p, hit T x (s ε)*hit T z (s δ)) ≤
            𝔼 s : Bool → Seed p, hit T x (s ε) := by
          apply expect_le_expect
          intro s _
          unfold hit
          split_ifs <;> norm_num
        rw [evalBool, oneMean hT] at hle
        linarith [sq_nonneg ((T : ℝ)/p)]
      · rw [if_neg hbad, add_zero]
        by_cases hεδ : ε = δ
        · rw [← hεδ, evalBool ε (fun s => hit T x s * hit T z s)]
          apply twoMean hT
          intro hx
          subst z
          apply hbad
          rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hw.1 hy.1 rfl with he | he
          · exact mem_insert.mpr (Or.inl (by cases he; rfl))
          · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (by cases he; rfl)))
        · rw [evalBool_pair hεδ, oneMean hT, oneMean hT, sq]

private theorem fpJoint {p T : ℕ} [Fact p.Prime] (hT : T ≤ p) (a b : (ZMod p)ˣ) :
    (𝔼 s, hit T (a : ZMod p) s * hit T (b : ZMod p) s) ≤
      ((T : ℝ)/p)^2 + (if b ∈ ({a} : Finset _) then (T : ℝ)/p else 0) := by
  by_cases h : a = b
  · subst b
    simp only [mem_singleton_self, if_true]
    have e (s : Seed p) : hit T (a : ZMod p) s * hit T (a : ZMod p) s = hit T (a : ZMod p) s := by
      unfold hit
      split_ifs <;> norm_num
    simp_rw [e, oneMean hT]
    linarith [sq_nonneg ((T : ℝ)/p)]
  · rw [if_neg (by simpa using Ne.symm h), add_zero]
    exact twoMean hT (fun e => h (Units.ext e))

private theorem fpCount {p : ℕ} [Fact p.Prime] {m : ℕ} (T : ℕ) (S : FpSeed p m) (i : Fin m) :
    ((fpFactorBlock T S i).card : ℝ) = ∑ a : (ZMod p)ˣ, hit T (a : ZMod p) (S i) := by
  unfold fpFactorBlock
  simp [hit, value_val, fpFactorMem]

private theorem ecCount {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    {m : ℕ} (T : ℕ) (S : ECSeed p m) (i : Fin m) :
    letI := ecPointFintype E
    ((ecFactorBlock E T S i).card : ℝ) =
      ∑ a ∈ (univ.erase (0 : E.toAffine.Point)), curveHit T a (S i) := by
  letI := ecPointFintype E
  have h (a : E.toAffine.Point) :
      curveHit T a (S i) = if ecFactorMem T S i a then 1 else 0 := by
    cases a <;> simp [ecFactorMem,curveHit,hit,value_val]
  calc
    _ = ∑ a : E.toAffine.Point, curveHit T a (S i) := by
      simp_rw [h]
      simp [ecFactorBlock]
    _ = _ := by
      simpa only [curveHit, add_zero] using
        (sum_erase_add univ (fun a => curveHit T a (S i)) (mem_univ (0 : E.toAffine.Point))).symm
end DetDLP.Moment

open DetDLP
set_option maxHeartbeats 600000 in
theorem solution :
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let q := qBlk p n T
        let μ := q ^ m
        (∑ S : ECSeed p m, ((productSize (ecFactorBlock E T S) : ℝ) - μ) ^ 2) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ μ^2 * ((1 + 2/q)^m - 1)) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let q := qBlk p n T
      let μ := q ^ m
      (∑ S : FpSeed p m, ((productSize (fpFactorBlock (p := p) T S) : ℝ) - μ) ^ 2) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ μ^2 * ((1 + 2/q)^m - 1)) := by
  constructor
  · intro p m hp hp3 hm E hE g n hg hn T q μ
    letI := ecPointFintype E
    letI : NeZero (p-1) := ⟨by have := hp.out.one_lt; omega⟩
    obtain ⟨hT, hq⟩ := Moment.threshold_valid hp.out.pos hm hn (show g ≤ n+1 by dsimp [n]; omega)
    let D := (Finset.univ.erase (0 : E.toAffine.Point))
    have hD : D.card = n := by simp [D, n, g]
    have hμ (a : E.toAffine.Point) (ha : a ∈ D) := Moment.curveMean hT a (Finset.mem_erase.mp ha).1
    have hJ (a : E.toAffine.Point) (ha : a ∈ D) (b : E.toAffine.Point) (hb : b ∈ D) :=
      Moment.curveJoint hT a b (Finset.mem_erase.mp ha).1 (Finset.mem_erase.mp hb).1
    obtain ⟨mean, second⟩ := Moment.single_block D (Moment.curveHit T) ((T : ℝ)/p) (by positivity)
      (fun a => {a,-a}) (fun a _ => Finset.card_le_two) hμ hJ
    have hθ : (D.card : ℝ) * ((T : ℝ)/p) = q := by rw [hD]; dsimp [q,qBlk]; ring
    rw [hθ] at mean second
    rw [← Fintype.expect_eq_sum_div_card]
    have e (S : ECSeed p m) : (productSize (ecFactorBlock E T S) : ℝ) =
        ∏ i, ∑ a ∈ D, Moment.curveHit T a (S i) := by
      unfold productSize
      push_cast
      exact Finset.prod_congr rfl (fun i _ => Moment.ecCount E T S i)
    simp_rw [e]
    exact Moment.independent_blocks _ q hq mean second m
  · intro p m hp hm g n hg hn T q μ
    letI : NeZero (p-1) := ⟨by have := hp.out.one_lt; omega⟩
    obtain ⟨hT,hq⟩ := Moment.threshold_valid hp.out.pos hm hn (show g ≤ n+1 by omega)
    have hD : (Finset.univ : Finset (ZMod p)ˣ).card = n := by
      rw [Finset.card_univ,ZMod.card_units_eq_totient,Nat.totient_prime hp.out]
    obtain ⟨mean, second⟩ := Moment.single_block (Finset.univ : Finset (ZMod p)ˣ)
      (fun a => AffineHash.hit T (a : ZMod p)) ((T : ℝ)/p) (by positivity)
      (fun a => {a}) (by simp)
      (fun a _ => AffineHash.oneMean hT (a : ZMod p)) (fun a _ b _ => Moment.fpJoint hT a b)
    have hθ : ((Finset.univ : Finset (ZMod p)ˣ).card : ℝ) * ((T : ℝ)/p) = q := by
      rw [hD]; dsimp [q,qBlk]; ring
    rw [hθ] at mean second
    rw [← Fintype.expect_eq_sum_div_card]
    have e (S : FpSeed p m) : (productSize (fpFactorBlock T S) : ℝ) =
        ∏ i, ∑ a : (ZMod p)ˣ, AffineHash.hit T (a : ZMod p) (S i) := by
      unfold productSize
      push_cast
      exact Finset.prod_congr rfl (fun i _ => Moment.fpCount T S i)
    simp_rw [e]
    exact Moment.independent_blocks _ q hq mean second m
