-- Prove2me | solution 1 for DetDLP.collision_energy_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:30:53.785973+00:00
-- url     : https://prove2.me/submissions/f6716353-ea9c-400a-936b-ca6f27164921

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

end DetDLP.Moment

open Finset
namespace DetDLP.Moment

private theorem four_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) : (4 : ZMod p) ≠ 0 := by
  rcases (show p = 4 ∨ 4 < p by omega) with rfl|hp
  · have h4 := (Fact.out : Nat.Prime 4)
    norm_num at h4
  · intro h
    have e := congrArg ZMod.val h
    norm_num [ZMod.val_natCast_of_lt hp, ZMod.val_ofNat, Nat.mod_eq_of_lt hp] at e

private def abscissa {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)} : E.toAffine.Point → ZMod p
  | .zero => 0
  | .some x _ _ => x

theorem doubling_fiber {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (E : WeierstrassCurve (ZMod p))
    (d : E.toAffine.Point) :
    letI := ecPointFintype E
    (univ.filter fun a : E.toAffine.Point => a+a=d).card ≤ 4 := by
  classical
  letI := ecPointFintype E
  let K := univ.filter fun a : E.toAffine.Point => a+a=0
  have hK (a : E.toAffine.Point) (ha : a ∈ K) : a = -a := eq_neg_of_add_eq_zero_left (mem_filter.mp ha).2
  have hroot : Set.MapsTo abscissa ((K.erase 0 : Finset _) : Set E.toAffine.Point) E.Ψ₂Sq.roots.toFinset := by
    rintro (_|⟨x,y,h⟩) ha
    · exact False.elim ((mem_erase.mp ha).1 rfl)
    have hneg := hK (.some x y h) (mem_erase.mp ha).2
    have hy : y = E.toAffine.negY x y := (WeierstrassCurve.Affine.Point.some.inj hneg).2
    have hy0 : 2*y+E.a₁*x+E.a₃=0 := by
      dsimp [WeierstrassCurve.Affine.negY] at hy
      linear_combination hy
    change x ∈ E.Ψ₂Sq.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (E.Ψ₂Sq_ne_zero (four_ne_zero hp3))]
    change E.Ψ₂Sq.eval x = 0
    have heq := (E.toAffine.equation_iff x y).mp h.1
    change y^2 + E.a₁*x*y + E.a₃*y = x^3+E.a₂*x^2+E.a₄*x+E.a₆ at heq
    calc
      _ = (2*y+E.a₁*x+E.a₃)^2 := by
        simp [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        linear_combination -4*heq
      _ = 0 := by rw [hy0]; norm_num
  have hinj : ((K.erase 0 : Finset _) : Set E.toAffine.Point).InjOn abscissa := by
    rintro (_|⟨x,y,h⟩) ha (_|⟨u,v,k⟩) hb e
    · rfl
    · exact False.elim ((mem_erase.mp ha).1 rfl)
    · exact False.elim ((mem_erase.mp hb).1 rfl)
    · rcases WeierstrassCurve.Affine.Point.X_eq_iff.mp e with he | he
      · exact he
      · exact he.trans (hK _ (mem_erase.mp hb).2).symm
  have h3 := (card_le_card_of_injOn abscissa hroot hinj).trans
    ((Multiset.toFinset_card_le E.Ψ₂Sq.roots).trans (Polynomial.card_roots' _))
  have hdeg := E.natDegree_Ψ₂Sq_le
  have hz : (0 : E.toAffine.Point) ∈ K := by simp [K]
  have herase := card_erase_of_mem hz
  let F := univ.filter fun a : E.toAffine.Point => a+a=d
  by_cases hn : F.Nonempty
  · obtain ⟨v,hv⟩ := hn
    have hv' := (mem_filter.mp hv).2
    have hmap : Set.MapsTo (fun a => a-v) (F : Set E.toAffine.Point) K := by
      intro a ha
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      have ha' := (mem_filter.mp ha).2
      calc
        a-v+(a-v) = (a+a)-(v+v) := by abel
        _ = 0 := by rw [ha',hv',sub_self]
    have hfin := card_le_card_of_injOn _ hmap (fun _ _ _ _ e => (sub_left_inj.mp e))
    change F.card ≤ 4
    omega
  · change F.card ≤ 4
    rw [not_nonempty_iff_eq_empty.mp hn]
    simp
end DetDLP.Moment

open Finset
namespace DetDLP.Energy

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def conv (f h : G → ℝ) (x : G) : ℝ := ∑ z, f z * h (x-z)

def spike (x : G) : ℝ := if x = 0 then 1 else 0

def convPow (f : G → ℝ) : ℕ → G → ℝ
  | 0 => spike
  | k+1 => conv f (convPow f k)

theorem conv_comm (f h : G → ℝ) (x : G) : conv f h x = conv h f x := by
  unfold conv
  rw [← (Equiv.subLeft x).sum_comp (fun y => h y * f (x-y))]
  simp [mul_comm, Equiv.subLeft_apply]

theorem conv_mass (f h : G → ℝ) : (∑ x, conv f h x) = (∑ x, f x) * ∑ x, h x := by
  unfold conv
  rw [sum_comm, sum_mul]
  apply sum_congr rfl
  intro z _
  rw [← mul_sum]
  congr 1
  exact (Equiv.subRight z).sum_comp h

theorem mass_pow (f : G → ℝ) (m : ℕ) : (∑ x, convPow f m x) = (∑ x, f x)^m := by
  induction m with
  | zero => simp [convPow,spike]
  | succ m ih => rw [convPow, conv_mass, ih, pow_succ']

theorem nonneg_pow {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) (m : ℕ) (x : G) : 0 ≤ convPow f m x := by
  induction m generalizing x with
  | zero => simp [convPow,spike]; split_ifs <;> norm_num
  | succ m ih => exact sum_nonneg fun y _ => mul_nonneg (hf y) (ih _)

theorem conv_le_add {f f' h : G → ℝ} (k : ℝ) (hf : ∀ x, f x ≤ k + f' x)
    (hh : ∀ x, 0 ≤ h x) (x : G) : conv f h x ≤ k*(∑ y, h y) + conv f' h x := by
  unfold conv
  calc
    _ ≤ ∑ z, (k + f' z)*h (x-z) := sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (hf z) (hh _))
    _ = _ := by
      simp_rw [add_mul, sum_add_distrib, ← mul_sum]
      have e : (∑ i, h (x-i)) = ∑ i, h i := (Equiv.subLeft x).sum_comp h
      rw [e]

theorem conv_spike (q : ℝ) (f : G → ℝ) (x : G) :
    conv (fun z => q*spike z) f x = q*f x := by
  classical simp [conv, spike, mul_ite, ite_mul]

theorem profile_bound (K M : G → ℝ) (q n : ℝ) (hq : 0 < q) (hn : 0 < n)
    (hKn : ∀ x, 0 ≤ K x) (hMn : ∀ x, 0 ≤ M x)
    (hK : ∀ x, K x ≤ q^2/n + M x) (hM : ∀ x, M x ≤ 4*q/n + q*spike x)
    (hKm : (∑ x, K x) ≤ q^2+2*q) (hMm : (∑ x, M x) ≤ 2*q) (m : ℕ) :
    convPow K m 0 ≤ q^m + (q^m)^2/n*((1+2/q)^m+4*(2/q)^m) := by
  let A := q^2+2*q
  have hmassK (k : ℕ) : (∑ x, convPow K k x) ≤ A^k := by
    rw [mass_pow]; exact pow_le_pow_left₀ (sum_nonneg (fun i _ => hKn i)) hKm _
  have hmassM (k : ℕ) : (∑ x, convPow M k x) ≤ (2*q)^k := by
    rw [mass_pow]; exact pow_le_pow_left₀ (sum_nonneg (fun i _ => hMn i)) hMm _
  have good (k : ℕ) (x : G) : convPow K k x ≤ A^k/n + convPow M k x := by
    induction k generalizing x with
    | zero => simp [convPow,hn.le] <;> positivity
    | succ k ih =>
      calc
        _ ≤ q^2/n * (∑ z, convPow K k z) + conv M (convPow K k) x :=
          conv_le_add _ hK (nonneg_pow hKn k) _
        _ ≤ q^2/n*A^k + (A^k/n*(∑ z, M z) + conv (convPow M k) M x) := by
          rw [conv_comm M]
          exact add_le_add (mul_le_mul_of_nonneg_left (hmassK k) (by positivity))
            (conv_le_add _ ih hMn _)
        _ ≤ q^2/n*A^k + (A^k/n*(2*q) + conv M (convPow M k) x) := by
          rw [conv_comm (convPow M k)]; gcongr
        _ = _ := by rw [convPow,pow_succ]; dsimp [A]; ring
  have marked (k : ℕ) (x : G) : convPow M k x ≤ q^k*spike x + 4*(2*q)^k/n := by
    induction k generalizing x with
    | zero => simp [convPow,hn.le] <;> positivity
    | succ k ih =>
      calc
        _ ≤ 4*q/n*(∑ z, convPow M k z) + conv (fun z => q*spike z) (convPow M k) x :=
          conv_le_add _ hM (nonneg_pow hMn k) _
        _ ≤ 4*q/n*(2*q)^k + q*(q^k*spike x + 4*(2*q)^k/n) := by
          rw [conv_spike]
          exact add_le_add (mul_le_mul_of_nonneg_left (hmassM k) (by positivity))
            (mul_le_mul_of_nonneg_left (ih x) hq.le)
        _ = _ := by rw [pow_succ q, pow_succ (2*q)]; ring
  have hfinal := (good m 0).trans (add_le_add_right (marked m 0) (A^m/n))
  simp [spike] at hfinal
  apply hfinal.trans_eq
  have hA : A = q^2*(1+2/q) := by dsimp [A]; field_simp
  have h2 : 2*q = q^2*(2/q) := by field_simp
  rw [hA,h2,mul_pow,mul_pow,pow_right_comm q 2 m]
  ring
end DetDLP.Energy

namespace DetDLP.Energy
open Finset
open scoped BigOperators
variable {A G : Type*} [Fintype A] [AddCommGroup G] [Fintype G] [DecidableEq G]

def fiber (v : A → G) (w : A → ℝ) (g : G) : ℝ := ∑ a, if v a = g then w a else 0

def profile (v : A → G) (w : A → ℝ) (m : ℕ) (g : G) : ℝ :=
  ∑ t : Fin m → A, if ∑ i, v (t i) = g then ∏ i, w (t i) else 0

theorem profile_conv (v : A → G) (w : A → ℝ) (m : ℕ) (g : G) :
    profile v w m g = convPow (fiber v w) m g := by
  induction m generalizing g with
  | zero => simp [profile,convPow,spike,eq_comm]
  | succ m ih =>
    let f (t : Fin (m+1) → A) : ℝ := if ∑ i, v (t i)=g then ∏ i, w (t i) else 0
    change (∑ t, f t) = _
    rw [← (Fin.consEquiv (fun _ : Fin (m+1) => A)).sum_comp f, Fintype.sum_prod_type]
    have head (a : A) (t : Fin m → A) : f (Fin.cons a t) =
        w a * (if ∑ i, v (t i) = g - v a then ∏ i, w (t i) else 0) := by
      simp only [f,Fin.sum_univ_succ,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_ite,mul_zero]
      congr 1
      exact propext eq_sub_iff_add_eq'.symm
    change (∑ a, ∑ t, f (Fin.cons a t)) = _
    simp_rw [head, ← mul_sum]
    change (∑ a, w a * profile v w m (g-v a)) = _
    simp_rw [ih]
    simp only [convPow,conv,fiber,sum_mul,ite_mul,zero_mul]
    rw [sum_comm (s := (univ : Finset G))]
    simp

private theorem square_hist (v : A → G) (w : A → ℝ) :
    (∑ g, (fiber v w g)^2) = ∑ a, ∑ b, if v a = v b then w a * w b else 0 := by
  simp_rw [fiber,sq,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  simp [ite_mul,mul_ite,eq_comm]

private def memWeight (F : Finset G) (a : G) : ℝ := if a ∈ F then 1 else 0

private theorem rep_weights {m : ℕ} (F : Fin m → Finset G) (x : G) :
    (repCountAdd F x : ℝ) = fiber (fun a : Fin m → G => ∑ i, a i)
      (fun a => ∏ i, memWeight (F i) (a i)) x := by
  have hset : Fintype.piFinset F = univ.filter (fun a : Fin m → G => ∀ i, a i ∈ F i) := by ext; simp
  rw [repCountAdd, hset, filter_filter, ← sum_boole]
  unfold fiber memWeight
  apply sum_congr rfl
  intro a _
  simp only [Fintype.prod_boole]
  split_ifs <;> simp_all

theorem weighted_energy {m : ℕ} (F : Fin m → Finset G) :
    (collisionEnergyAdd F : ℝ) = ∑ t : Fin m → G×G,
      if ∑ i, ((t i).1-(t i).2) = 0 then
        ∏ i, (memWeight (F i) (t i).1 * memWeight (F i) (t i).2) else 0 := by
  unfold collisionEnergyAdd
  push_cast
  simp_rw [rep_weights, square_hist]
  rw [← Fintype.sum_prod_type']
  rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => G) (fun _ => G)).sum_comp]
  apply sum_congr rfl
  intro t _
  simp [sum_sub_distrib,sub_eq_zero,prod_mul_distrib]

theorem indep_weights {S : Type*} [Fintype S] {m : ℕ} (f : Fin m → S → ℝ) :
    (𝔼 s : Fin m → S, ∏ i, f i (s i)) = ∏ i, 𝔼 s, f i s := by
  simp_rw [Fintype.expect_eq_sum_div_card,prod_div_distrib,Fintype.prod_sum]
  simp [Fintype.card_fun]

theorem energy_profile {S : Type*} [Fintype S] (F : S → Finset G) (m : ℕ) :
    (𝔼 s : Fin m → S, (collisionEnergyAdd (fun i => F (s i)) : ℝ)) =
      convPow (fiber (fun t : G×G => t.1-t.2)
        (fun t => 𝔼 s, memWeight (F s) t.1 * memWeight (F s) t.2)) m 0 := by
  rw [← profile_conv]
  simp_rw [weighted_energy, expect_sum_comm]
  unfold profile
  apply sum_congr rfl
  intro t _
  split_ifs
  · exact indep_weights (fun i (s : S) => memWeight (F s) (t i).1 * memWeight (F s) (t i).2)
  · simp
end DetDLP.Energy

namespace DetDLP.Energy
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem diff_fiber (f : G → G → ℝ) (d : G) :
    fiber (fun t : G×G => t.1-t.2) (fun t => f t.1 t.2) d = ∑ a, f a (a-d) := by
  unfold fiber
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  have he (b : G) : a-b = d ↔ b = a-d := by
    rw [eq_sub_iff_add_eq,sub_eq_iff_eq_add,add_comm b d,eq_comm]
  simp_rw [he]
  simp

theorem sum_diff (f : G → G → ℝ) :
    (∑ d, ∑ a, f a (a-d)) = ∑ a, ∑ b, f a b := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  exact (Equiv.subLeft a).sum_comp _

theorem kernel_bound (D : Finset G) (B : G → Finset G) (J : G → G → ℝ)
    (θ : ℝ) (hθ : 0 < θ) (hn : 0 < D.card)
    (hB : ∀ a ∈ D, (B a).card ≤ 2)
    (hBd : ∀ d : G, d ≠ 0 → (D.filter fun a => a-d ∈ B a).card ≤ 4)
    (hJn : ∀ a b, 0 ≤ J a b)
    (hJ : ∀ a b, J a b ≤ if a ∈ D then
      ((if b ∈ D then θ^2 else 0)+(if b ∈ B a then θ else 0)) else 0) (m : ℕ) :
    let n : ℝ := D.card
    let q := n*θ
    convPow (fiber (fun t : G×G => t.1-t.2) (fun t => J t.1 t.2)) m 0 ≤
      q^m + (q^m)^2/n*((1+2/q)^m+4*(2/q)^m) := by
  intro n q
  let M (d : G) := ((D.filter fun a => a-d ∈ B a).card : ℝ)*θ
  let K := fiber (fun t : G×G => t.1-t.2) (fun t => J t.1 t.2)
  have hn' : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hq : 0 < q := mul_pos hn' hθ
  have hMn (d : G) : 0 ≤ M d := by dsimp [M]; positivity
  have hKn (d : G) : 0 ≤ K d := by dsimp [K]; rw [diff_fiber]; exact sum_nonneg fun a _ => hJn _ _
  have hrow (a : G) : (∑ b, J a b) ≤
      if a ∈ D then n*θ^2+2*θ else 0 := by
    apply (sum_le_sum (fun b (_ : b ∈ univ) => hJ a b)).trans
    by_cases ha : a ∈ D
    · simp only [if_pos ha,sum_add_distrib,← sum_filter,sum_const,nsmul_eq_mul]
      simp only [filter_mem_eq_inter,univ_inter]
      change _ ≤ (D.card : ℝ)*θ^2+2*θ
      gcongr
      exact_mod_cast hB a ha
    · simp [ha]
  have hKm : (∑ d, K d) ≤ q^2+2*q := by
    dsimp [K]
    simp_rw [diff_fiber]
    rw [sum_diff]
    apply (sum_le_sum (fun a _ => hrow a)).trans_eq
    rw [← sum_filter]
    simp [q,n]
    ring
  have hMm : (∑ d, M d) ≤ 2*q := by
    have e (d : G) : M d = ∑ a ∈ D, if a-d ∈ B a then θ else 0 := by rw [← sum_filter]; simp [M]
    simp_rw [e]
    rw [sum_comm]
    calc
      _ = ∑ a ∈ D, ((B a).card : ℝ)*θ := by
        apply sum_congr rfl
        intro a _
        have he : (∑ d : G, if a-d ∈ B a then θ else 0) = ∑ b : G, if b ∈ B a then θ else 0 :=
          (Equiv.subLeft a).sum_comp (fun b => if b ∈ B a then θ else 0)
        rw [he, ← sum_filter]
        simp
      _ ≤ ∑ _ ∈ D, 2*θ := sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (by exact_mod_cast hB a ha) hθ.le)
      _ = _ := by simp [q,n]; ring
  have hKd (d : G) : K d ≤ q^2/n + M d := by
    dsimp [K]
    rw [diff_fiber]
    apply (sum_le_sum (fun a (_ : a ∈ univ) => hJ a (a-d))).trans
    rw [← sum_filter]
    simp only [filter_mem_eq_inter,univ_inter,sum_add_distrib]
    have he : q^2/n = n*θ^2 := by dsimp [q]; field_simp
    rw [he]
    apply add_le_add
    · apply (sum_le_sum (g := fun _ => θ^2) (fun a (_ : a ∈ D) => by split_ifs <;> first | rfl | positivity)).trans_eq
      simp [n]
    · rw [← sum_filter]; simp [M]
  have hMd (d : G) : M d ≤ 4*q/n + q*spike d := by
    have he : q/n = θ := by dsimp [q]; field_simp
    rw [mul_div_assoc,he]
    by_cases hd : d = 0
    · have hc := card_le_card (filter_subset (fun a => a-d ∈ B a) D)
      have hm : M d ≤ q := mul_le_mul_of_nonneg_right (show ((D.filter fun a => a-d ∈ B a).card : ℝ) ≤ (D.card : ℝ) by exact_mod_cast hc) hθ.le
      simp only [spike,if_pos hd,mul_one]
      linarith
    · simp only [spike,if_neg hd,mul_zero,add_zero]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hBd d hd) hθ.le
  exact profile_bound K M q n hq hn' hKn hMn hKd hMd hKm hMm m
end DetDLP.Energy

namespace DetDLP.Energy
open Finset AffineHash Moment
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {S : Type*} [Fintype S]

private theorem block_bound (F : S → Finset G) (D : Finset G) (B : G → Finset G)
    (θ : ℝ) (hθ : 0 < θ) (hn : 0 < D.card)
    (hB : ∀ a ∈ D, (B a).card ≤ 2)
    (hBd : ∀ d : G, d ≠ 0 → (D.filter fun a => a-d ∈ B a).card ≤ 4)
    (hF : ∀ s, F s ⊆ D)
    (hJ : ∀ a ∈ D, ∀ b ∈ D, (𝔼 s, memWeight (F s) a * memWeight (F s) b) ≤
        θ^2+(if b ∈ B a then θ else 0)) (m : ℕ) :
    let n : ℝ := D.card
    let q := n*θ
    (𝔼 s : Fin m → S, (collisionEnergyAdd (fun i => F (s i)) : ℝ)) ≤
      q^m+(q^m)^2/n*((1+2/q)^m+4*(2/q)^m) := by
  rw [energy_profile]
  refine kernel_bound D B (fun a b => 𝔼 s, memWeight (F s) a * memWeight (F s) b) θ hθ hn hB hBd ?_ ?_ m
  · intro a b
    apply expect_nonneg
    intro s _
    simp only [memWeight]
    split_ifs <;> norm_num
  · intro a b
    by_cases ha : a ∈ D
    · rw [if_pos ha]
      by_cases hb : b ∈ D
      · simpa [hb] using hJ a ha b hb
      · have he (s : S) : memWeight (F s) b = 0 := if_neg (fun h => hb (hF s h))
        simp_rw [he,mul_zero]
        simp [hb]
        split_ifs <;> linarith
    · have he (s : S) : memWeight (F s) a = 0 := if_neg (fun h => ha (hF s h))
      simp [he,ha]

private theorem negative_fibers {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (E : WeierstrassCurve (ZMod p))
    (D : Finset E.toAffine.Point) (d : E.toAffine.Point) (hd : d ≠ 0) :
    (D.filter fun a => a-d ∈ ({a,-a} : Finset _)).card ≤ 4 := by
  letI := ecPointFintype E
  apply le_trans _ (doubling_fiber hp3 E d)
  apply card_le_card
  intro a ha
  obtain h | h := mem_insert.mp (mem_filter.mp ha).2
  · exact False.elim (hd (by apply neg_eq_zero.mp; exact add_left_cancel (show a + (-d) = a + 0 by simpa [sub_eq_add_neg] using h)))
  · have e := mem_singleton.mp h
    exact mem_filter.mpr ⟨mem_univ _,by rw [sub_eq_iff_eq_add] at e; abel_nf at *; grind⟩

private theorem equal_fibers (D : Finset G) (d : G) (hd : d ≠ 0) :
    (D.filter fun a => a-d ∈ ({a} : Finset _)).card ≤ 4 := by
  have h (a : G) : a-d ≠ a := by
    intro e
    apply hd
    apply neg_eq_zero.mp
    exact add_left_cancel (show a + (-d) = a + 0 by simpa [sub_eq_add_neg] using e)
  simp [h]

private theorem mul_energy {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
    (F : Fin m → Finset H) :
    collisionEnergyMul F = collisionEnergyAdd (G := Additive H) F := by
  unfold collisionEnergyMul collisionEnergyAdd
  rw [← (Additive.ofMul : H ≃ Additive H).sum_comp]
  apply sum_congr rfl
  intro g _
  congr 1

end DetDLP.Energy

open DetDLP
open scoped BigOperators
set_option maxHeartbeats 800000 in
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
        (∑ S : ECSeed p m, (collisionEnergyAdd (ecFactorBlock E T S) : ℝ)) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ μ + μ^2 / (n : ℝ) * ((1 + 2/q)^m + 4 * (2/q)^m)) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let q := qBlk p n T
      let μ := q ^ m
      (∑ S : FpSeed p m, (collisionEnergyMul (fpFactorBlock (p := p) T S) : ℝ)) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ μ + μ^2 / (n : ℝ) * ((1 + 2/q)^m + 4 * (2/q)^m)) := by
  constructor
  · intro p m hp hp3 hm E hE g n hg hn T q μ
    letI := ecPointFintype E
    letI : NeZero (p-1) := ⟨by have := hp.out.one_lt; omega⟩
    obtain ⟨hT,hq⟩ := Moment.threshold_valid hp.out.pos hm hn (show g ≤ n+1 by dsimp [n]; omega)
    let D := Finset.univ.erase (0 : E.toAffine.Point)
    let F (s : Bool → AffineHash.Seed p) := ecFactorBlock E T (fun _ : Fin 1 => s) 0
    have hD : D.card = n := by simp [D,n,g]
    have hc : 0 < D.card := by rw [hD]; omega
    have hθ : 0 < (T : ℝ)/p := by
      by_contra! h
      have : (n : ℝ)*((T : ℝ)/p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h
      exact hq.not_ge (by simpa [qBlk,mul_div_assoc] using this)
    have hF (s : Bool → AffineHash.Seed p) : F s ⊆ D := by
      intro a ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact Bool.false_ne_true ((Finset.mem_filter.mp ha).2)
    have hI (a : E.toAffine.Point) (s : Bool → AffineHash.Seed p) :
        Energy.memWeight (F s) a = Moment.curveHit T a s := by
      have hm : a ∈ F s ↔ ecFactorMem T (fun _ : Fin 1 => s) 0 a = true :=
        ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
      simp only [Energy.memWeight,hm]
      cases a <;> simp [ecFactorMem,Moment.curveHit,AffineHash.hit,AffineHash.value_val]
    have hJ (a : E.toAffine.Point) (ha : a ∈ D) (b : E.toAffine.Point) (hb : b ∈ D) :
        (𝔼 s, Energy.memWeight (F s) a * Energy.memWeight (F s) b) ≤
          ((T : ℝ)/p)^2 + (if b ∈ ({a,-a} : Finset _) then (T : ℝ)/p else 0) := by
      simp_rw [hI]
      exact Moment.curveJoint hT a b (Finset.mem_erase.mp ha).1 (Finset.mem_erase.mp hb).1
    have e := Energy.block_bound F D (fun a => {a,-a}) ((T : ℝ)/p) hθ hc
      (fun a _ => Finset.card_le_two) (Energy.negative_fibers hp3 E D) hF hJ m
    have hFam (S : ECSeed p m) : (fun i => F (S i)) = ecFactorBlock E T S := by
      funext i
      ext a
      simp only [F,ecFactorBlock,Finset.mem_filter,Finset.mem_univ,true_and]
      cases a <;> rfl
    dsimp only at e
    simp only [hFam,hD, Fintype.expect_eq_sum_div_card] at e
    simpa only [q,μ,qBlk,mul_div_assoc] using e
  · intro p m hp hm g n hg hn T q μ
    letI : NeZero (p-1) := ⟨by have := hp.out.one_lt; omega⟩
    obtain ⟨hT,hq⟩ := Moment.threshold_valid hp.out.pos hm hn (show g ≤ n+1 by omega)
    let G := Additive (ZMod p)ˣ
    let D := (Finset.univ : Finset G)
    let F (s : AffineHash.Seed p) : Finset G := fpFactorBlock T (fun _ : Fin 1 => s) 0
    have hD : D.card = n := by
      change Fintype.card (Additive (ZMod p)ˣ) = n
      rw [Fintype.card_congr (Additive.toMul : Additive (ZMod p)ˣ ≃ (ZMod p)ˣ),
        ZMod.card_units_eq_totient,Nat.totient_prime hp.out]
    have hc : 0 < D.card := by rw [hD]; omega
    have hθ : 0 < (T : ℝ)/p := by
      by_contra! h
      have : (n : ℝ)*((T : ℝ)/p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h
      exact hq.not_ge (by simpa [qBlk,mul_div_assoc] using this)
    have hI (a : G) (s : AffineHash.Seed p) :
        Energy.memWeight (F s) a = AffineHash.hit T (a.toMul : ZMod p) s := by
      have hm : a ∈ F s ↔ fpFactorMem T (fun _ : Fin 1 => s) 0 a.toMul = true := by
        change a.toMul ∈ fpFactorBlock T (fun _ : Fin 1 => s) 0 ↔ _
        simp only [fpFactorBlock,Finset.mem_filter,Finset.mem_univ,true_and]
      simp [Energy.memWeight,hm,fpFactorMem,AffineHash.hit,AffineHash.value_val]
    have hJ (a : G) (_ : a ∈ D) (b : G) (_ : b ∈ D) :
        (𝔼 s, Energy.memWeight (F s) a * Energy.memWeight (F s) b) ≤
          ((T : ℝ)/p)^2+(if b ∈ ({a} : Finset G) then (T : ℝ)/p else 0) := by
      simp_rw [hI]
      exact Moment.fpJoint hT a.toMul b.toMul
    have e := Energy.block_bound F D (fun a => {a}) ((T : ℝ)/p) hθ hc
      (by simp) (Energy.equal_fibers D) (fun _ => Finset.subset_univ _) hJ m
    have hFam (S : FpSeed p m) : (fun i => F (S i)) = fpFactorBlock T S := rfl
    have henergy (S : FpSeed p m) : collisionEnergyAdd (G := G) (fun i => F (S i)) =
        collisionEnergyMul (fpFactorBlock T S) := (Energy.mul_energy (fpFactorBlock T S)).symm
    dsimp only at e
    simp only [henergy,hD,Fintype.expect_eq_sum_div_card] at e
    simpa only [q,μ,qBlk,mul_div_assoc] using e
