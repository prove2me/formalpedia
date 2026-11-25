-- Prove2me | solution 1 for DetDLP.oriented_dyadic_sample_child_contractions
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T15:20:46.239216+00:00
-- url     : https://prove2.me/submissions/5745fc7a-b92e-44e4-95dd-eb574144a717

import Definitions.Def_DetDLP_OrientedPacketInstance
import Definitions.Def_DetDLP_PacketKernel

namespace DetDLP.DyadicGrid
open Finset
private theorem split_sum (f : ℕ → ℕ) (n : ℕ) :
    ∑ j ∈ range (2*n), f j = ∑ j ∈ range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]; omega

private theorem even_val (n : ℕ) (hn : n ≠ 0) : padicValNat 2 (2*n) = 1+padicValNat 2 n := by
  rw [padicValNat.mul (by decide) hn,padicValNat_self]
private theorem odd_val (n : ℕ) : padicValNat 2 (2*n+1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

def first (k : ℕ) := ∑ n ∈ range (2^k), padicValNat 2 n
def moment (k i : ℕ) := ∑ n ∈ range (2^k), (padicValNat 2 n - i)^2

private theorem first_bound (k : ℕ) : first k ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    change ∑ n ∈ range (2^(k+1)), _ ≤ _
    rw [pow_succ',split_sum]
    calc
      _ ≤ ∑ n ∈ range (2^k), (1+padicValNat 2 n) := by
        apply sum_le_sum; intro n hn; rw [odd_val,add_zero]
        by_cases h : n=0
        · simp [h]
        · exact (even_val n h).le
      _ = 2^k + first k := by simp [Finset.sum_add_distrib,first]
      _ ≤ _ := by omega

private theorem moment_zero (k : ℕ) : moment k 0 ≤ 3*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    change ∑ n ∈ range (2^(k+1)), _ ≤ _
    rw [pow_succ',split_sum]
    calc
      _ ≤ ∑ n ∈ range (2^k), ((padicValNat 2 n)^2+2*padicValNat 2 n+1) := by
        apply sum_le_sum; intro n hn; rw [odd_val]; simp only [Nat.sub_zero,zero_pow (by decide : 2≠0),add_zero]
        by_cases h : n=0
        · simp [h]
        · rw [even_val n h]; nlinarith
      _ = moment k 0 + 2*first k + 2^k := by
        simp [moment,first,Finset.sum_add_distrib,← Finset.mul_sum]
      _ ≤ _ := by have := first_bound k; omega

theorem moment_bound (k i : ℕ) : moment k i ≤ 3*2^(k-i) := by
  induction k generalizing i with
  | zero => simp [moment]
  | succ k ih =>
    cases i with
    | zero => simpa using moment_zero (k+1)
    | succ i =>
      change (∑ n ∈ range (2^(k+1)), _) ≤ _
      rw [pow_succ',split_sum]
      convert ih i using 1
      · unfold moment; apply sum_congr rfl; intro n hn
        by_cases h : n=0
        · simp [h]
        · rw [even_val n h,odd_val]; simp [Nat.add_comm] <;> omega
      · rw [Nat.succ_sub_succ_eq_sub]

abbrev Grid (k : ℕ) := ZMod (2^k)
def level {k : ℕ} (t : Grid k) := padicValNat 2 t.val

private theorem dvd_equiv {a b : ℤ} {k j : ℕ} (hj : j ≤ k) (h : (2:ℤ)^k ∣ b-a) :
    (2:ℤ)^j ∣ a ↔ (2:ℤ)^j ∣ b := by
  have hd := (pow_dvd_pow (2:ℤ) hj).trans h
  constructor
  · intro ha; simpa using dvd_add hd ha
  · intro hb; simpa using dvd_sub hb hd

theorem val_rep {k : ℕ} {z : ℤ} {x : Grid k} (hx : x ≠ 0) (hc : (z : Grid k) = x) :
    padicValInt 2 z = level x := by
  let b : ℤ := x.val
  have hcast : (b : Grid k) = x := by simp [b]
  have hk : (2:ℤ)^k ∣ b-z := by
    simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub z b (2^k)).mp (hc.trans hcast.symm)
  have hn : z ≠ 0 := by intro h; simp [h] at hc; exact hx hc.symm
  have hb : b ≠ 0 := by intro h; simp [h] at hcast; exact hx hcast.symm
  have hnk : ¬(2:ℤ)^k ∣ z := by
    intro h; apply hx; rw [← hc,ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using h
  have hbk : ¬(2:ℤ)^k ∣ b := by
    intro h; exact hnk ((dvd_equiv (le_refl k) hk).mpr h)
  have hv (y : ℤ) (hy : y ≠ 0) (h : ¬(2:ℤ)^k ∣ y) : padicValInt 2 y < k := by
    rw [show (2:ℤ)^k ∣ y ↔ y=0 ∨ k ≤ padicValInt 2 y from padicValInt_dvd_iff (p:=2) k y,or_iff_right hy] at h; omega
  have hxy : padicValInt 2 z = padicValInt 2 b := by
    apply le_antisymm
    · exact ((padicValInt_dvd_iff _ b).mp ((dvd_equiv (hv z hn hnk).le hk).mp (padicValInt_dvd z))).resolve_left hb
    · exact ((padicValInt_dvd_iff _ z).mp ((dvd_equiv (hv b hb hbk).le hk).mpr (padicValInt_dvd b))).resolve_left hn
  exact hxy

theorem level_sub {k : ℕ} {t q : Grid k} (ht : t ≠ 0) (hq : q ≠ 0) (hd : t ≠ q)
    (hne : level t ≠ level q) : level (t-q) = min (level t) (level q) := by
  let a : ℤ := t.val
  let b : ℤ := q.val
  have ea : (a : Grid k) = t := by simp [a]
  have eb : (b : Grid k) = q := by simp [b]
  have ed : ((a-b : ℤ) : Grid k) = t-q := by simp [ea,eb]
  have hd' := sub_ne_zero.mpr hd
  have ha : (a:ℚ) ≠ 0 := by exact_mod_cast (fun h => ht (ea.symm.trans (by simp [h])) : a ≠ 0)
  have hb : (b:ℚ) ≠ 0 := by exact_mod_cast (fun h => hq (eb.symm.trans (by simp [h])) : b ≠ 0)
  have hd'' : (a:ℚ)+ -(b:ℚ) ≠ 0 := by
    rw [← sub_eq_add_neg,← Int.cast_sub]; exact_mod_cast (fun h => hd' (ed.symm.trans (by simp [h])) : a-b ≠ 0)
  have va : padicValRat 2 (a:ℚ) = (level t:ℤ) := by simp [val_rep ht ea]
  have vb : padicValRat 2 (-(b:ℚ)) = (level q:ℤ) := by rw [padicValRat.neg]; simp [val_rep hq eb]
  have h := padicValRat.add_eq_min hd'' ha (neg_ne_zero.mpr hb) (by rw [va,vb]; exact_mod_cast hne)
  rw [← sub_eq_add_neg,← Int.cast_sub,padicValRat.of_int,val_rep hd' ed,va,vb] at h
  exact_mod_cast h

end DetDLP.DyadicGrid


namespace DetDLP.DyadicGrid
open Finset

private theorem gridMoment (k i : ℕ) :
    (∑ x : Grid k, (level x-i)^2) ≤ 3*2^(k-i) := by
  have h (N : ℕ) [NeZero N] :
      (∑ x : ZMod N, (padicValNat 2 x.val-i)^2) =
      ∑ n ∈ range N, (padicValNat 2 n-i)^2 := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ N =>
      change (∑ x : Fin (N+1), (padicValNat 2 x.val-i)^2) = _
      rw [Fin.sum_univ_eq_sum_range (fun n => (padicValNat 2 n-i)^2)]
  simpa only [level,h,moment] using (moment_bound k i : moment k i ≤ _)

def nodes {k : ℕ} (t : Grid k) : Finset (Grid k) := (univ.erase 0).erase t
def mult (h u i : ℕ) := h*(u-i)

/-- Rational Hermite cardinal multiplier at the origin, allowing any choice of
integer representatives of the complete residue grid that sends zero to zero. -/
def atOrigin {k : ℕ} (r : Grid k → ℤ) (t : Grid k) (h u : ℕ) : ℚ :=
  ∏ x ∈ nodes t, ((-(r x : ℚ))/((r t:ℚ)-(r x:ℚ)))^(mult h u (level x))

private theorem mem_nodes {k : ℕ} (x t : Grid k) : x ∈ nodes t ↔ x ≠ t ∧ x ≠ 0 := by simp [nodes]

private theorem reflect_sum {k : ℕ} (t : Grid k) :
    (∑ x ∈ nodes t, (level x:ℤ)) = ∑ x ∈ nodes t, (level (t-x):ℤ) := by
  apply sum_bij' (fun x _ => t-x) (fun x _ => t-x)
  · intro x hx; obtain ⟨ht,hz⟩ := (mem_nodes x t).mp hx
    apply (mem_nodes _ _).mpr; exact ⟨by simpa using hz,sub_ne_zero.mpr ht.symm⟩
  · intro x hx; obtain ⟨ht,hz⟩ := (mem_nodes x t).mp hx
    apply (mem_nodes _ _).mpr; exact ⟨by simpa using hz,sub_ne_zero.mpr ht.symm⟩
  · intro x hx; simp
  · intro x hx; simp
  · intro x hx; simp

private theorem local_loss {k : ℕ} {t x : Grid k} (ht : t ≠ 0) (hx : x ∈ nodes t) (h u : ℕ) :
    -((h:ℤ)*((level x-level t:ℕ):ℤ)^2) ≤
    ((mult h u (level x):ℤ)-(mult h u (level t):ℤ))*
        ((level x:ℤ)-(level (t-x):ℤ)) := by
  obtain ⟨hd,hz⟩ := (mem_nodes _ _).mp hx
  rcases lt_trichotomy (level x) (level t) with hlt|he|hgt
  · rw [level_sub ht hz hd.symm (ne_of_gt hlt),min_eq_right hlt.le,Nat.sub_eq_zero_of_le hlt.le]; simp
  · simp [he]
  · rw [level_sub ht hz hd.symm (ne_of_lt hgt),min_eq_left hgt.le]
    have hc : ((u-level t : ℕ):ℤ)-((u-level x : ℕ):ℤ) ≤ (level x:ℤ)-(level t:ℤ) := by omega
    have hd' : 0 ≤ (level x:ℤ)-(level t:ℤ) := by omega
    have hh := mul_le_mul_of_nonneg_left hc (Int.natCast_nonneg h)
    have hl := mul_le_mul_of_nonneg_right hh hd'
    simp only [mult,Nat.cast_mul,Nat.cast_sub hgt.le]
    nlinarith only [hl]

theorem val_prod {α : Type*} (s : Finset α) (f : α → ℚ) (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValRat 2 (∏ x ∈ s, f x) = ∑ x ∈ s, padicValRat 2 (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h := hf a (mem_insert_self ..)
    have hh : ∀ x ∈ s, f x ≠ 0 := fun x hx => hf x (mem_insert_of_mem hx)
    rw [prod_insert ha,sum_insert ha,padicValRat.mul h (Finset.prod_ne_zero_iff.mpr hh),ih hh]

theorem origin_bound {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x : ℤ):Grid k)=x)
    {t : Grid k} (ht : t ≠ 0) (h u : ℕ) :
    -(3*(2:ℤ)^(k-level t)*h) ≤ padicValRat 2 (atOrigin r t h u) := by
  have hv (x : Grid k) (hx : x ∈ nodes t) :
      let f := (-(r x : ℚ))/((r t:ℚ)-(r x:ℚ))
      f ≠ 0 ∧ padicValRat 2 f = (level x:ℤ)-(level (t-x):ℤ) := by
    obtain ⟨hxt,hx0⟩ := (mem_nodes x t).mp hx
    have h0 : r x ≠ 0 := fun e => hx0 ((hr x).symm.trans (by simp [e]))
    have he : (((r t-r x:ℤ):Grid k)) = t-x := by simp [hr]
    have h1 : r t-r x ≠ 0 := fun e => sub_ne_zero.mpr hxt.symm (he.symm.trans (by simp [e]))
    have z0 : (r x:ℚ) ≠ 0 := by exact_mod_cast h0
    have z1 : (r t:ℚ)-(r x:ℚ) ≠ 0 := by exact_mod_cast h1
    refine ⟨div_ne_zero (neg_ne_zero.mpr z0) z1,?_⟩
    rw [padicValRat.div (neg_ne_zero.mpr z0) z1,padicValRat.neg,← Int.cast_sub,
      padicValRat.of_int,padicValRat.of_int,val_rep hx0 (hr x),val_rep (sub_ne_zero.mpr hxt.symm) he]
  rw [atOrigin,val_prod _ _ (fun x hx => pow_ne_zero _ (hv x hx).1)]
  simp_rw [padicValRat.pow]
  have ez : (∑ x ∈ nodes t, ((level x:ℤ)-(level (t-x):ℤ))) = 0 := by
    rw [sum_sub_distrib,reflect_sum t,sub_self]
  have em : (∑ x ∈ nodes t, ((mult h u (level x):ℤ)-(mult h u (level t):ℤ))*
      ((level x:ℤ)-(level (t-x):ℤ))) = ∑ x ∈ nodes t, (mult h u (level x):ℤ)*((level x:ℤ)-(level (t-x):ℤ)) := by
    simp_rw [sub_mul]; rw [sum_sub_distrib,← mul_sum,ez,mul_zero,sub_zero]
  have hm : (∑ x ∈ nodes t, (level x-level t)^2) ≤ 3*2^(k-level t) :=
    (Finset.sum_le_sum_of_subset (subset_univ _)).trans (gridMoment k (level t))
  have hmi : (∑ x ∈ nodes t, ((level x-level t:ℕ):ℤ)^2) ≤ 3*(2:ℤ)^(k-level t) := by exact_mod_cast hm
  calc
    _ ≤ -((h:ℤ)*∑ x ∈ nodes t, ((level x-level t:ℕ):ℤ)^2) := by
      have hh := mul_le_mul_of_nonneg_left hmi (Int.natCast_nonneg h); linarith
    _ = ∑ x ∈ nodes t, -((h:ℤ)*((level x-level t:ℕ):ℤ)^2) := by rw [mul_sum,sum_neg_distrib]
    _ ≤ _ := by
      apply (sum_le_sum (fun x hx => local_loss ht hx h u)).trans
      rw [em]
      apply le_of_eq; apply sum_congr rfl; intro x hx; rw [(hv x hx).2]
end DetDLP.DyadicGrid


namespace DetDLP.DyadicGrid
open Finset Polynomial
/-- Divisibility by a power of two in the local ring at two, allowing rational inputs. -/
def Prec (p : ℤ) (x : ℚ) : Prop := x=0 ∨ p ≤ padicValRat 2 x

namespace Prec
theorem mono {p q : ℤ} {x : ℚ} (hp : p ≤ q) (hx : Prec q x) : Prec p x :=
  hx.imp id (hp.trans ·)
theorem add {p : ℤ} {x y : ℚ} (hx : Prec p x) (hy : Prec p y) : Prec p (x+y) := by
  rcases hx with rfl|h
  · simpa using hy
  rcases hy with rfl|h'
  · simp [Prec,h]
  by_cases hz : x+y=0
  · exact Or.inl hz
  · exact Or.inr ((le_min h h').trans (padicValRat.min_le_padicValRat_add hz))
theorem neg {p : ℤ} {x : ℚ} (hx : Prec p x) : Prec p (-x) := by simpa [Prec,padicValRat.neg] using hx
theorem mul {p q : ℤ} {x y : ℚ} (hx : Prec p x) (hy : Prec q y) : Prec (p+q) (x*y) := by
  by_cases h : x=0
  · simp [h,Prec]
  by_cases h' : y=0
  · simp [h',Prec]
  exact Or.inr (by rw [padicValRat.mul h h']; exact add_le_add (hx.resolve_left h) (hy.resolve_left h'))
theorem pow {p : ℤ} {x : ℚ} (hx : Prec p x) (n : ℕ) : Prec ((n:ℤ)*p) (x^n) := by
  induction n with
  | zero => simp [Prec]
  | succ n ih => simpa [pow_succ,add_mul] using ih.mul hx
theorem sum {α : Type*} (s : Finset α) (f : α → ℚ) (p : ℤ) (hf : ∀ i ∈ s, Prec p (f i)) :
    Prec p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Prec]
  | insert a s ha ih =>
    rw [sum_insert ha]; exact (hf _ (mem_insert_self ..)).add (ih (fun x hx => hf x (mem_insert_of_mem hx)))
end Prec

def integral (F : ℚ[X]) := ∀ j, Prec 0 (F.coeff j)

theorem integral_add {F G : ℚ[X]} (hF : integral F) (hG : integral G) : integral (F+G) := by
  intro j; rw [coeff_add]; exact (hF j).add (hG j)
theorem integral_mul {F G : ℚ[X]} (hF : integral F) (hG : integral G) : integral (F*G) := by
  intro j; rw [coeff_mul]; apply Prec.sum; intro i hi; simpa using (hF i.1).mul (hG i.2)
theorem integral_one : integral 1 := by intro j; by_cases h : j=0 <;> simp [coeff_one,h,Prec]
theorem integral_pow {F : ℚ[X]} (hf : integral F) (n : ℕ) : integral (F^n) := by
  induction n with
  | zero => simpa using integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hf
theorem integral_prod {α : Type*} (s : Finset α) (f : α → ℚ[X]) (hf : ∀ x ∈ s, integral (f x)) :
    integral (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using integral_one
  | insert a s ha ih => rw [prod_insert ha]; exact integral_mul (hf _ (mem_insert_self ..)) (ih fun x hx => hf x (mem_insert_of_mem hx))

theorem level_lt {k : ℕ} {x : Grid k} (hx : x≠0) : level x < k := by
  by_contra! h
  have hl : (2:ℤ)^k ∣ (x.val:ℤ) := (padicValInt_dvd_iff (p:=2) k (x.val:ℤ)).mpr (Or.inr h)
  apply hx; rw [← ZMod.natCast_zmod_val x,← Int.cast_natCast,ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa only [Nat.cast_pow,Nat.cast_ofNat] using hl

noncomputable def coord {k : ℕ} (r : Grid k → ℤ) (t : Grid k) : ℚ[X] := C (r t:ℚ) + C ((2:ℚ)^k)*X
end DetDLP.DyadicGrid


namespace DetDLP.DyadicGrid
open Finset Polynomial DeformedContraction

private theorem val_derivatives {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x) (t : Grid k) :
    let R (x : Grid k) : ℚ := r x
    let D (x : Grid k) := ∏ j ∈ univ.erase x, (R x-R j)
    D t ≠ 0 ∧ padicValRat 2 (D t) = ∑ j ∈ univ.erase (0:Grid k), (level j:ℤ) := by
  intro R D
  have hx (j : Grid k) (hj : j ∈ univ.erase t) :
      R t-R j ≠ 0 ∧ padicValRat 2 (R t-R j) = (level (t-j):ℤ) := by
    have hne : t-j ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hj).symm
    have he : ((r t-r j:ℤ):Grid k) = t-j := by simp [hr]
    have hz : r t-r j ≠ 0 := fun h => hne (he.symm.trans (by simp [h]))
    refine ⟨by dsimp [R]; exact_mod_cast hz,?_⟩
    dsimp only [R]; rw [← Int.cast_sub,padicValRat.of_int,val_rep hne he]
  refine ⟨prod_ne_zero_iff.mpr (fun j hj => (hx j hj).1),?_⟩
  change padicValRat 2 (∏ j ∈ univ.erase t, (R t-R j)) = _
  rw [val_prod _ _ (fun j hj => (hx j hj).1)]
  calc
    _ = ∑ j ∈ univ.erase t, (level (t-j):ℤ) := sum_congr rfl (fun j hj => (hx j hj).2)
    _ = _ := by
      apply sum_bij' (fun j _ => t-j) (fun j _ => t-j)
      · intro j hj; simp [sub_ne_zero.mpr (ne_of_mem_erase hj).symm]
      · intro j hj; have h := ne_of_mem_erase hj; simpa using h
      · intro j hj; simp
      · intro j hj; simp
      · intro j hj; rfl

private theorem coeff_integral_C (c : ℚ) (hc : Prec 0 c) : integral (C c) := by
  intro j; by_cases h : j=0
  · simpa [h] using hc
  · simp [coeff_C,h,Ne.symm h,Prec]
private theorem coeff_integral_X : integral (X:ℚ[X]) := by
  intro j; by_cases h : j=1 <;> simp [coeff_X,h,eq_comm,Prec]

private theorem normalized_linear {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x)
    {t j : Grid k} (hne : t≠j) :
    let d := (r t:ℚ)-(r j:ℚ)
    let c := (2:ℚ)^k/d
    Prec ((k:ℤ)-level (t-j)) c ∧ integral (1+C c*X) := by
  intro d c
  have he : ((r t-r j:ℤ):Grid k)=t-j := by simp [hr]
  have hg := sub_ne_zero.mpr hne
  have hq : d≠0 := by dsimp [d]; exact_mod_cast (fun h => hg (he.symm.trans (by simp [h])) : r t-r j≠0)
  have h : Prec ((k:ℤ)-level (t-j)) c := by
    right; dsimp [c,d]
    rw [padicValRat.div (by positivity) (show (r t:ℚ)-(r j:ℚ) ≠ 0 from hq),padicValRat.pow,show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide : 1 < 2),
      ←Int.cast_sub,padicValRat.of_int,val_rep hg he,mul_one]
  have hl := level_lt hg
  exact ⟨h,integral_add integral_one (integral_mul (coeff_integral_C _ (h.mono (by omega))) coeff_integral_X)⟩

noncomputable def rawKernel {k : ℕ} (r : Grid k → ℤ) (d : Grid k) : ℚ[X] :=
  C ((∏ x ∈ univ.erase (0:Grid k), -(r x:ℚ))⁻¹) * ∏ x ∈ univ.erase d, (X-C (r x:ℚ))

/-- Every coefficient is 2-integral in the local coordinate. At a nontarget node
the extra factor of alpha gives k-v(t-d) more bits on every coefficient. -/
theorem local_kernel {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x)
    (h0 : r 0=0) (d t : Grid k) :
    let Q : ℚ[X] := C (r t:ℚ) + C ((2:ℚ)^k)*X
    ∀ i, Prec (if d=t then 0 else (k:ℤ)-level (t-d)) (((rawKernel r d).comp Q).coeff i) := by
  intro Q
  let R (x : Grid k) : ℚ := r x
  let D (x : Grid k) := ∏ j ∈ univ.erase x, (R x-R j)
  let lin (x : Grid k) : ℚ[X] := 1+C ((2:ℚ)^k/(R t-R x))*X
  let H (s : Finset (Grid k)) := ∏ j ∈ s,lin j
  have hD := val_derivatives r hr t
  have hZ := val_derivatives r hr 0
  have hrat : Prec 0 ((D 0)⁻¹*(D t)) := by
    right; rw [padicValRat.mul (inv_ne_zero hZ.1) hD.1,padicValRat.inv,hD.2,hZ.2]; simp
  have hden : D 0 = ∏ j ∈ univ.erase (0:Grid k), -(r j:ℚ) := by simp [D,R,h0]
  have hn (j : Grid k) (hj : j≠t) : R t-R j ≠ 0 := by
    apply sub_ne_zero.mpr; intro eqn
    have hh : r t = r j := by dsimp [R] at eqn; exact_mod_cast eqn
    exact hj (by rw [←hr j,←hr t,hh])
  have hlocal (s : Finset (Grid k)) (hs : ∀ j ∈ s,j≠t) : integral (H s) :=
    integral_prod s _ (fun j hj => (normalized_linear r hr (hs j hj).symm).2)
  have hs (s : Finset (Grid k)) (hs : ∀ j ∈ s,j≠t) :
      (∏ j ∈ s, (Q-C (R j))) = C (∏ j ∈ s,(R t-R j)) * H s := by
    rw [map_prod]; dsimp only [H]; rw [←prod_mul_distrib]; apply prod_congr rfl; intro j hj
    change C (R t)+C ((2:ℚ)^k)*X-C (R j) = C (R t-R j) * (1+C ((2:ℚ)^k/(R t-R j))*X)
    have he : C (R t-R j)*C ((2:ℚ)^k/(R t-R j)) = (C ((2:ℚ)^k):ℚ[X]) := by rw [←map_mul];congr 1; field_simp [hn j (hs j hj)]
    rw [mul_add,mul_one,← mul_assoc,he,map_sub]; ring
  have hraw : (rawKernel r d).comp Q = C ((D 0)⁻¹) * ∏ j ∈ univ.erase d, (Q-C (R j)) := by
    simp only [rawKernel,mul_comp,C_comp,Polynomial.prod_comp,sub_comp,X_comp,hden,R]
  rw [hraw]
  by_cases he : d=t
  · subst d; simp only [if_pos rfl]
    rw [hs _ (fun _ h => ne_of_mem_erase h),← mul_assoc,←map_mul]
    exact integral_mul (coeff_integral_C _ hrat) (hlocal _ (fun _ h => ne_of_mem_erase h))
  · simp only [if_neg he]
    let s := (univ.erase t).erase d
    have hdt : d ∈ univ.erase t := by simp [he]
    have htd : t ∈ univ.erase d := by simp [Ne.symm he]
    have hfin : (univ.erase d).erase t = s := by ext j; simp [s,and_comm]
    have hd' : (∏ j ∈ s,(R t-R j)) = (D t)/(R t-R d) := by
      apply (eq_div_iff (hn d he)).mpr
      exact prod_erase_mul _ _ hdt
    rw [← mul_prod_erase _ _ htd,hfin,hs _ (fun _ hj => ne_of_mem_erase (mem_of_mem_erase hj)),hd']
    have hself : Q-C (R t) = C ((2:ℚ)^k)*X := by dsimp only [Q,R]; ring
    rw [hself]
    let c := (2:ℚ)^k/(R t-R d)
    have eqn : C ((D 0)⁻¹) * (C ((2:ℚ)^k)*X*(C (D t/(R t-R d))*H s)) =
      C c*(C ((D 0)⁻¹*D t)*(X*H s)) := by dsimp only [c]; simp only [div_eq_mul_inv,map_mul]; ring
    rw [eqn]
    have hh := integral_mul (coeff_integral_C _ hrat) (integral_mul coeff_integral_X (hlocal s (fun _ hj => ne_of_mem_erase (mem_of_mem_erase hj))))
    intro i; rw [coeff_C_mul]
    simpa using (normalized_linear r hr (Ne.symm he)).1.mul (hh i)
end DetDLP.DyadicGrid


namespace DetDLP.DyadicGrid
open Finset Polynomial DeformedContraction
noncomputable def repEmbedding {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x) : Grid k ↪ ℚ where
  toFun x := r x
  inj' := by
    intro a b hh
    change (r a : ℚ) = (r b : ℚ) at hh
    have h : r a = r b := by exact_mod_cast hh
    rw [← hr a, ← hr b, h]

theorem raw_matches {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x) (h0 : r 0=0) (d : Grid k) :
    shiftKernel (univ.map (repEmbedding r hr)) (r d:ℚ) = rawKernel r d := by
  let e := repEmbedding r hr
  have hzero : e 0=0 := by change (r 0:ℚ) = 0; simp [h0]
  change C ((∏ x ∈ (univ.map e).erase 0, -x)⁻¹) *
    (∏ x ∈ (univ.map e).erase (e d), (X-C x)) = _
  have hzerase : (univ.map e).erase 0 = (univ.erase 0).map e := by
    rw [Finset.map_erase, hzero]
  rw [hzerase, ← Finset.map_erase e univ d]
  simp only [Finset.prod_map]
  rfl

theorem scale_precision {k : ℕ} {t d : Grid k} (hne : d≠t) :
    1 ≤ (k:ℤ)-level (t-d) := by have hh := level_lt (sub_ne_zero.mpr (Ne.symm hne)); omega

end DetDLP.DyadicGrid


namespace DetDLP.DyadicGrid
open Finset Polynomial DeformedContraction

def localRing : Subring ℚ where
  carrier := {x | Prec 0 x}
  zero_mem' := Or.inl rfl
  one_mem' := by simp [Prec]
  add_mem' := Prec.add
  neg_mem' := Prec.neg
  mul_mem' := by intro x y hx hy; simpa using (Prec.mul (p:=0) (q:=0) hx hy)

noncomputable def liftPoly (P : ℚ[X]) (hP : integral P) : localRing[X] :=
  P.toSubring localRing fun _ hx => by
    obtain ⟨n,_,rfl⟩ := mem_coeffs_iff.mp hx; exact hP n

@[simp] theorem map_liftPoly (P : ℚ[X]) (hP : integral P) :
    (liftPoly P hP).map localRing.subtype = P := Polynomial.map_toSubring ..

noncomputable def atNode {k} (r : Grid k → ℤ) (t d : Grid k) :=
  (rawKernel r d).comp (coord r t)

private theorem atNode_integral {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (h0 : r 0=0) (t d : Grid k) : integral (atNode r t d) := by
  intro j
  have hh := local_kernel r hr h0 d t j
  apply hh.mono
  split <;> first | omega | have := scale_precision (d:=d) (t:=t) (by assumption); omega

noncomputable def residueKernel {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (h0 : r 0=0) (t d : Grid k) :=
  liftPoly (atNode r t d) (atNode_integral r hr h0 t d)

private theorem half_integral {x : ℚ} (h : Prec 1 x) : Prec 0 (2⁻¹*x) := by
  have h2 : Prec (-1) ((2:ℚ)⁻¹) := by right; rw [padicValRat.inv,show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide : 1<2)]
  simpa using h2.mul h

private theorem kernel_even {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (h0 : r 0=0) (t d : Grid k) (hd : d≠t) :
    ∃ Q : localRing[X], residueKernel r hr h0 t d = 2*Q := by
  let P := atNode r t d
  have hi : integral (C (2:ℚ)⁻¹*P) := by
    intro j
    rw [coeff_C_mul]
    have hh := local_kernel r hr h0 d t j
    rw [if_neg hd] at hh
    exact half_integral (hh.mono (scale_precision hd))
  refine ⟨liftPoly _ hi,?_⟩
  apply Polynomial.map_injective localRing.subtype Subtype.val_injective
  simp only [residueKernel,map_liftPoly,Polynomial.map_mul,Polynomial.map_ofNat]
  change P = C 2 * (C (2:ℚ)⁻¹*P)
  rw [← mul_assoc,← map_mul]; norm_num

private theorem same_numerator {k} (r : Grid k → ℤ) (t d : Grid k) (z : ℚ) :
    let T := (r t:ℚ)+(2:ℚ)^k*z
    (T-(r d:ℚ))*((atNode r t d).eval z) =
      (∏ x ∈ univ.erase (0:Grid k), -(r x:ℚ))⁻¹ * (∏ x : Grid k, (T-(r x:ℚ))) := by
  intro T
  simp only [atNode,rawKernel,coord,eval_comp,eval_mul,eval_add,eval_C,eval_X,eval_prod,eval_sub]
  rw [← Finset.mul_prod_erase univ (fun x : Grid k => T-(r x:ℚ)) (mem_univ d)]
  dsimp [T]; ring

/-- The ratio between consecutive tile poles after normalizing the denominator
by the difference between the base node and its pole. Both coefficients have
an explicit factor of two in the local ring. -/
private theorem ratios {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (t d₀ : Grid k) (hd : d₀≠t) (i : ℕ) (hi : level (t-d₀) ≤ i) :
    let D := (r t:ℚ)-(r d₀:ℚ)
    ∃ A B : localRing, D*(2*(A:ℚ))=(2:ℚ)^k ∧ D*(2*(B:ℚ))=(2:ℚ)^(i+1) := by
  intro D
  have hne := sub_ne_zero.mpr (Ne.symm hd)
  have he : ((r t-r d₀:ℤ):Grid k)=t-d₀ := by simp [hr]
  have hd' : D≠0 := by dsimp [D]; exact_mod_cast (fun h => hne (he.symm.trans (by simp [h])) : r t-r d₀≠0)
  have hval : padicValRat 2 D = (level (t-d₀):ℤ) := by
    dsimp [D]; rw [←Int.cast_sub,padicValRat.of_int,val_rep hne he]
  have hk := level_lt hne
  have hq (j : ℕ) (hj : level (t-d₀) ≤ j) : Prec 0 ((2:ℚ)^j/D) := by
    right; rw [padicValRat.div (by positivity) hd',padicValRat.pow,show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide : 1<2),hval,mul_one]; omega
  refine ⟨⟨(2:ℚ)^(k-1)/D,hq _ (by omega)⟩,⟨(2:ℚ)^i/D,hq _ hi⟩,?_,?_⟩
  · change D*(2*(2^(k-1)/D))=(2:ℚ)^k
    conv_rhs => rw [show k=k-1+1 by omega,pow_succ]
    field_simp
  · change D*(2*(2^i/D))=(2:ℚ)^(i+1)
    rw [pow_succ]; field_simp

private theorem tile_identity {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (h0 : r 0=0) (t d₀ d : Grid k) (hd : d₀≠t) (i j : ℕ) (A B : localRing)
    (ha : ((r t:ℚ)-(r d₀:ℚ))*(2*(A:ℚ))=(2:ℚ)^k)
    (hb : ((r t:ℚ)-(r d₀:ℚ))*(2*(B:ℚ))=(2:ℚ)^(i+1))
    (shift : r d-r d₀=(2:ℤ)^(i+1)*(j:ℤ)) :
    (1+C (2*A)*X-C (2*B*(j:localRing)))*residueKernel r hr h0 t d =
      (1+C (2*A)*X)*residueKernel r hr h0 t d₀ := by
  have he : ((r t-r d₀:ℤ):Grid k)=t-d₀ := by simp [hr]
  have hne : (r t:ℚ)-(r d₀:ℚ)≠0 := by
    exact_mod_cast (fun h => (sub_ne_zero.mpr hd.symm) (he.symm.trans (by simp [h])) : r t-r d₀≠0)
  have hs : (r d:ℚ)-(r d₀:ℚ)=(2:ℚ)^(i+1)*(j:ℚ) := by exact_mod_cast shift
  apply Polynomial.map_injective localRing.subtype Subtype.val_injective
  apply Polynomial.funext; intro z
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_one,
    Polynomial.map_C,Polynomial.map_X,residueKernel,map_liftPoly,eval_mul,eval_sub,eval_add,eval_one,eval_C,eval_X,
    map_mul,map_ofNat,map_natCast,Subring.subtype_apply,Polynomial.map_ofNat,Polynomial.map_natCast,eval_ofNat,eval_natCast]
  have eq := (same_numerator r t d z).trans (same_numerator r t d₀ z).symm
  apply mul_left_cancel₀ hne
  linear_combination eq + (z*(atNode r t d).eval z-z*(atNode r t d₀).eval z)*ha -
    ((j:ℚ)*(atNode r t d).eval z)*hb + ((atNode r t d).eval z)*hs

/-- A single family of weighted coefficients works for all columns of this tile
and every evaluation point in any finite-precision coefficient algebra. -/
theorem residue_tile {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (h0 : r 0=0) (t d₀ : Grid k) (hd₀ : d₀≠t) (i : ℕ) (hi : level (t-d₀) ≤ i)
    {R : Type*} [CommRing R] (φ : localRing →+* R) (p : ℕ) (hp : 0<p) (hz : (2:R)^p=0) (z : R) :
    let W (d : Grid k) := (residueKernel r hr h0 t d).eval₂ φ z
    ∃ u v : R, ∀ (d : Grid k) (j : ℕ), d≠t → r d-r d₀=(2:ℤ)^(i+1)*(j:ℤ) →
      W d = ∑ b ∈ range (p-1), (2:R)^(b+1)*(u*v^b)*(j:R)^b := by
  intro W
  obtain ⟨A,B,ha,hb⟩ := ratios r hr t d₀ hd₀ i hi
  obtain ⟨Q,hQ⟩ := kernel_even r hr h0 t d₀ hd₀
  let V := 1 + (2:R)*φ A*z
  have hnil : IsNilpotent ((2:R)*φ A*z) := ⟨p,by rw [mul_pow,mul_pow,hz]; simp⟩
  obtain ⟨e,he⟩ : IsUnit V := hnil.isUnit_one_add
  let v := φ B * (↑e⁻¹:R)
  let u := Q.eval₂ φ z
  have hW₀ : W d₀ = 2*u := by simp [W,hQ,u]
  have hv : V*v=φ B := by dsimp only [v]; rw [←he]; simp [mul_comm,mul_left_comm]
  refine ⟨u,v,?_⟩
  intro d j hd hshift
  have hx := congrArg (Polynomial.eval₂ φ z) (tile_identity r hr h0 t d₀ d hd₀ i j A B ha hb hshift)
  change (eval₂ φ z _) = (eval₂ φ z _) at hx
  simp only [eval₂_mul,eval₂_sub,eval₂_add,eval₂_one,eval₂_C,eval₂_X,map_mul,map_ofNat,map_natCast,eval₂_ofNat,eval₂_natCast] at hx
  change (V-2*φ B*(j:R))*W d = V*W d₀ at hx
  let q := (2:R)*v*(j:R)
  have heq : W d*(1-q)=W d₀ := by
    apply (show IsUnit V from ⟨e,he⟩).mul_right_inj.mp
    dsimp [q]; linear_combination hx - (2*(j:R)*W d)*hv
  have hsum (n : ℕ) : W d - ∑ b ∈ range n, (2:R)^(b+1)*(u*v^b)*(j:R)^b = W d*q^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,←sub_sub,ih,pow_succ q]
      have hterm : (2:R)^(n+1)*(u*v^n)*(j:R)^n = W d₀*q^n := by rw [hW₀]; simp only [q,mul_pow,pow_succ]; ring
      rw [hterm,←heq]; ring
  have hW : ∃ a : R,W d=2*a := by
    obtain ⟨P,hP⟩ := kernel_even r hr h0 t d hd
    exact ⟨P.eval₂ φ z,by simp [W,hP]⟩
  obtain ⟨a,ea⟩ := hW
  apply sub_eq_zero.mp
  rw [hsum,ea]; dsimp [q]; simp only [mul_pow]
  calc
    (2*a)*(2^(p-1)*v^(p-1)*(j:R)^(p-1)) =
        (2:R)^(p-1+1)*(a*v^(p-1)*(j:R)^(p-1)) := by rw [pow_succ]; ring
    _ = 0 := by rw [show p-1+1=p by omega,hz,zero_mul]

noncomputable def toPadic : localRing →+* ℤ_[2] where
  toFun x := ⟨((x:ℚ):ℚ_[2]),by
    rw [Padic.eq_padicNorm]
    have h : padicNorm 2 (x:ℚ) ≤ 1 := by
      rcases x.property with h|h
      · simp [h]
      · unfold padicNorm
        split
        · norm_num
        · exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    exact_mod_cast h⟩
  map_zero' := by apply Subtype.ext; change ((0:ℚ):ℚ_[2])=0; simp
  map_one' := by apply Subtype.ext; change ((1:ℚ):ℚ_[2])=1; simp
  map_add' x y := by apply Subtype.ext; change (((x:ℚ)+(y:ℚ):ℚ):ℚ_[2])=_; push_cast; rfl
  map_mul' x y := by apply Subtype.ext; change (((x:ℚ)*(y:ℚ):ℚ):ℚ_[2])=_; push_cast; rfl

noncomputable def reduceAt (p : ℕ) : localRing →+* ZMod (2^p) :=
  (PadicInt.toZModPow p).comp toPadic

theorem extension_tile {k} (r : Grid k → ℤ) (hr : ∀ s, ((r s:ℤ):Grid k)=s)
    (h0 : r 0=0) (t d₀ : Grid k) (hd₀ : d₀≠t) (i : ℕ) (hi : level (t-d₀) ≤ i)
    (p : ℕ) (hp : 0<p) {R : Type*} [CommRing R] [Algebra (ZMod (2^p)) R] (z : R) :
    let φ := (algebraMap (ZMod (2^p)) R).comp (reduceAt p)
    let W (d : Grid k) := (residueKernel r hr h0 t d).eval₂ φ z
    ∃ u v : R, ∀ (d : Grid k) (j : ℕ), d≠t → r d-r d₀=(2:ℤ)^(i+1)*(j:ℤ) →
      W d = ∑ b ∈ range (p-1), (2:R)^(b+1)*(u*v^b)*(j:R)^b := by
  apply residue_tile r hr h0 t d₀ hd₀ i hi _ p hp
  have h : (2:ZMod (2^p))^p=0 := by exact_mod_cast ZMod.natCast_self (2^p)
  simpa only [map_pow,map_ofNat,map_zero] using congrArg (algebraMap (ZMod (2^p)) R) h

theorem reduce_fraction (p : ℕ) (x : localRing) :
    reduceAt p x * ((x:ℚ).den : ZMod (2^p)) = ((x:ℚ).num : ZMod (2^p)) := by
  have h : x*((x:ℚ).den : localRing) = ((x:ℚ).num : localRing) := by
    apply Subtype.ext
    change (x:ℚ)*((x:ℚ).den:ℚ)=((x:ℚ).num:ℚ)
    exact Rat.mul_den_eq_num _
  simpa only [map_mul,map_natCast,map_intCast] using congrArg (reduceAt p) h
end DetDLP.DyadicGrid

namespace DetDLP.PacketSlotLayout
abbrev SymbolPair (r : ℕ) := Fin r × Fin r
def orient {r : ℕ} (p : SymbolPair r) (b : Bool) : SymbolPair r :=
  if b then (max p.1 p.2,min p.1 p.2) else (min p.1 p.2,max p.1 p.2)

end DetDLP.PacketSlotLayout


namespace DetDLP.DyadicGrid

def offset {a : ℕ} (x y : ℕ) : Grid (a+1) := (y:Grid (a+1))-(x:Grid (a+1))

theorem slot_rep {a x y : ℕ} (hx : x < 2^a) (hy : y < 2^a) :
    (offset (a:=a) x y).valMinAbs=(y:ℤ)-(x:ℤ) := by
  have X : (x:ℤ)<(2:ℤ)^a := by exact_mod_cast hx
  have Y : (y:ℤ)<(2:ℤ)^a := by exact_mod_cast hy
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨by simp [offset],?_,?_⟩ <;> rw [pow_succ] <;> push_cast <;> omega

private theorem flips {n : ℕ} (hn : n≠0) (x : ℕ) :
    (n+x).testBit (padicValNat 2 n)= !(x.testBit (padicValNat 2 n)) := by
  let i := padicValNat 2 n
  obtain ⟨q,hq⟩ : 2^i ∣ n := pow_padicValNat_dvd
  have odd : q%2=1 := by
    by_contra h
    have hq' : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
    have bad : 2^(i+1) ∣ n := by rw [hq,pow_succ]; exact Nat.mul_dvd_mul_left _ hq'
    have := (padicValNat_dvd_iff_le (p:=2) hn).mp bad
    change i+1 ≤ i at this; omega
  change (n+x).testBit i= !(x.testBit i)
  rw [hq,Nat.testBit_mul_two_pow_add_eq,odd]
  cases x.testBit i <;> decide

theorem crossing_level {a : ℕ} (t : Grid (a+1)) (ht : t≠0) (i : ℕ) (hi : level t=i)
    (hi' : i < a) (x y : ℕ) (hbits : x.testBit i=y.testBit i) :
    offset (a:=a) x y≠t ∧ level (t-offset (a:=a) x y) ≤ i := by
  let δ := t-offset (a:=a) x y
  have et : t.val≠0 := by intro h; apply ht; simpa [h] using (ZMod.natCast_zmod_val t).symm
  have neq : ¬ (t.val+x ≡ y [MOD 2^(i+1)]) := by
    intro h
    have eq := congrArg (fun z : ℕ => z.testBit i) h
    simp only [Nat.testBit_mod_two_pow,show decide (i < i+1)=true from decide_eq_true (by omega),Bool.true_and] at eq
    have flip := flips et x
    change padicValNat 2 t.val=i at hi
    rw [hi,hbits] at flip
    rw [eq] at flip
    cases hbit : y.testBit i <;> simp [hbit] at flip
  have nodiv : ¬2^(i+1) ∣ δ.val := by
    intro hd
    have sumEq : (t.val+x:ℕ) ≡ (δ.val+y:ℕ) [MOD 2^(a+1)] := by
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      simp [δ,offset]; ring
    have sm := sumEq.of_dvd (pow_dvd_pow 2 (by omega : i+1 ≤ a+1))
    have zd : δ.val ≡ 0 [MOD 2^(i+1)] := Nat.modEq_zero_iff_dvd.mpr hd
    exact neq (sm.trans (by simpa using zd.add_right y))
  have nδ : δ≠0 := by intro h; apply nodiv; simp [h]
  constructor
  · intro h; apply nδ; simp [δ,h]
  · change padicValNat 2 δ.val ≤ i
    by_contra h
    apply nodiv
    apply (padicValNat_dvd_iff _ _).mpr
    exact Or.inr (by omega)

theorem actual_tile {a : ℕ} (t : Grid (a+1)) (ht : t≠0) (i : ℕ)
    (hi : level t=i) (hi' : i<a) (x y₀ : Fin (2^a))
    (hbits : x.val.testBit i=y₀.val.testBit i) (p : ℕ) (hp : 0<p)
    {R : Type*} [CommRing R] [Algebra (ZMod (2^p)) R] (z : R) :
    let r (d : Grid (a+1)) := d.valMinAbs
    let φ := (algebraMap (ZMod (2^p)) R).comp (reduceAt p)
    let W (y : Fin (2^a)) := (residueKernel r ZMod.coe_valMinAbs
      (by simp [r]) t (offset (a:=a) x.val y.val)).eval₂ φ z
    ∃ u v : R,∀ (y : Fin (2^a)) (j : ℕ), y.val=y₀.val+2^(i+1)*j →
      W y = ∑ b ∈ Finset.range (p-1), (2:R)^(b+1)*(u*v^b)*(j:R)^b := by
  intro r φ W
  obtain ⟨hne,hl⟩ := crossing_level t ht i hi hi' x.val y₀.val hbits
  obtain ⟨u,v,H⟩ := extension_tile r ZMod.coe_valMinAbs (by simp [r]) t _ hne i hl p hp z
  refine ⟨u,v,?_⟩
  intro y j hy
  have hmod : y.val % 2^(i+1)=y₀.val % 2^(i+1) := by rw [hy,Nat.add_mul_mod_self_left]
  have hb := congrArg (fun z : ℕ => z.testBit i) hmod
  simp only [Nat.testBit_mod_two_pow,show decide (i < i+1)=true from decide_eq_true (by omega),Bool.true_and] at hb
  apply H _ j (crossing_level t ht i hi hi' _ _ (hbits.trans hb.symm)).1
  dsimp only [r]
  rw [slot_rep x.isLt y.isLt,slot_rep x.isLt y₀.isLt,hy]
  push_cast; ring

end DetDLP.DyadicGrid

namespace DetDLP.PacketRowModes
open Finset DyadicGrid PacketSlotLayout

def tile (i y : ℕ) : Fin (2^(i+1)) := ⟨y%2^(i+1),Nat.mod_lt _ (Nat.two_pow_pos _)⟩
def index (i y : ℕ) := y/2^(i+1)
theorem tile_bit (i y : ℕ) : (tile i y).val.testBit i=y.testBit i := by simp [tile]

theorem different {r} (tag : SymbolPair r) (u v : Bool) :
    (orient tag u).1 ≠ (orient tag v).2 ↔ tag.1≠tag.2 ∧ u=v := by
  obtain ⟨c,d⟩ := tag
  rcases lt_trichotomy c d with h|rfl|h <;> cases u <;> cases v <;> simp_all [orient,min_eq_left,min_eq_right,max_eq_left,max_eq_right,le_of_lt,ne_of_lt,ne_of_gt]

noncomputable def kernel {a p : ℕ} {R : Type*} [CommRing R] [Algebra (ZMod (2^p)) R]
    (t : Grid (a+1)) (z : R) (x y : Fin (2^a)) : R :=
  (residueKernel (fun d => d.valMinAbs) ZMod.coe_valMinAbs (by simp) t (offset (a:=a) x.val y.val)).eval₂
    ((algebraMap (ZMod (2^p)) R).comp (reduceAt p)) z

variable {E R : Type*} [Fintype E] [DecidableEq E] [CommRing R]

noncomputable def moment {a i : ℕ} (pos : E → Fin (2^a)) (realPorts : Finset E)
    (k : Fin (2^(i+1))) (b : ℕ) (X : E → R) : R :=
  ∑ e ∈ realPorts, if tile i (pos e).val=k then (index i (pos e).val : R)^b*X e else 0

theorem row {r a p : ℕ} [Algebra (ZMod (2^p)) R] (hp : 0<p) (i : Fin a)
    (t : Grid (a+1)) (ht : t≠0) (hi : level t=i.val) (z : R) (tag : SymbolPair r)
    (x : Fin (2^a)) (pos : E → Fin (2^a)) (ports : Finset E) :
    let rowG := (orient tag (x.val.testBit i.val)).1
    let colG (e : E) := (orient tag ((pos e).val.testBit i.val)).2
    ∃ A : Fin (2^(i.val+1)) → Fin (p-1) → R,
      (∀ k b, (orient tag (k.val.testBit i.val)).2=rowG → A k b=0) ∧
      ∀ X : E → R, (∑ e ∈ ports,kernel (p:=p) t z x (pos e)*X e) =
        (∑ e ∈ ports,if colG e=rowG then kernel (p:=p) t z x (pos e)*X e else 0) +
        ∑ k, ∑ b : Fin (p-1), A k b*((2:R)^(b.val+1)*moment pos ports k b.val X) := by
  classical
  intro rowG colG
  let K := Fin (2^(i.val+1))
  have one (k : K) : ∃ A : Fin (p-1) → R,
      ((orient tag (k.val.testBit i.val)).2=rowG → ∀ b,A b=0) ∧
      ∀ e : E,tile i.val (pos e).val=k →
        (if colG e=rowG then 0 else kernel (p:=p) t z x (pos e)) =
          ∑ b : Fin (p-1), A b*((2:R)^(b.val+1)*(index i.val (pos e).val:R)^b.val) := by
    have cg (e : E) (he : tile i.val (pos e).val=k) : colG e=(orient tag (k.val.testBit i.val)).2 := by
      dsimp [colG]; rw [← tile_bit i.val (pos e).val,he]
    by_cases localG : (orient tag (k.val.testBit i.val)).2=rowG
    · refine ⟨fun _ => 0,fun _ _ => rfl,?_⟩
      intro e he; simp [cg e he,localG]
    · let y₀ : Fin (2^a) := ⟨k.val,k.isLt.trans_le (Nat.pow_le_pow_right (by decide) i.isLt)⟩
      have bit := ((different tag (x.val.testBit i.val) (k.val.testBit i.val)).mp (Ne.symm localG)).2
      obtain ⟨u,v,h⟩ := actual_tile t ht i.val hi i.isLt x y₀ bit p hp z
      refine ⟨fun b => u*v^b.val,fun eq => (localG eq).elim,?_⟩
      intro e he
      rw [if_neg (by rw [cg e he]; exact localG)]
      have heq : (pos e).val=y₀.val+2^(i.val+1)*index i.val (pos e).val := by
        change (pos e).val=k.val+2^(i.val+1)*((pos e).val/2^(i.val+1))
        rw [← he]; exact (Nat.mod_add_div ..).symm
      have H := h (pos e) _ heq
      change kernel (p:=p) t z x (pos e)=_ at H
      rw [H,← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl; intro b _; ring
  choose A vanish H using one
  refine ⟨A,fun k b h => vanish k h b,?_⟩
  intro X
  have byedge (e : E) :
      kernel (p:=p) t z x (pos e)*X e =
        (if colG e=rowG then kernel (p:=p) t z x (pos e)*X e else 0) +
        ∑ k : K, ∑ b : Fin (p-1), A k b*((2:R)^(b.val+1)*
         (if tile i.val (pos e).val=k then (index i.val (pos e).val:R)^b.val*X e else 0)) := by
    rw [sum_eq_single (tile i.val (pos e).val)]
    · simp only [ite_true]
      have h := congrArg (fun v : R => v*X e) (H (tile i.val (pos e).val) e rfl)
      simp only [sum_mul] at h
      simp only [← mul_assoc]
      by_cases q : colG e=rowG
      · simp [q,←mul_assoc] at h ⊢; exact h.symm
      · simpa [q,←mul_assoc] using h
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  rw [sum_congr rfl (fun e _ => byedge e),sum_add_distrib]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl; intro k _
  rw [sum_comm]
  apply sum_congr rfl; intro b _
  simp [moment,mul_sum]

end DetDLP.PacketRowModes

namespace DetDLP.PacketSelectorForms
open Finset PacketSlotLayout PacketRowModes DyadicGrid
variable {r a p : ℕ} (i : Fin a) (tag : SymbolPair r)
abbrev Tile (i : Fin a) := Fin (2^(i.val+1))
def side (right : Bool) (x : ℕ) := if right then (orient tag (x.testBit i.val)).2 else (orient tag (x.testBit i.val)).1
abbrev Mode (i : Fin a) (tag : SymbolPair r) (p : ℕ) (g : Fin r) :=
  {k : Tile i // side i tag false k.val=g} × Fin (p-1)
variable {R E : Type*} [CommRing R] [Fintype E] [DecidableEq E] [Algebra (ZMod (2^p)) R]
variable (pos : E → Fin (2^a)) (ports : Finset E)
def same (g : Fin r) (X Y : E → R) := ∀ e∈ports,side i tag true (pos e).val=g → X e=Y e
theorem moment_local (k : Tile i) (b : ℕ) (X Y : E → R) (h : same i tag pos ports (side i tag true k.val) X Y) :
    moment pos ports k b X=moment pos ports k b Y := by
  unfold PacketRowModes.moment
  apply sum_congr rfl; intro e he
  by_cases hk : tile i.val (pos e).val=k
  · have heq : side i tag true (pos e).val=side i tag true k.val := by
      simp only [side,ite_true]; rw [←tile_bit i.val (pos e).val,hk]
    simp [hk,h e he heq]
  · simp [hk]

theorem other (x y : ℕ) (h : side i tag false y≠side i tag false x) :
    side i tag true y=side i tag false x := by
  dsimp [side] at *
  cases hx : x.testBit i.val <;> cases hy : y.testBit i.val <;> simp_all [orient]

theorem row_poly (hp : 0<p) (t : Grid (a+1)) (ht : t≠0) (hi : level t=i.val) (z : R) (x : Fin (2^a)) :
    let g := side i tag false x.val
    ∃ F : (E→R) → MvPolynomial (Mode i tag p g) R,
      (∀ X Y,same i tag pos ports g X Y → F X=F Y) ∧
      ∀ X,MvPolynomial.eval (fun j : Mode i tag p g => (2:R)^(j.2.val+1)*moment pos ports j.1.val j.2.val X) (F X) =
        ∑ e∈ports,kernel (p:=p) t z x (pos e)*X e := by
  classical
  intro g
  obtain ⟨A,zero,H⟩ := row hp i t ht hi z tag x pos ports
  let base (X : E→R) := ∑ e∈ports,if side i tag true (pos e).val=g then kernel (p:=p) t z x (pos e)*X e else 0
  let F (X : E→R) : MvPolynomial (Mode i tag p g) R := MvPolynomial.C (base X) +
    ∑ k : {k : Tile i // side i tag false k.val=g},∑ b : Fin (p-1),
      MvPolynomial.C (A k.val b)*MvPolynomial.X (k,b)
  refine ⟨F,?_,?_⟩
  · intro X Y hh
    have eq : base X=base Y := by
      apply sum_congr rfl; intro e he
      split_ifs with h
      · rw [hh e he h]
      · rfl
    simp [F,eq]
  · intro X
    rw [H X]
    simp only [F,MvPolynomial.eval_add,MvPolynomial.eval_sum,MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
    change base X+_=base X+_
    congr 1
    let f (k : Tile i) := ∑ b : Fin (p-1), A k b*((2:R)^(b.val+1)*PacketRowModes.moment pos ports k b.val X)
    let sub : Finset (Tile i) := univ.filter (fun k => side i tag false k.val=g)
    change (∑ k : {k : Tile i // side i tag false k.val=g}, f k.val)=∑ k,f k
    rw [← Finset.sum_subtype sub (fun k => by simp [sub]) f]
    apply sum_subset (filter_subset _ _)
    intro k _ hk
    have ne : side i tag false k.val≠g := by simpa using hk
    have zz := other i tag x.val k.val ne
    apply sum_eq_zero; intro b _
    rw [zero k b zz,zero_mul]

theorem packet (hp : 0<p) (t : Grid (a+1)) (ht : t≠0) (hi : level t=i.val) (z : R)
    (g : Fin r) (rows : Finset (Fin (2^a))) (hrow : ∀ x∈rows,side i tag false x.val=g) :
    ∃ F : (Fin (2^a)→Bool) → (E→R) → MvPolynomial (Mode i tag p g) R,
      (∀ Y Y' X X',(∀ x∈rows,Y x=Y' x) → same i tag pos ports g X X' → F Y X=F Y' X') ∧
      ∀ Y X,MvPolynomial.eval (fun j : Mode i tag p g => (2:R)^(j.2.val+1)*moment pos ports j.1.val j.2.val X) (F Y X) =
        ∏ x∈rows,let v:=∑ e∈ports,kernel (p:=p) t z x (pos e)*X e
                 if Y x then v else 1-v := by
  classical
  have one (x : ↥rows) : ∃ P : (E→R) → MvPolynomial (Mode i tag p g) R,
      (∀ X Y,same i tag pos ports g X Y → P X=P Y) ∧
      ∀ X,MvPolynomial.eval (fun j : Mode i tag p g => (2:R)^(j.2.val+1)*moment pos ports j.1.val j.2.val X) (P X) =
        ∑ e∈ports,kernel (p:=p) t z x.val (pos e)*X e := by
    have h := row_poly i tag pos ports hp t ht hi z x.val
    dsimp only at h; rwa [hrow x.val x.property] at h
  choose P loc ev using one
  let F (Y : Fin (2^a)→Bool) (X : E→R) := ∏ x : ↥rows,if Y x then P x X else 1-P x X
  refine ⟨F,?_,?_⟩
  · intro Y Y' X X' hy hx
    apply prod_congr rfl; intro x _
    rw [hy x x.property,loc x X X' hx]
  · intro Y X
    rw [show F Y X= _ from rfl,map_prod,← Finset.prod_attach rows]
    apply prod_congr rfl; intro x _
    cases h : Y x.val <;> simp [h,ev]

end DetDLP.PacketSelectorForms

section

namespace DetDLP.ResidualChildGraph
open Finset
variable {L P E R : Type*} [Fintype L] [Fintype P] [Fintype E] [CommRing R]

abbrev vertex := L ⊕ P
noncomputable def network (owner : E → L) (pkt : E → P) : BipartiteMultigraph where
  nV := Fintype.card (L ⊕ P)
  nE := Fintype.card E
  endpoints i := (Fintype.equivFin _ (Sum.inl (owner ((Fintype.equivFin E).symm i)) : L ⊕ P),
    Fintype.equivFin _ (Sum.inr (pkt ((Fintype.equivFin E).symm i)) : L ⊕ P))
  side v := ((Fintype.equivFin (L ⊕ P)).symm v).isRight
  bipartite e := by simp

/-- Provide the entry tensor with exactly the bits at its incident ports. -/
def supplied (G : BipartiteMultigraph) (v : Fin G.nV) (α : Fin (G.deg v) → Bool) (e : Fin G.nE) : Bool :=
  if h : e ∈ G.ports v then α ⟨(G.ports v).idxOf e,List.idxOf_lt_length_iff.mpr h⟩ else false

private theorem supplied_eq (G : BipartiteMultigraph) (v : Fin G.nV) (x : Fin G.nE → Bool)
    (e : Fin G.nE) (h : (G.endpoints e).1=v ∨ (G.endpoints e).2=v) :
    supplied G v (fun i => x ((G.ports v).get i)) e = x e := by
  have he : e ∈ G.ports v := by simp [BipartiteMultigraph.ports,h]
  rw [supplied,dif_pos he]; exact congrArg x (List.idxOf_get _)

abbrev fiber {A B : Type*} (f : A → B) (b : B) := {a : A // f a=b}

noncomputable def tensor (owner : E → L) (pkt : E → P)
    (old : (l : L) → (fiber owner l → Bool) → R)
    (fresh : (p : P) → (fiber pkt p → Bool) → R)
    (j : Fin (network owner pkt).nV) (α : Fin ((network owner pkt).deg j) → Bool) : R :=
  let bit (e : E) := supplied _ j α (Fintype.equivFin E e)
  match (Fintype.equivFin (L ⊕ P)).symm j with
  | .inl l => old l (fun e => bit e.val)
  | .inr p => fresh p (fun e => bit e.val)

theorem contract [DecidableEq E] (owner : E → L) (pkt : E → P)
    (old : (l : L) → (fiber owner l → Bool) → R)
    (fresh : (p : P) → (fiber pkt p → Bool) → R) :
    BTNContract (network owner pkt) (tensor owner pkt old fresh) =
      ∑ x : E → Bool,(∏ l,old l (fun e => x e.val))*(∏ p,fresh p (fun e => x e.val)) := by
  classical
  let G := network owner pkt
  let v := Fintype.equivFin (L ⊕ P)
  let e := Fintype.equivFin E
  let re : (Fin (Fintype.card E) → Bool) ≃ (E → Bool) := (e.arrowCongr (Equiv.refl Bool)).symm
  unfold BTNContract
  apply Fintype.sum_equiv re; intro x
  let V (j : L ⊕ P) := Sum.elim (fun l => old l (fun k => re x k.val))
    (fun p => fresh p (fun k => re x k.val)) j
  have eq : (∏ j : Fin G.nV, tensor owner pkt old fresh j (fun i => x ((G.ports j).get i))) = ∏ j, V j := by
    symm; apply Fintype.prod_equiv v; intro j
    cases j with
    | inl l =>
      dsimp only [V,Sum.elim_inl]
      simp only [tensor,v,Equiv.symm_apply_apply]
      apply congrArg (old l); funext k; symm
      apply supplied_eq; left
      simp [G,network,v,k.property]
    | inr p =>
      dsimp only [V,Sum.elim_inr]
      simp only [tensor,v,Equiv.symm_apply_apply]
      apply congrArg (fresh p); funext k; symm
      apply supplied_eq; right
      simp [G,network,v,k.property]
  rw [eq,Fintype.prod_sum_type]
  rfl

/-- Degrees count actual incident edges, including parallel copies. -/
theorem degree [DecidableEq L] [DecidableEq P] (owner : E → L) (pkt : E → P) (j : L ⊕ P) :
    let G := network owner pkt
    G.deg (Fintype.equivFin _ j) =
      Fintype.card {e : E // (Sum.inl (owner e) : L ⊕ P)=j ∨ Sum.inr (pkt e)=j} := by
  classical
  intro G
  let v := Fintype.equivFin (L ⊕ P)
  let e := Fintype.equivFin E
  let l := G.ports (v j)
  have hn : l.Nodup := (List.nodup_finRange _).filter _
  have hm (a : Fin G.nE) : a ∈ l ↔ (Sum.inl (owner (e.symm a)) : L ⊕ P)=j ∨ Sum.inr (pkt (e.symm a))=j := by
    change a ∈ List.filter _ (List.finRange _) ↔ _
    rw [List.mem_filter]; simp [G,network,v,e]; exact fun _ => List.mem_finRange a
  let f : {a : Fin G.nE // a∈l} ≃ {a : E // (Sum.inl (owner a) : L ⊕ P)=j ∨ Sum.inr (pkt a)=j} :=
    { toFun := fun a => ⟨e.symm a.val,(hm _).mp a.property⟩
      invFun := fun a => ⟨e a.val,(hm _).mpr (by simpa using a.property)⟩
      left_inv := by intro a; exact Subtype.ext (e.apply_symm_apply a.val)
      right_inv := by intro a; exact Subtype.ext (e.symm_apply_apply a.val) }
  change l.length = _
  rw [← Nat.card_eq_fintype_card,← Nat.card_fin l.length]; exact Nat.card_congr ((List.Nodup.getEquiv l hn).trans f)

end DetDLP.ResidualChildGraph
end

section

namespace DetDLP.TerminalModeFactor
open Finset MvPolynomial

noncomputable def exponent {J : Type*} [Fintype J] {p : ℕ} (β : J → Fin p) : J →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (β j).val)

@[simp] theorem exponent_apply {J : Type*} [Fintype J] {p : ℕ} (β : J → Fin p) (j : J) :
    exponent β j = (β j).val := rfl

private theorem killed {R : Type*} [CommSemiring R] {p n : ℕ} (hz : (2:R)^p=0) (h : p≤n) :
    (2:R)^n=0 := by rw [← Nat.add_sub_of_le h,pow_add,hz,zero_mul]

theorem finite_expand {R J : Type*} [CommSemiring R] [Fintype J] [DecidableEq J]
    (p : ℕ) (hz : (2:R)^p=0) (w : J → ℕ) (hw : ∀ i, 0<w i) (z : J → R) (P : MvPolynomial J R) :
    eval (fun i => (2:R)^(w i)*z i) P = ∑ β : J → Fin p,
      (2:R)^(∑ i,w i*(β i).val) * (P.coeff (exponent β) * ∏ i, z i^(β i).val) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add,hf,hg,← sum_add_distrib]; apply sum_congr rfl; intro β hβ; rw [coeff_add]; ring
  | monomial d c =>
    have val : eval (fun i => (2:R)^(w i)*z i) (monomial d c) =
        (2:R)^(∑ i,w i*d i)*(c*∏ i,z i^(d i)) := by
      rw [eval_monomial,Finsupp.prod_fintype _ _ (by simp)]
      simp_rw [mul_pow,← pow_mul]
      rw [prod_mul_distrib,← Finset.prod_pow_eq_pow_sum]; ring
    rw [val]
    by_cases small : ∀ i,d i<p
    · let β : J → Fin p := fun i => ⟨d i,small i⟩
      have he : exponent β = d := by ext; rfl
      rw [sum_eq_single β]
      · simp [he,β]
      · intro η hη hn
        have hd : exponent η ≠ d := by
          intro he; apply hn; funext j; apply Fin.ext; exact DFunLike.congr_fun he j
        simp [coeff_monomial,hd,hd.symm]
      · simp
    · push_neg at small
      obtain ⟨i,hi⟩ := small
      have hb : p ≤ ∑ j,w j*d j := hi.trans ((Nat.le_mul_of_pos_left _ (hw i)).trans
        (single_le_sum (fun j _ => Nat.zero_le (w j*d j)) (mem_univ i)))
      rw [killed hz hb,zero_mul]; symm; apply sum_eq_zero; intro β hβ
      have he : exponent β ≠ d := by
        intro eqn; have h := DFunLike.congr_fun eqn i
        change (β i).val = d i at h; have := (β i).isLt; omega
      simp [coeff_monomial,he,he.symm]

section
variable {G : Type*} [Fintype G] [DecidableEq G] {J : G → Type*} [∀ g, Fintype (J g)] [∀ g, DecidableEq (J g)]
variable {A : G → Type*} [∀ g,Fintype (A g)] {T : G → Type*} {R : Type*} [CommSemiring R]

noncomputable def child {p : ℕ} (src : Sigma J → G)
    (loc : ∀ g, T g → A g → MvPolynomial (J g) R)
    (leg : ∀ g, Sigma J → A g → R) (β : ∀ g,J g → Fin p) (g : G) (η : T g) : R :=
  ∑ x : A g, (loc g η x).coeff (exponent (β g)) *
    ∏ s ∈ univ.filter (fun s : Sigma J => src s = g), (leg g s x)^(β s.1 s.2).val

/-- Each fixed terminal assignment uses the same feasible mode set. After the source
powers are regrouped, each child depends only on its own terminal component. -/
theorem factor (p : ℕ) (hz : (2:R)^p=0) (w : ∀ g,J g → ℕ) (hw : ∀ g j, 0 < w g j)
    (src : Sigma J → G) (loc : ∀ g, T g → A g → MvPolynomial (J g) R)
    (leg : ∀ g, Sigma J → A g → R) (τ : ∀ g,T g) :
    let cost (β : ∀ g,J g → Fin p) := ∑ g,∑ j,w g j*(β g j).val
    (∑ x : (∀ g,A g), ∏ g, eval
      (fun j => (2:R)^(w g j)*leg (src ⟨g,j⟩) ⟨g,j⟩ (x (src ⟨g,j⟩))) (loc g (τ g) (x g))) =
      ∑ β ∈ univ.filter (fun β => cost β < p), (2:R)^(cost β) * ∏ g,child src loc leg β g (τ g) := by
  classical
  intro cost
  let L (x : ∀ g,A g) (s : Sigma J) := leg (src s) s (x (src s))
  let c (β : ∀ g,J g → Fin p) (g : G) (x : A g) := (loc g (τ g) x).coeff (exponent (β g))
  let f (β : ∀ g,J g → Fin p) (g : G) (x : A g) :=
    c β g x * ∏ s ∈ univ.filter (fun s : Sigma J => src s=g), (leg g s x)^(β s.1 s.2).val
  have splitx (x : ∀ g,A g) :
      (∏ g, eval (fun j => (2:R)^(w g j)* L x ⟨g,j⟩) (loc g (τ g) (x g))) =
          ∑ β : (∀ g,J g → Fin p), (2:R)^(cost β) * ∏ g, f β g (x g) := by
    simp_rw [finite_expand p hz _ (hw _)]; rw [Fintype.prod_sum]; apply sum_congr rfl; intro β hβ
    dsimp only [cost,f,c]
    rw [prod_mul_distrib,← prod_pow_eq_pow_sum,prod_mul_distrib,prod_mul_distrib]
    congr 2
    let F (s : Sigma J) := (L x s)^(β s.1 s.2).val
    calc
      _ = ∏ s : Sigma J, F s := (Fintype.prod_sigma F).symm
      _ = ∏ g, ∏ s ∈ univ.filter (fun s : Sigma J => src s=g), F s := (Finset.prod_fiberwise univ src F).symm
      _ = _ := by
        apply prod_congr rfl; intro g hg
        apply prod_congr rfl; intro s hs; have he := (mem_filter.mp hs).2
        change src s = g at he
        subst g
        rfl
  change (∑ x : (∀ g,A g), ∏ g, eval (fun j => (2:R)^(w g j)* L x ⟨g,j⟩) _) = _
  simp_rw [splitx]; rw [sum_comm]
  have eg (β : ∀ g,J g → Fin p) : (∑ x : (∀ g,A g), (2:R)^(cost β)*∏ g,f β g (x g)) =
      (2:R)^(cost β)*∏ g,child src loc leg β g (τ g) := by
    rw [← mul_sum,← Fintype.prod_sum]; rfl
  simp_rw [eg]
  symm; apply sum_subset (filter_subset ..); intro β hβ hout
  have hi : p ≤ cost β := by simpa using hout
  rw [killed hz hi,zero_mul]
end
end DetDLP.TerminalModeFactor
end

section

namespace DetDLP.PacketChildContraction
open Finset MvPolynomial ResidualChildGraph
variable {G P R : Type*} [Fintype G] [DecidableEq G] [Fintype P] [DecidableEq P] [CommRing R]
variable {L E T : G → Type*} [∀ g,Fintype (L g)] [∀ g,Fintype (E g)] [∀ g,DecidableEq (E g)]
variable {J : G × P → Type*} [∀ h,Fintype (J h)] [∀ h,DecidableEq (J h)]

noncomputable def fresh (pkt : ∀ g,E g → P) (src : Sigma J → G)
    (localP : (h : G × P) → (fiber (pkt h.1) h.2 → Bool) → MvPolynomial (J h) R)
    (observable : ∀ g p,Sigma J → (fiber (pkt g) p → Bool) → R)
    {n : ℕ} (β : ∀ h,J h → Fin n) (g : G) (p : P) (x : fiber (pkt g) p → Bool) : R :=
  (localP (g,p) x).coeff (TerminalModeFactor.exponent (β (g,p))) *
    ∏ s ∈ univ.filter (fun s : Sigma J => (src s,s.1.2)=(g,p)), (observable g p s x)^(β s.1 s.2).val

/-- Each finite mode contributes the contractions of actual bipartite child graphs.
Their edges are the retained ports, and each new tensor is local to one packet. -/
theorem factor (owner : ∀ g,E g → L g) (pkt : ∀ g,E g → P) (src : Sigma J → G)
    (old : ∀ g (l : L g),T g → (fiber (owner g) l → Bool) → R)
    (localP : (h : G × P) → (fiber (pkt h.1) h.2 → Bool) → MvPolynomial (J h) R)
    (observable : ∀ g p,Sigma J → (fiber (pkt g) p → Bool) → R)
    (n : ℕ) (hn : (2:R)^n=0) (weight : ∀ h,J h→ℕ) (hw : ∀ h j,0<weight h j)
    (τ : ∀ g,T g) :
    let cost (β : ∀ h,J h → Fin n) := ∑ h,∑ j,weight h j*(β h j).val
    let obs (x : ∀ g,E g → Bool) (s : Sigma J) :=
      observable (src s) s.1.2 s (fun i => x (src s) i.val)
    (∑ x : (∀ g,E g → Bool),
      (∏ g,∏ l,old g l (τ g) (fun i => x g i.val)) *
      ∏ h : G × P,MvPolynomial.eval (fun j => (2:R)^(weight h j)*obs x ⟨h,j⟩)
        (localP h (fun i => x h.1 i.val))) =
    ∑ β ∈ univ.filter (fun β => cost β<n),(2:R)^(cost β) *
      ∏ g,BTNContract (network (owner g) (pkt g))
        (tensor (owner g) (pkt g) (fun l => old g l (τ g)) (fresh pkt src localP observable β g)) := by
  classical
  intro cost obs
  let orig (g : G) (x : E g → Bool) := ∏ l,old g l (τ g) (fun i => x i.val)
  let A (x : ∀ g,E g→Bool) (β : ∀ h,J h → Fin n) (h : G × P) :=
    (localP h (fun i => x h.1 i.val)).coeff (TerminalModeFactor.exponent (β h))
  let F (x : ∀ g,E g→Bool) (β : ∀ h,J h → Fin n) (h : G × P) :=
    fresh pkt src localP observable β h.1 h.2 (fun i => x h.1 i.val)
  have regroup (x : ∀ g,E g→Bool) (β : ∀ h,J h → Fin n) :
      (∏ h : G × P, A x β h * ∏ j,obs x ⟨h,j⟩^(β h j).val) =
        ∏ h : G × P, F x β h := by
    dsimp only [F,fresh]
    rw [prod_mul_distrib,prod_mul_distrib]
    congr 1
    let u (s : Sigma J) := (obs x s)^(β s.1 s.2).val
    calc
      _ = ∏ s : Sigma J,u s := (Fintype.prod_sigma u).symm
      _ = ∏ h : G × P,∏ s ∈ univ.filter (fun s : Sigma J => (src s,s.1.2)=h),u s :=
        (Finset.prod_fiberwise univ (fun s : Sigma J => (src s,s.1.2)) u).symm
      _ = _ := by
        apply prod_congr rfl; intro h _
        apply prod_congr rfl; intro s hs
        obtain rfl : (src s,s.1.2)=h := (mem_filter.mp hs).2
        rfl
  have expand (x : ∀ g,E g→Bool) :
      (∏ h : G × P,MvPolynomial.eval (fun j => (2:R)^(weight h j)*obs x ⟨h,j⟩)
           (localP h (fun i => x h.1 i.val))) =
        ∑ β : (∀ h,J h → Fin n),(2:R)^(cost β)*∏ h : G × P,F x β h := by
    simp_rw [TerminalModeFactor.finite_expand n hn _ (hw _)]
    rw [Fintype.prod_sum]; apply sum_congr rfl; intro β _
    rw [prod_mul_distrib,← prod_pow_eq_pow_sum]
    exact congrArg (_*·) (regroup x β)
  simp_rw [expand,mul_sum]; rw [sum_comm]
  have collected (β : ∀ h,J h → Fin n) :
      (∑ x : (∀ g,E g→Bool),(∏ g, orig g (x g))*((2:R)^(cost β)*∏ h,F x β h)) =
        (2:R)^(cost β)*∏ g,BTNContract (network (owner g) (pkt g))
          (tensor (owner g) (pkt g) (fun l => old g l (τ g)) (fresh pkt src localP observable β g)) := by
    simp_rw [ResidualChildGraph.contract]
    rw [Fintype.prod_sum,mul_sum]; apply sum_congr rfl; intro x _
    rw [Fintype.prod_prod_type,prod_mul_distrib]
    dsimp only [orig,F]; ring
  change (∑ β,∑ x : (∀ g,E g→Bool),(∏ g, orig g (x g))*((2:R)^(cost β)*∏ h,F x β h))=_
  simp_rw [collected]
  symm; apply sum_subset (filter_subset ..); intro β _ h
  have hle : n ≤ cost β := by simpa using h
  rw [← Nat.add_sub_of_le hle,pow_add,hn,zero_mul,zero_mul]
end DetDLP.PacketChildContraction
end

section
namespace DetDLP.PacketPortFibers
open Finset PacketSelectorForms PacketSlotLayout PacketRowModes DyadicGrid ResidualChildGraph
variable {a r p : ℕ} {P : Type} [Fintype P] [DecidableEq P]
abbrev Slot (a : ℕ) := Fin (2^a)
variable (i : Fin a) (tag : P → SymbolPair r) (real : P → Finset (Slot a))
abbrev Port (g : Fin r) := {e : P × Slot a × Bool // e.2.1 ∈ real e.1 ∧ side i (tag e.1) e.2.2 e.2.1.val=g}
abbrev packetId (g : Fin r) (e : Port i tag real g) := e.val.1
abbrev Cell (g : Fin r) (q : P) := fiber (packetId i tag real g) q
abbrev J (p : ℕ) (h : Fin r × P) := Mode i (tag h.2) p h.1
abbrev source (s : Sigma (J i tag p)) := side i (tag s.1.2) true s.2.1.val.val
abbrev label (s : Sigma (J i tag p)) := s.2.2.val+1

def localBit (g : Fin r) (q : P) (x : Cell i tag real g q → Bool) (right : Bool) (v : Slot a) : Bool :=
  if h : v∈real q ∧ side i (tag q) right v.val=g then x ⟨⟨(q,v,right),h⟩,rfl⟩ else false
def bit (x : ∀ g,Port i tag real g → Bool) (q : P) (right : Bool) (v : Slot a) : Bool :=
  if h : v∈real q then x (side i (tag q) right v.val) ⟨(q,v,right),h,rfl⟩ else false

theorem restrict_bit (x : ∀ g,Port i tag real g → Bool) (q : P) (g : Fin r) (right : Bool) (v : Slot a)
    (hv : v∈real q) (hg : side i (tag q) right v.val=g) :
    localBit i tag real g q (fun e => x g e.val) right v=bit i tag real x q right v := by
  subst g; simp [localBit,bit,hv]

variable {R : Type} [CommRing R] [Algebra (ZMod (2^p)) R]
def val (b : Bool) : R := if b then 1 else 0
noncomputable def obs (g : Fin r) (q : P) (s : Sigma (J i tag p)) (x : Cell i tag real g q→Bool) : R :=
  moment id (real q) s.2.1.val s.2.2.val (fun v => val (localBit i tag real g q x true v))
noncomputable def rowFactor (t : Grid (a+1)) (z : R) (x : ∀ g,Port i tag real g→Bool) (q : P) (v : Slot a) : R :=
  let u := ∑ e∈real q,kernel (p:=p) t z v e*val (bit i tag real x q true e)
  if bit i tag real x q false v then u else 1-u

theorem realize (hp : 0<p) (t : Grid (a+1)) (ht : t≠0) (hi : level t=i.val) (z : R) :
    ∃ F : (h : Fin r × P) → (Cell i tag real h.1 h.2→Bool) → MvPolynomial (J i tag p h) R,
      ∀ (x : ∀ g,Port i tag real g→Bool),
        (∏ h : Fin r × P,MvPolynomial.eval (fun j : J i tag p h =>
          (2:R)^(label i tag ⟨h,j⟩)*obs i tag real (source i tag ⟨h,j⟩) h.2 ⟨h,j⟩ (fun e => x _ e.val))
          (F h (fun e => x h.1 e.val))) = ∏ q,∏ v∈real q,rowFactor (p:=p) i tag real t z x q v := by
  classical
  let rows (h : Fin r × P) := (real h.2).filter (fun v => side i (tag h.2) false v.val=h.1)
  have forms (h : Fin r × P) := packet i (tag h.2) (id : Slot a → Slot a) (real h.2) hp t ht hi z h.1 (rows h)
    (fun v hv => (mem_filter.mp hv).2)
  choose A localA ev using forms
  let F (h : Fin r × P) (x : Cell i tag real h.1 h.2→Bool) := A h
    (localBit i tag real h.1 h.2 x false) (fun v => val (localBit i tag real h.1 h.2 x true v))
  refine ⟨F,fun x => ?_⟩
  have one (h : Fin r × P) : MvPolynomial.eval (fun j : J i tag p h =>
          (2:R)^(label i tag ⟨h,j⟩)*obs i tag real (source i tag ⟨h,j⟩) h.2 ⟨h,j⟩ (fun e => x _ e.val))
          (F h (fun e => x h.1 e.val)) = ∏ v∈rows h,rowFactor (p:=p) i tag real t z x h.2 v := by
    let V := fun v => val (R:=R) (bit i tag real x h.2 true v)
    let Y := bit i tag real x h.2 false
    have L : F h (fun e => x h.1 e.val) = A h Y V := by
      apply localA
      · intro v hv; exact restrict_bit i tag real x h.2 h.1 false v (mem_filter.mp hv).1 (mem_filter.mp hv).2
      · intro e he hg; exact congrArg val (restrict_bit i tag real x h.2 h.1 true e he hg)
    have O (j : J i tag p h) : obs i tag real (source i tag ⟨h,j⟩) h.2 ⟨h,j⟩ (fun e => x _ e.val) =
        moment id (real h.2) j.1.val j.2.val V := by
      apply moment_local i (tag h.2)
      intro e he hg; exact congrArg val (restrict_bit i tag real x h.2 _ true e he hg)
    simp only [L,O]
    exact ev h Y V
  simp_rw [one]; rw [Fintype.prod_prod_type,Finset.prod_comm]
  apply prod_congr rfl; intro q _
  exact Finset.prod_fiberwise (real q) (fun v => side i (tag q) false v.val) (rowFactor (p:=p) i tag real t z x q)
end DetDLP.PacketPortFibers
end

section
namespace DetDLP.OrientedPacketChildren
open Finset PacketSelectorForms PacketSlotLayout PacketRowModes DyadicGrid ResidualChildGraph PacketPortFibers
variable {a r p : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable (i : Fin a) (tag : P→SymbolPair r) (real : P→Finset (Slot a))
variable {R : Type} [CommRing R] [Algebra (ZMod (2^p)) R]
variable {L T : Fin r→Type} [∀ g,Fintype (L g)]

theorem reduction (hp : 0<p) (t : Grid (a+1)) (ht : t≠0) (hi : level t=i.val) (z : R)
    (owner : ∀ g,Port i tag real g→L g)
    (old : ∀ g (l : L g),T g→(fiber (owner g) l→Bool)→R) :
    let beta := ∀ h,J i tag p h→Fin p
    let w (b : beta) := ∑ h,∑ j : J i tag p h,(j.2.val+1)*(b h j).val
    ∃ F : beta→∀ g q,(Cell i tag real g q→Bool)→R,
    ∀ τ : ∀ g,T g,
      (∑ x : ∀ g,Port i tag real g→Bool,
        (∏ g,∏ l,old g l (τ g) (fun e => x g e.val)) *
        (∏ q,∏ v∈real q,rowFactor (p:=p) i tag real t z x q v)) =
      ∑ b ∈ univ.filter (fun b => w b<p),(2:R)^(w b)*
        ∏ g,BTNContract (network (owner g) (packetId i tag real g))
          (tensor (owner g) (packetId i tag real g) (fun l => old g l (τ g)) (F b g)) := by
  classical
  intro beta w
  obtain ⟨A,hA⟩ := realize i tag real hp t ht hi z
  let pkt := packetId i tag real
  let src := source (p:=p) i tag
  let obs' := obs (R:=R) (p:=p) i tag real
  let wt := fun h (j : J i tag p h) => j.2.val+1
  let f := PacketChildContraction.fresh pkt src A obs' (n:=p)
  have hn : (2:R)^p=0 := by
    have h : ((2:ZMod (2^p))^p)=0 := by rw [← Nat.cast_ofNat (R:=ZMod (2^p)) (n:=2),← Nat.cast_pow]; exact ZMod.natCast_self _
    simpa only [map_pow,map_ofNat,map_zero] using congrArg (algebraMap (ZMod (2^p)) R) h
  refine ⟨f,fun τ => ?_⟩
  have H := PacketChildContraction.factor owner pkt src old A obs' p hn wt (fun _ _ => Nat.succ_pos _) τ
  change _=∑ b ∈ univ.filter (fun b => w b<p), (2:R)^(w b)*_ at H
  rw [← H]
  apply sum_congr rfl; intro x _
  rw [← hA x]

end DetDLP.OrientedPacketChildren
end

section
namespace DetDLP.OrientedOriginalPorts
open Finset PacketSlotLayout PacketSelectorForms PacketPortFibers
abbrev Slots {a : ℕ} {P : Type} (real : P→Finset (Slot a)) := (q : P) × ↥(real q)
def endpoint (G : BipartiteMultigraph) (e : Fin G.nE) (right : Bool) :=
  if G.side (G.endpoints e).1=right then (G.endpoints e).1 else (G.endpoints e).2
theorem incident (G : BipartiteMultigraph) (v : Fin G.nV) (k : Fin (G.deg v)) :
    endpoint G ((G.ports v).get k) (G.side v)=v := by
  let e := (G.ports v).get k
  have h := List.get_mem (G.ports v) k
  change e∈G.ports v at h
  have d : (G.endpoints e).1=v ∨ (G.endpoints e).2=v := by simpa [BipartiteMultigraph.ports] using h
  change endpoint G e (G.side v)=v; unfold endpoint
  rcases d with eq|eq
  · simp [eq]
  · rw [← eq,if_neg (G.bipartite e)]

variable {a r : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable (i : Fin a) (tag : P→SymbolPair r) (real : P→Finset (Slot a))
variable (G : BipartiteMultigraph) (layout : Fin G.nE ≃ Slots real)
abbrev vertex (grp : Fin G.nV→Fin r) (g : Fin r) := {v : Fin G.nV // grp v=g}
def physical (e : P×Slot a×Bool) (he : e.2.1∈real e.1) : Fin G.nE := layout.symm ⟨e.1,e.2.1,he⟩
def assignments (x : ∀ g,Port i tag real g→Bool) (right : Bool) (e : Fin G.nE) : Bool :=
  bit i tag real x (layout e).1 right (layout e).2.val

theorem inverse_assignment (x : ∀ g,Port i tag real g→Bool) (d : Bool) (u : Slots real) :
    assignments i tag real G layout x d (layout.symm u)=bit i tag real x u.1 d u.2.val :=
  congrArg (fun t : Slots real => bit i tag real x t.1 d t.2.val) (layout.apply_symm_apply u)

theorem alignedBit (x : ∀ g,Port i tag real g→Bool) (q : P) (v : Slot a) (d : Bool) (hv : v∈real q)
    (g : Fin r) (hg : side i (tag q) d v.val=g) :
    x g ⟨(q,v,d),hv,hg⟩=bit i tag real x q d v := by
  subst g; simp [bit,hv]

def reindex : (∀ g,Port i tag real g→Bool) ≃ ((Fin G.nE→Bool)×(Fin G.nE→Bool)) where
  toFun x := (assignments i tag real G layout x true,assignments i tag real G layout x false)
  invFun v := fun _ e => if e.val.2.2 then v.1 (physical real G layout e.val e.property.1)
    else v.2 (physical real G layout e.val e.property.1)
  left_inv x := by
    funext g e; obtain ⟨⟨q,k,right⟩,hk,hg⟩ := e; dsimp only at hk hg
    subst g; cases right <;> simp only [Bool.false_eq_true,if_false,if_true,physical,inverse_assignment] <;> simp [bit,hk]
  right_inv v := by
    obtain ⟨x,y⟩ := v
    apply Prod.ext <;> funext e <;> simp [assignments,bit,(layout e).2.property,physical]

variable (grp : Fin G.nV→Fin r)
def Compatible := ∀ e right,side i (tag (layout e).1) right (layout e).2.val.val=grp (endpoint G e right)
variable (align : Compatible i tag real G layout grp)
def owner (g : Fin r) (e : Port i tag real g) : vertex G grp g :=
  ⟨endpoint G (physical real G layout e.val e.property.1) e.val.2.2,by
    have h := align (physical real G layout e.val e.property.1) e.val.2.2
    let u : Slots real := ⟨e.val.1,e.val.2.1,e.property.1⟩
    have E := congrArg (fun v : Slots real => side i (tag v.1) e.val.2.2 v.2.val.val) (layout.apply_symm_apply u)
    exact h.symm.trans (E.trans e.property.2)⟩
def edgeAt (v : Fin G.nV) (k : Fin (G.deg v)) :
    ResidualChildGraph.fiber (owner i tag real G layout grp align (grp v)) ⟨v,rfl⟩ := by
  let e := (G.ports v).get k
  have inc : endpoint G e (G.side v)=v := incident G v k
  let raw := ((layout e).1,(layout e).2.val,G.side v)
  have H : side i (tag (layout e).1) (G.side v) (layout e).2.val.val=grp v := (align e _).trans (congrArg grp inc)
  refine ⟨⟨raw,(layout e).2.property,H⟩,?_⟩
  apply Subtype.ext
  change endpoint G (layout.symm (layout e)) (G.side v)=v
  rw [layout.symm_apply_apply]; exact inc
def old {R : Type} (T : (v : Fin G.nV) → (Fin (G.deg v)→Bool)→R)
    (g : Fin r) (l : vertex G grp g) (x : ResidualChildGraph.fiber (owner i tag real G layout grp align g) l→Bool) : R := by
  obtain ⟨v,hg⟩ := l; subst g
  exact T v (fun k => x (edgeAt i tag real G layout grp align v k))
theorem old_eq {R : Type} (T : (v : Fin G.nV) → (Fin (G.deg v)→Bool)→R) (x : ∀ g,Port i tag real g→Bool)
    (g : Fin r) (l : vertex G grp g) :
    old i tag real G layout grp align T g l (fun k => x g k.val)=
      DeformedContraction.portValue T (assignments i tag real G layout x (G.side l.val)) l.val := by
  obtain ⟨v,hg⟩ := l; subst g
  unfold old DeformedContraction.portValue
  apply congrArg (T v); funext k
  let e := (G.ports v).get k
  have inc : endpoint G e (G.side v)=v := incident G v k
  have H := (align e (G.side v)).trans (congrArg grp inc)
  exact alignedBit i tag real x (layout e).1 (layout e).2.val (G.side v) (layout e).2.property _ H
end DetDLP.OrientedOriginalPorts
end

section
namespace DetDLP.OriginalPacketReduction
open Finset DyadicGrid PacketRowModes PacketSlotLayout PacketSelectorForms PacketPortFibers OrientedOriginalPorts
open ResidualChildGraph
variable {a r p : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable (i : Fin a) (tag : P→SymbolPair r) (real : P→Finset (Slot a))
variable (G : BipartiteMultigraph) (layout : Fin G.nE ≃ Slots real)
variable (grp : Fin G.nV→Fin r) (align : Compatible i tag real G layout grp)
variable {R : Type} [CommRing R] [Algebra (ZMod (2^p)) R]
noncomputable def select (t : Grid (a+1)) (z : R) (x y : Fin G.nE→Bool) (e : Fin G.nE) : R :=
  let q := (layout e).1
  let u := ∑ f : ↥(real q),kernel (p:=p) t z (layout e).2.val f.val * val (x (layout.symm ⟨q,f⟩))
  if y e then u else 1-u
theorem real_products (t : Grid (a+1)) (z : R) (x : ∀ g,Port i tag real g→Bool) :
    (∏ q,∏ k∈real q,rowFactor (p:=p) i tag real t z x q k) =
      ∏ e, select (p:=p) real G layout t z (assignments i tag real G layout x true) (assignments i tag real G layout x false) e := by
  classical
  let f (u : Slots real) := rowFactor (p:=p) i tag real t z x u.1 u.2.val
  calc
    _ = ∏ q,∏ k : ↥(real q),f ⟨q,k⟩ := by
      apply prod_congr rfl; intro q _; exact (Finset.prod_attach (real q) _).symm
    _ = ∏ u : Slots real,f u := (Fintype.prod_sigma f).symm
    _ = ∏ e,f (layout e) := (Equiv.prod_comp layout f).symm
    _ = _ := by
      apply prod_congr rfl; intro e _
      let q := (layout e).1
      have col (w : ↥(real q)) : assignments i tag real G layout x true (layout.symm ⟨q,w⟩) = bit i tag real x q true w.val :=
        inverse_assignment i tag real G layout x true ⟨q,w⟩
      let zf (k : Slot a) := kernel (p:=p) t z (layout e).2.val k * val (bit i tag real x q true k)
      have sumEq : (∑ k∈real q,zf k)= ∑ k : ↥(real q),zf k.val := (Finset.sum_attach (real q) zf).symm
      change (if bit i tag real x q false (layout e).2.val then ∑ k∈real q,zf k else 1-∑ k∈real q,zf k)=_
      rw [sumEq]; unfold select
      change (if bit i tag real x q false (layout e).2.val then ∑ k : ↥(real q),zf k.val else 1-∑ k : ↥(real q),zf k.val) =
        (if bit i tag real x q false (layout e).2.val then _ else 1-_)
      have hsum : (∑ k : ↥(real q),zf k.val) = ∑ k : ↥(real q), kernel (p:=p) t z (layout e).2.val k.val *
          val (assignments i tag real G layout x true (layout.symm ⟨q,k⟩)) := by
        apply sum_congr rfl; intro k _; rw [col]
      rw [hsum]

variable {T : Fin r→Type}
theorem reduce (hp : 0<p) (t : Grid (a+1)) (ht : t≠0) (hi : level t=i.val) (z : R)
    (V : (v : Fin G.nV) → T (grp v) → (Fin (G.deg v)→Bool)→R) :
    let beta := ∀ h,J i tag p h→Fin p
    let w (b : beta) := ∑ h,∑ j : J i tag p h,(j.2.val+1)*(b h j).val
    let own := owner i tag real G layout grp align
    ∃ entries : beta→∀ g q,(Cell i tag real g q→Bool)→R,
      ∃ localValue : (g : Fin r) → T g → (l : vertex G grp g) → (fiber (own g) l→Bool) → R,
      ∀ τ : ∀ g,T g,
        (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v => V v (τ (grp v))) x y * ∏ e,select (p:=p) real G layout t z x y e) =
        ∑ b ∈ univ.filter (fun b => w b<p),(2:R)^(w b)* ∏ g,
          BTNContract (network (own g) (packetId i tag real g))
            (tensor (own g) (packetId i tag real g) (localValue g (τ g)) (entries b g)) := by
  classical
  intro beta w own
  let loc (g : Fin r) (l : vertex G grp g) (u : T g) (b : fiber (own g) l→Bool) : R := by
    obtain ⟨v,h⟩ := l; subst g
    exact V v u (fun k => b (edgeAt i tag real G layout grp align v k))
  obtain ⟨entries,he⟩ := OrientedPacketChildren.reduction i tag real hp t ht hi z own loc
  refine ⟨entries,fun g u l => loc g l u,fun τ => ?_⟩
  rw [← he τ]
  let TT := fun v => V v (τ (grp v))
  let ex := reindex i tag real G layout
  let summand := fun v : (Fin G.nE→Bool)×(Fin G.nE→Bool) => DeformedContraction.weight TT v.1 v.2 *
    ∏ e,select (p:=p) real G layout t z v.1 v.2 e
  change (∑ x,∑ y,summand (x,y))=_
  rw [← Fintype.sum_prod_type,← Equiv.sum_comp ex summand]; apply sum_congr rfl; intro x _
  dsimp only [summand]; congr 1
  · let W := fun v => DeformedContraction.portValue TT (assignments i tag real G layout x (G.side v)) v
    have weight : DeformedContraction.weight TT (ex x).1 (ex x).2=∏ v,W v := by
      unfold DeformedContraction.weight; apply prod_congr rfl; intro v _
      cases hv : G.side v <;> simp [W,hv,ex,reindex]
    rw [weight,← Finset.prod_fiberwise univ grp W]
    apply prod_congr rfl; intro g _
    rw [Finset.prod_subtype (p:=fun v => grp v=g) (univ.filter (fun v => grp v=g)) (fun v => by simp) W]
    apply prod_congr rfl; intro l _
    obtain ⟨v,hg⟩ := l; subst g
    exact (old_eq i tag real G layout grp align TT x (grp v) ⟨v,rfl⟩).symm
  · exact (real_products i tag real G layout t z x).symm
end DetDLP.OriginalPacketReduction
end

open Polynomial Finset DetDLP

theorem solution {a p : ℕ} (i : Fin a) (hp : 0<p)
    (t : ZMod (2^(a+1))) (ht : t≠0) (hi : padicValNat 2 t.val=i.val) :
    ∃ U : ZMod (2^(a+1)) → (ZMod (2^p))[X], OrientedPacketInstance.Represents t U ∧
    ∀ {r : ℕ} (P R : Type) [Fintype P] [DecidableEq P] [CommRing R] [Algebra (ZMod (2^p)) R]
      (G : BipartiteMultigraph) (active : P→Finset (Fin (2^a))) (layout : Fin G.nE ≃ OrientedPacketInstance.Address active)
      (tag : P→Fin r×Fin r) (grp : Fin G.nV→Fin r),
      (∀ e d,OrientedPacketInstance.group i (tag (layout e).1) d (layout e).2.val.val=grp (OrientedPacketInstance.endpoint G e d)) →
      ∀ (T : Fin r→Type) (V : (v : Fin G.nV)→T (grp v)→(Fin (G.deg v)→Bool)→R) (z : R),
      let E := OrientedPacketInstance.Assigned i tag active
      let J := OrientedPacketInstance.Mode i tag p
      let beta := ∀ h,J h→Fin p
      let weight (b : beta) := ∑ h,∑ j : J h,(j.2.val+1)*(b h j).val
      ∃ H : Fin r→BipartiteMultigraph,
        (∀ g,(H g).nE=Fintype.card (E g) ∧ (H g).nV=Fintype.card {v : Fin G.nV // grp v=g}+Fintype.card P) ∧
        (∀ g D, (∀ v : Fin G.nV,Fintype.card {e : E g // OrientedPacketInstance.endpoint G
          (layout.symm ⟨e.val.1,e.val.2.1,e.property.1⟩) e.val.2.2=v} ≤ D) →
          (∀ q : P,Fintype.card {e : E g // e.val.1=q} ≤ D) → (H g).maxDeg≤D) ∧
        ∃ child : beta → (g : Fin r) → T g → (v : Fin (H g).nV) → (Fin ((H g).deg v)→Bool) → R,
          ∀ τ : ∀ g,T g,
            (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
              DeformedContraction.weight (fun v => V v (τ (grp v))) x y *
                ∏ e,OrientedPacketInstance.selector G active layout U z x y e) =
            ∑ b ∈ univ.filter (fun b => weight b<p),(2:R)^(weight b)* ∏ g,BTNContract (H g) (child b g (τ g)) := by
  classical
  let G₀ := ZMod (2^(a+1))
  let S := Finset.univ.image (fun d : G₀ => (d.valMinAbs:ℚ))
  let K := OrientedPacketInstance.kernel (a:=a) t
  let rep (d : G₀) := d.valMinAbs
  have hr : ∀ d : G₀, ((rep d:ℤ):G₀)=d := ZMod.coe_valMinAbs
  have h0 : rep 0=0 := by simp [rep]
  let F₀ (d : G₀) := DyadicGrid.residueKernel rep hr h0 t d
  let U (d : G₀) := (F₀ d).map (DyadicGrid.reduceAt p)
  have he (d : G₀) : K d=DyadicGrid.atNode rep t d := by
    dsimp only [K,S,OrientedPacketInstance.kernel]
    rw [show Finset.univ.image (fun d : G₀ => (d.valMinAbs:ℚ)) =
        Finset.univ.map (DyadicGrid.repEmbedding rep hr) from (Finset.map_eq_image (DyadicGrid.repEmbedding rep hr) Finset.univ).symm,
      DyadicGrid.raw_matches rep hr h0]; rfl
  refine ⟨U,?_,?_⟩
  · intro d n c
    let x := (F₀ d).coeff n
    have h : (x:ℚ)=c := by
      change (x:ℚ)=(K d).coeff n; rw [he]
      have hm : (F₀ d).map DyadicGrid.localRing.subtype=DyadicGrid.atNode rep t d := DyadicGrid.map_liftPoly _ _
      change DyadicGrid.localRing.subtype ((F₀ d).coeff n)=_
      exact (Polynomial.coeff_map ..).symm.trans (congrArg (fun H : ℚ[X] => H.coeff n) hm)
    rw [← h]
    constructor
    · have hu := PadicInt.isUnit_den (x:ℚ) (DyadicGrid.toPadic x).property
      simpa only [map_natCast] using hu.map (PadicInt.toZModPow (p:=2) p)
    · simpa only [U,Polynomial.coeff_map,x] using DyadicGrid.reduce_fraction p x
  · intro r P R _ _ _ _ G active layout tag grp align T V z E J beta weight
    let own := OrientedOriginalPorts.owner i tag active G layout grp align
    let pkt := PacketPortFibers.packetId i tag active
    let H (g : Fin r) := ResidualChildGraph.network (own g) (pkt g)
    obtain ⟨entries,localValue,h⟩ := OriginalPacketReduction.reduce i tag active G layout grp align hp t ht hi z V
    refine ⟨H,fun g => ⟨rfl,Fintype.card_sum⟩,?_,?_,?_⟩
    · intro g D hOld hPacket
      apply Finset.sup_le; intro v _
      let e := Fintype.equivFin (OrientedOriginalPorts.vertex G grp g ⊕ P)
      obtain ⟨v,rfl⟩ := e.surjective v
      rw [ResidualChildGraph.degree]
      cases v with
      | inl l =>
        let eq := Equiv.subtypeEquivProp (α:=E g)
          (p:=fun x => Sum.inl (own g x) = (Sum.inl l : OrientedOriginalPorts.vertex G grp g ⊕ P) ∨ Sum.inr (pkt g x) = Sum.inl l)
          (q:=fun x => OrientedPacketInstance.endpoint G (layout.symm ⟨x.val.1,x.val.2.1,x.property.1⟩) x.val.2.2=l.val)
          (by funext x; apply propext; simp only [Sum.inl.injEq,Sum.inr_ne_inl,or_false,Subtype.ext_iff]; rfl)
        exact (Fintype.card_congr eq).le.trans (hOld l.val)
      | inr q =>
        let eq := Equiv.subtypeEquivProp (α:=E g)
          (p:=fun x => Sum.inl (own g x) = (Sum.inr q : OrientedOriginalPorts.vertex G grp g ⊕ P) ∨ (Sum.inr (pkt g x) : OrientedOriginalPorts.vertex G grp g ⊕ P) = Sum.inr q)
          (q:=fun x => x.val.1=q) (by simp [pkt,PacketPortFibers.packetId])
        exact (Fintype.card_congr eq).le.trans (hPacket q)
    · exact fun b g u => ResidualChildGraph.tensor (own g) (pkt g) (localValue g u) (entries b g)
    · intro τ; refine Eq.trans ?_ (h τ)
      apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; congr 1
      apply prod_congr rfl; intro e _
      unfold OrientedPacketInstance.selector OriginalPacketReduction.select
      have W (f : ↥(active (layout e).1)) :
          (U ((f.val.val:G₀)-((layout e).2.val.val:G₀))).eval₂ (algebraMap (ZMod (2^p)) R) z =
            PacketRowModes.kernel (p:=p) t z (layout e).2.val f.val := by
        simp only [U,F₀,Polynomial.eval₂_map,PacketRowModes.kernel,DyadicGrid.offset,rep]
        rfl
      simp only [W,PacketPortFibers.val]
