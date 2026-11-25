-- Prove2me | solution 1 for DetDLP.tapered_hermite_recovery_weights
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T15:34:56.784973+00:00
-- url     : https://prove2.me/submissions/6808fb3c-53ce-4a3b-aec3-8e89c4ed9b9d

import Mathlib

section

namespace DetDLP.HermitePartialFractions
open Finset Polynomial
variable {ι : Type*} [DecidableEq ι]

noncomputable def power (r : ι → ℚ) (m : ι → ℕ) (i : ι) : ℚ[X] := (X-C (r i))^(m i)
noncomputable def others (s : Finset ι) (r : ι → ℚ) (m : ι → ℕ) (i : ι) := ∏ j ∈ s.erase i, power r m j

theorem decompose (s : Finset ι) (r : ι → ℚ) (hr : Function.Injective r) (m : ι → ℕ)
    (F : ℚ[X]) (hF : F.degree < ((∑ i ∈ s,m i : ℕ):WithBot ℕ)) :
    ∃ B : ι → ℚ[X], (∀ i ∈ s, (B i).degree < (m i : ℕ)) ∧
      F = ∑ i ∈ s, B i * others s r m i := by
  let g := power r m
  have mon (i : ι) : (g i).Monic := (monic_X_sub_C _).pow _
  have deg (i : ι) : (g i).degree = (m i : ℕ) := by simp [g,power,degree_pow]
  have cop : Set.Pairwise s (fun i j => IsCoprime (g i) (g j)) := by
    intro i hi j hj h; exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hr.ne h)).isUnit).pow
  obtain ⟨q,B,hB,eqn⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod F (fun i _ => mon i) cop
  let Z := ∑ i ∈ s, B i * others s r m i
  let D := ∏ i ∈ s, g i
  have hB' (i : ι) (hi : i ∈ s) : (B i).degree < (m i : ℕ) := (hB i hi).trans_eq (deg i)
  have hdeg (s : Finset ι) : (∏ i ∈ s,g i).degree = ((∑ i ∈ s,m i : ℕ):WithBot ℕ) := by
    simp only [degree_prod,deg,Nat.cast_sum]
  have hZ : Z.degree < D.degree := by
    apply (degree_sum_le _ _).trans_lt
    rw [hdeg]
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro i hi
    rw [degree_mul,others,hdeg,← Finset.add_sum_erase s m hi,Nat.cast_add]
    exact WithBot.add_lt_add_right WithBot.coe_ne_bot (hB' i hi)
  have hmon : D.Monic := monic_prod_of_monic _ _ (fun i _ => mon i)
  have hq' := div_modByMonic_unique (f:=F) q Z hmon ⟨by simpa [Z,D,g,others,add_comm,mul_comm] using eqn.symm,hZ⟩
  have hq : q=0 := hq'.1.symm.trans ((divByMonic_eq_zero_iff hmon).mpr ((hdeg s).symm ▸ hF))
  exact ⟨B,hB',by simpa [hq,Z,g,others] using eqn⟩

theorem local_divisibility (s : Finset ι) (r : ι → ℚ) (m : ι → ℕ) (B : ι → ℚ[X])
    (t : ι) (ht : t ∈ s) : power r m t ∣ (∑ i ∈ s, B i*others s r m i) - B t*others s r m t := by
  rw [← Finset.add_sum_erase s (fun i => B i*others s r m i) ht,add_sub_cancel_left]
  apply Finset.dvd_sum
  intro i hi
  apply dvd_mul_of_dvd_right _ _
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hi).symm,ht⟩)
end DetDLP.HermitePartialFractions
end

section
namespace DetDLP.ScaledHermiteBasis
open Polynomial Finset HermitePartialFractions
variable {I : Type*} [DecidableEq I]
noncomputable def chart (r : I→ℚ) (c : ℚ) (i : I) : ℚ[X] := C (r i)+C c*X
theorem cardinal (s : Finset I) (r : I→ℚ) (hr : Function.Injective r) (c : ℚ) (hc : c≠0) (m : I→ℕ)
    (t : I) (ht : t∈s) (j : ℕ) :
    ∃ H : ℚ[X], H.degree < ((∑ i∈s,m i:ℕ):WithBot ℕ) ∧
      ∀ i∈s,∀ d < m i,(H.comp (chart r c i)).coeff d=if i=t ∧ d=j then 1 else 0 := by
  classical
  let g := power r m
  let P := ∏ i∈s,g i
  let B := others s r m t
  let L := (C c⁻¹*(X-C (r t)))^j
  have mon : P.Monic := monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C _).pow _)
  have cop : IsCoprime B (g t) := by
    apply IsCoprime.prod_left
    intro i hi
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hr.ne (ne_of_mem_erase hi))).isUnit).pow
  obtain ⟨u,v,hh⟩ := cop
  let A := u*B*L
  let H := A %ₘ P
  refine ⟨H,?_,?_⟩
  · have deg (i : I) : (g i).degree=(m i:ℕ) := by simp [g,power,degree_pow]
    have dP : P.degree=((∑ i∈s,m i:ℕ):WithBot ℕ) := by simp only [P,degree_prod,deg,Nat.cast_sum]
    exact (degree_modByMonic_lt _ mon).trans_eq dP
  · intro i hi d hd
    have loc : g i ∣ A-(if i=t then L else 0) := by
      by_cases e : i=t
      · subst i; rw [if_pos rfl]
        refine ⟨-(v*L),?_⟩; dsimp only [A]; linear_combination L*hh
      · rw [if_neg e,sub_zero]
        have db : g i∣B := Finset.dvd_prod_of_mem _ (mem_erase.mpr ⟨e,hi⟩)
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right db _) _
    have rem : P ∣ H-A := by
      refine ⟨-(A /ₘ P),?_⟩; rw [show H=A %ₘ P from rfl,modByMonic_eq_sub_mul_div]; ring
    have dl := ((Finset.dvd_prod_of_mem g hi).trans rem).add loc
    rw [sub_add_sub_cancel] at dl
    obtain ⟨Z,hZ⟩ := dl
    have pcomp : (g i).comp (chart r c i)=(C c*X)^(m i) := by simp [g,power,chart,pow_comp]
    have dw : X^(m i) ∣ (H.comp (chart r c i))-((if i=t then L else 0).comp (chart r c i)) := by
      rw [← sub_comp,hZ,mul_comp,pcomp,mul_pow]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hz := X_pow_dvd_iff.mp dw d hd
    rw [coeff_sub,sub_eq_zero] at hz; rw [hz]
    by_cases e : i=t
    · subst i; have hL : L.comp (chart r c t)=X^j := by
        simp [L,chart,pow_comp,mul_comp,sub_comp,← mul_assoc,← map_mul,hc]
      simp only [if_pos rfl,hL,true_and,coeff_X_pow]; split_ifs <;> simp_all
    · simp [e]
end DetDLP.ScaledHermiteBasis
end

section

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
end

section

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
end

section

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

/-- The normalized cardinal polynomial in the local coordinate at t. -/
noncomputable def localFactor {k : ℕ} (r : Grid k → ℤ) (t : Grid k) (h u : ℕ) : ℚ[X] :=
  ∏ x ∈ nodes t, (1+C ((2:ℚ)^k / ((r t:ℚ)-(r x:ℚ)))*X)^(mult h u (level x))

theorem local_unit {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x) (t : Grid k) (h u : ℕ) :
    integral (localFactor r t h u) ∧ (localFactor r t h u).coeff 0 = 1 := by
  constructor
  · apply integral_prod; intro x hx; apply integral_pow; apply integral_add integral_one
    have hxt : x ≠ t := (by simpa [nodes] using hx : x ≠ t ∧ x ≠ 0).1
    have he : (((r t-r x:ℤ):Grid k)) = t-x := by simp [hr]
    have htx := sub_ne_zero.mpr hxt.symm
    have hz : (r t:ℚ)-(r x:ℚ) ≠ 0 := by exact_mod_cast (fun h => htx (he.symm.trans (by simp [h])) : r t-r x ≠ 0)
    have hc : Prec 0 ((2:ℚ)^k / ((r t:ℚ)-(r x:ℚ))) := by
      right; rw [padicValRat.div (by positivity) hz,padicValRat.pow,
        show padicValRat 2 (2:ℚ) = 1 from padicValRat.self (by decide : 1<2),
        ← Int.cast_sub,padicValRat.of_int,val_rep htx he,mul_one]
      have := level_lt htx; omega
    intro j; by_cases hj : j=1
    · simpa [hj] using hc
    · simp [coeff_C_mul,coeff_X,hj,Ne.symm hj,Prec]
  · rw [coeff_zero_eq_eval_zero,localFactor,eval_prod]; simp

/-- Triangular division by a series with 2-integral coefficients and constant term one
preserves the precision of every retained jet. -/
theorem cancel_unit {E H : ℚ[X]} (he : integral E) (h0 : E.coeff 0=1) {n : ℕ} {p : ℤ}
    (hh : ∀ j < n, Prec p ((H*E).coeff j)) : ∀ j < n, Prec p (H.coeff j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    let s := Finset.HasAntidiagonal.antidiagonal j
    have hmem : (j,0) ∈ s := by simp [s]
    let g (z : ℕ × ℕ) := H.coeff z.1 * E.coeff z.2
    have htotal : (H*E).coeff j = H.coeff j + ∑ z ∈ s.erase (j,0), g z := by
      rw [coeff_mul,← Finset.add_sum_erase s g hmem]; simp [g,h0]
    have htail : Prec p (∑ z ∈ s.erase (j,0),g z) := by
      apply Prec.sum; intro z hz; obtain ⟨hneq,hz⟩ := mem_erase.mp hz
      have heq : z.1+z.2=j := Finset.HasAntidiagonal.mem_antidiagonal.mp hz
      have hlt : z.1 < j := by by_contra! hk; apply hneq; ext <;> simp <;> omega
      simpa [g] using (ih z.1 hlt (hlt.trans hj)).mul (he z.2)
    have hh' := (hh j hj).add htail.neg
    rwa [htotal,add_neg_cancel_right] at hh'

/-- Evaluation bound for a local quotient of degree smaller than its multiplicity. -/
theorem summand_precision {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x)
    {t : Grid k} (ht : t ≠ 0) (h u : ℕ) (p : ℤ) (H : ℚ[X])
    (hdeg : H.degree < (mult h u (level t):ℕ))
    (hjets : ∀ j < mult h u (level t),
      Prec (p+3*(2:ℤ)^(k-level t)*h+k*(mult h u (level t):ℤ)) ((H*localFactor r t h u).coeff j)) :
    Prec p (atOrigin r t h u * H.eval (-(r t:ℚ)/(2:ℚ)^k)) := by
  let n := mult h u (level t)
  let loss := 3*(2:ℤ)^(k-level t)*h
  have ew : Prec (-loss) (atOrigin r t h u) := Or.inr (origin_bound r hr ht h u)
  have hp (x : ℤ) : Prec (-(k:ℤ)) (-(x:ℚ)/(2:ℚ)^k) := by
    by_cases hz : x=0
    · simp [hz,Prec]
    · right; rw [padicValRat.div (neg_ne_zero.mpr (by exact_mod_cast hz)) (by positivity),padicValRat.neg,
        padicValRat.pow,show padicValRat 2 (2:ℚ) = 1 from padicValRat.self (by decide : 1<2),padicValRat.of_int,mul_one]
      omega
  have hu := local_unit r hr t h u
  have hc := cancel_unit hu.1 hu.2 hjets
  by_cases hz : H=0
  · simp [hz,Prec]
  have hn : H.natDegree < n := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hdeg
  rw [eval_eq_sum_range' hn,mul_sum]
  apply Prec.sum; intro j hj
  have hj' := mem_range.mp hj
  have hjn : (j:ℤ) ≤ n := by exact_mod_cast hj'.le
  have hn' := mul_le_mul_of_nonneg_left hjn (Int.natCast_nonneg k)
  apply Prec.mono _ (ew.mul ((hc j hj').mul ((hp (r t)).pow j)))
  dsimp [loss,n] at *; nlinarith only [hn']
end DetDLP.DyadicGrid
end

section

namespace DetDLP.DyadicGrid
open Finset Polynomial HermitePartialFractions

noncomputable def coord {k : ℕ} (r : Grid k → ℤ) (t : Grid k) : ℚ[X] := C (r t:ℚ) + C ((2:ℚ)^k)*X

private theorem other_local {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x)
    (t : Grid k) (h u : ℕ) :
    let R (x : Grid k) : ℚ := r x
    let m (x : Grid k) := mult h u (level x)
    let d := ∏ x ∈ nodes t, (R t-R x)^(m x)
    let B := others (univ.erase 0) R m t
    B.comp (coord r t) = C d * localFactor r t h u ∧
      B.eval 0 = d * atOrigin r t h u := by
  intro R m d B
  have hn (x : Grid k) (hx : x ∈ nodes t) : R t-R x ≠ 0 := by
    have hd : x ≠ t := (show x≠t ∧ x≠0 by simpa [nodes] using hx).1
    apply sub_ne_zero.mpr; intro he
    have he' : r t = r x := by dsimp [R] at he; exact_mod_cast he
    exact hd (by rw [← hr x,← hr t,he'])
  constructor
  · change (∏ x ∈ nodes t, power R m x).comp (coord r t) = C (∏ x ∈ nodes t,(R t-R x)^(m x)) * _
    rw [Polynomial.prod_comp,map_prod,localFactor,← prod_mul_distrib]; apply prod_congr rfl; intro x hx
    rw [map_pow,← mul_pow]; unfold power; rw [pow_comp,sub_comp,X_comp,C_comp]
    apply congrArg (fun z : ℚ[X] => z^(m x))
    have hh : C (R t-R x) * C ((2:ℚ)^k / (R t-R x)) = C ((2:ℚ)^k) := by
      rw [← map_mul]; congr 1; field_simp [hn x hx]
    change C (R t) + C ((2:ℚ)^k)*X - C (R x) =
      C (R t-R x) * (1+C ((2:ℚ)^k/(R t-R x))*X)
    rw [mul_add,mul_one,← mul_assoc,hh,map_sub]; ring
  · change (∏ x ∈ nodes t, power R m x).eval 0 = (∏ x ∈ nodes t, (R t-R x)^(m x)) * _
    rw [eval_prod,atOrigin,← prod_mul_distrib]; apply prod_congr rfl; intro x hx
    simp only [power,eval_pow,eval_sub,eval_X,eval_C,zero_sub]
    rw [← mul_pow]; apply congrArg (fun z : ℚ => z^(m x))
    change -R x = (R t-R x)*(-R x/(R t-R x)); field_simp [hn x hx]

/-- Node-dependent precision for every rational polynomial below the Hermite degree threshold. -/
theorem recovery {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x) (h u : ℕ)
    (p : ℤ) (F : ℚ[X]) (hdeg : F.degree < ((∑ t ∈ (univ.erase (0:Grid k)),mult h u (level t) : ℕ):WithBot ℕ))
    (jets : ∀ t : Grid k, t ≠ 0 → ∀ j < mult h u (level t),
      Prec (p+3*(2:ℤ)^(k-level t)*h+k*(mult h u (level t):ℤ)) ((F.comp (coord r t)).coeff j)) :
    Prec p (F.eval 0) := by
  let S : Finset (Grid k) := univ.erase 0
  let R (x : Grid k) : ℚ := r x
  let m (x : Grid k) := mult h u (level x)
  have hin : Function.Injective R := by
    intro a b hab
    have he : r a = r b := by dsimp [R] at hab; exact_mod_cast hab
    rw [← hr a,← hr b,he]
  obtain ⟨B,hB,hF⟩ := decompose S R hin m F hdeg
  conv => rhs; rw [hF,eval_finsetSum]
  apply Prec.sum; intro t ht
  have ht0 : t ≠ 0 := ne_of_mem_erase ht
  let E := others S R m t
  let d := ∏ x ∈ nodes t, (R t-R x)^(m x)
  let Q := coord r t
  let H := C d * (B t).comp Q
  obtain ⟨he,he0⟩ := other_local r hr t h u
  change E.comp Q = C d*localFactor r t h u at he
  change E.eval 0 = d*atOrigin r t h u at he0
  have eq : ((B t*E).comp Q) = H*localFactor r t h u := by rw [mul_comp,he]; dsimp only [H]; ring
  have hdvd : power R m t ∣ F-B t*E := hF ▸ local_divisibility S R m B t ht
  obtain ⟨A,hA⟩ := hdvd
  have hh : X^(m t) ∣ F.comp Q - H*localFactor r t h u := by
    rw [← eq,← sub_comp,hA,mul_comp]
    have hp : (power R m t).comp Q = ((C ((2:ℚ)^k))*X)^(m t) := by simp [power,Q,coord,R,pow_comp]
    rw [hp,mul_pow]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hj (j : ℕ) (hj : j < m t) : (H*localFactor r t h u).coeff j = (F.comp Q).coeff j := by
    have hz := X_pow_dvd_iff.mp hh j hj; rw [coeff_sub,sub_eq_zero] at hz; exact hz.symm
  have hH : H.degree < (m t:ℕ) := by
    by_cases hzero : B t=0
    · simp [H,hzero]
    have hb := (natDegree_lt_iff_degree_lt hzero).mpr (hB t ht)
    have hQ : Q.natDegree ≤ 1 := by
      exact natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))
    have hl : H.natDegree ≤ (B t).natDegree := (natDegree_C_mul_le ..).trans
      (natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left (B t).natDegree hQ))
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hl.trans_lt hb)
  have hp := summand_precision r hr ht0 h u p H hH (fun j hlt => by rw [hj j hlt]; exact jets t ht0 j hlt)
  have evQ : Q.eval (-(r t:ℚ)/(2:ℚ)^k) = 0 := by
    simp [Q,coord]; field_simp <;> ring
  change Prec p ((B t*E).eval 0)
  rw [eval_mul,he0]; dsimp only [H] at hp
  rw [eval_mul,eval_C,eval_comp,evQ] at hp
  convert hp using 1 <;> ring
end DetDLP.DyadicGrid
end

section

namespace DetDLP.TaperedHermiteWeights
open Finset Polynomial DyadicGrid
def loss {k : ℕ} (h u : ℕ) (t : Grid k) : ℤ := 3*(2:ℤ)^(k-level t)*h+k*(mult h u (level t):ℤ)
theorem weights {k : ℕ} (r : Grid k→ℤ) (hr : ∀ x,((r x:ℤ):Grid k)=x) (h u : ℕ) :
    let S := univ.erase (0:Grid k)
    let m (x : Grid k) := mult h u (level x)
    ∃ w : (t : ↥S) → ℕ → ℚ,
      (∀ t j,Prec (-(loss h u t.val)) (w t j)) ∧
      ∀ F : ℚ[X], F.degree < ((∑ t∈S,m t:ℕ):WithBot ℕ) →
        F.eval 0=∑ t : ↥S,∑ j∈range (m t.val),w t j*(F.comp (coord r t.val)).coeff j := by
  classical
  intro S m
  let R (x : Grid k) : ℚ := r x
  have hin : Function.Injective R := by
    intro a b eq
    have e : r a=r b := by dsimp [R] at eq; exact_mod_cast eq
    rw [← hr a,← hr b,e]
  have C (t : ↥S) (j : ℕ) : ∃ H : ℚ[X],H.degree < ((∑ t∈S,m t:ℕ):WithBot ℕ) ∧
      ∀ v∈S,∀ d < m v,(H.comp (coord r v)).coeff d=if v=t.val ∧ d=j then 1 else 0 :=
    ScaledHermiteBasis.cardinal S R hin (2^k) (by positivity) m t.val t.property j
  choose B deg jets using C
  refine ⟨fun t j => (B t j).eval 0,?_,?_⟩
  · intro t j
    apply DyadicGrid.recovery r hr h u _ (B t j) (deg t j)
    intro v hv d hd
    rw [jets t j v (mem_erase.mpr ⟨hv,mem_univ _⟩) d hd]
    split_ifs with e
    · rcases e with ⟨rfl,rfl⟩
      simp only [Prec,padicValRat.one]; right; dsimp [loss]; omega
    · exact Or.inl rfl
  · intro F hF
    let coeff (t : ↥S) (j : ℕ) := (F.comp (coord r t.val)).coeff j
    let piece (t : ↥S) (j : ℕ) := Polynomial.C (coeff t j) * B t j
    let Q := ∑ t : ↥S,∑ j∈range (m t.val),piece t j
    let D := ((∑ t∈S,m t:ℕ):WithBot ℕ)
    have sum_lt {α : Type} (A : Finset α) (f : α→ℚ[X]) (hf : ∀ i∈A,(f i).degree<D) : (∑ i∈A,f i).degree<D :=
      (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr hf)
    have dq : Q.degree<D := by
      dsimp only [Q]; apply sum_lt; intro t _; apply sum_lt; intro j _
      dsimp only [piece]
      by_cases hx : coeff t j=0
      · rw [hx,map_zero,zero_mul,degree_zero]; exact WithBot.bot_lt_coe _
      · rw [degree_C_mul hx]; exact deg t j
    have agree (t : ↥S) (d : ℕ) (hd : d < m t.val) : (Q.comp (coord r t.val)).coeff d=coeff t d := by
      simp only [Q,Polynomial.sum_comp,finsetSum_coeff,piece,mul_comp,C_comp,coeff_C_mul]
      have eq (v : ↥S) (j : ℕ) : ((B v j).comp (coord r t.val)).coeff d=if t=v ∧ d=j then 1 else 0 := by
        rw [jets v j t.val t.property d hd]; simp only [Subtype.ext_iff]
      simp_rw [eq]
      rw [sum_eq_single t]
      · simp [hd]
      · intro v _ hv
        simp [Ne.symm hv]
      · simp
    let delta := F.eval 0-Q.eval 0
    have diff : (F-Q).degree<D := degree_sub_le _ _ |>.trans_lt (max_lt hF dq)
    have pd := DyadicGrid.recovery r hr h u (padicValRat 2 delta+1) (F-Q) diff (by
      intro v hv d hd
      left; rw [sub_comp,coeff_sub]
      have e := agree ⟨v,mem_erase.mpr ⟨hv,mem_univ _⟩⟩ d hd
      exact sub_eq_zero.mpr e.symm)
    rw [eval_sub] at pd
    change delta=0 ∨ padicValRat 2 delta+1≤padicValRat 2 delta at pd
    have same : F.eval 0=Q.eval 0 := sub_eq_zero.mp (pd.resolve_right (by omega))
    rw [same]; simp only [Q,eval_finsetSum,piece,eval_mul,eval_C]; apply sum_congr rfl;intro t _
    apply sum_congr rfl; intro j _; exact mul_comm _ _
end DetDLP.TaperedHermiteWeights
end

section

namespace DetDLP.DyadicGrid
open Finset

theorem available_jets (a h u : ℕ) :
    2^a*(h*u) ≤ ∑ t ∈ univ.erase (0:Grid (a+1)), h*(u-level t) := by
  let f (i : ℕ) := if i=0 then 0 else h*(u-padicValNat 2 i)
  have convertGrid (N : ℕ) [NeZero N] :
      ∑ x : ZMod N, f x.val = ∑ n ∈ range N, f n := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ N =>
      change (∑ x : Fin (N+1), f x.val) = _
      rw [Fin.sum_univ_eq_sum_range f]
  have split' (n : ℕ) :
      ∑ j ∈ range (2*n), f j = ∑ j ∈ range n, (f (2*j)+f (2*j+1)) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ,sum_range_succ,sum_range_succ,ih,sum_range_succ]; omega
  have hodd (n : ℕ) : f (2*n+1) = h*u := by
    have hv : padicValNat 2 (2*n+1)=0 := padicValNat.eq_zero_of_not_dvd (by omega)
    simp [f,hv]
  have hrange : 2^a*(h*u) ≤ ∑ n ∈ range (2^(a+1)), f n := by
    rw [pow_succ',split']
    calc
      _ = ∑ _j ∈ range (2^a), h*u := by simp
      _ ≤ _ := sum_le_sum fun n _ => by rw [hodd]; omega
  rw [← convertGrid] at hrange
  have hr := Finset.add_sum_erase (univ : Finset (Grid (a+1))) (fun x => f x.val) (mem_univ (0:Grid (a+1)))
  have h0 : f (0:Grid (a+1)).val = 0 := by simp [f]
  rw [h0,zero_add] at hr
  rw [← hr] at hrange
  apply hrange.trans_eq; apply sum_congr rfl; intro x hx
  have hne := ne_of_mem_erase hx
  have hv : x.val ≠ 0 := by intro h; apply hne; rw [← ZMod.natCast_zmod_val x,h]; simp
  simp [level,f,hv]

theorem enough_jets (a M h u : ℕ) (hM : 0 < M) (hu : 3*M ≤ h*u) :
    M*(2^(a+1)-1) < ∑ t ∈ univ.erase (0:Grid (a+1)), h*(u-level t) := by
  apply lt_of_lt_of_le _ (available_jets a h u)
  have hh := Nat.mul_le_mul_left (2^a) hu
  have hp : 0 < 2^a := by positivity
  have hle : M*(2^(a+1)-1) ≤ M*(2*2^a) := Nat.mul_le_mul_left M (by rw [pow_succ']; omega)
  nlinarith only [hh,hle,Nat.mul_pos hM hp]
end DetDLP.DyadicGrid
end

section
namespace DetDLP.TaperedAlgebraWeights
open Finset Polynomial DyadicGrid
theorem transfer {I : Type*} [Fintype I] (r : I→ℚ) (c : ℚ) (m : I→ℕ) (D : ℕ) (w : I→ℕ→ℚ)
    (hw : ∀ F : ℚ[X],F.natDegree≤D→F.eval 0=∑ t,∑ j∈range (m t),w t j*(F.comp (C (r t)+C c*X)).coeff j)
    {A : Type*} [CommRing A] [Algebra ℚ A] (F : A[X]) (hd : F.natDegree≤D) :
    F.eval 0=∑ t,∑ j∈range (m t),algebraMap ℚ A (w t j)*
      (F.comp (C (algebraMap ℚ A (r t))+C (algebraMap ℚ A c)*X)).coeff j := by
  classical
  let f := algebraMap ℚ A
  let E (t : I) := C (f (r t))+C (f c)*X
  let recover (H : A[X]) := ∑ t,∑ j∈range (m t),f (w t j)*(H.comp (E t)).coeff j
  have Hmono (k : ℕ) (hk : k≤D) : (0:A)^k=recover (X^k) := by
    have J := hw (X^k) (by simpa using hk)
    have h (t : I) (j : ℕ) : f (((X^k:ℚ[X]).comp (C (r t)+C c*X)).coeff j)=
        (((X^k:A[X]).comp (E t)).coeff j) := by
      rw [← coeff_map,map_comp]; simp [E]
    simpa only [eval_pow,eval_X,map_pow,map_zero,map_sum,map_mul,h,recover] using congrArg f J
  have Hmul (u : A) (H : A[X]) : recover (C u*H)=u*recover H := by
    unfold recover; simp only [mul_comp,C_comp,coeff_C_mul,mul_sum]
    apply sum_congr rfl; intro t _
    apply sum_congr rfl; intro j _;ring
  have Hsum (s : Finset ℕ) (H : ℕ → A[X]) : recover (∑ j∈s,H j)=∑ j∈s,recover (H j) := by
    have add (P Q : A[X]) : recover (P+Q)=recover P+recover Q := by
      simp [recover,add_comp,mul_add,sum_add_distrib]
    induction s using Finset.induction_on with
    | empty => simp [recover]
    | insert a s ha ih => simp only [sum_insert ha,add,ih]
  change F.eval 0=recover F
  have hs := F.as_sum_support_C_mul_X_pow
  calc
    _=(∑ j∈F.support,C (F.coeff j)*X^j).eval 0 := congrArg (eval 0) hs
    _=∑ j∈F.support,recover (C (F.coeff j)*X^j) := by
      rw [eval_finsetSum];apply sum_congr rfl;intro j hj
      simp only [eval_mul,eval_C,eval_pow,eval_X,Hmul]
      exact congrArg (F.coeff j*·) (Hmono j ((le_natDegree_of_mem_supp j hj).trans hd))
    _=recover F := (Hsum _ _).symm.trans (congrArg recover hs.symm)

theorem guarded (a M h u : ℕ) (hm : 0<M) (lo : 3*M≤h*u) (high : h*u≤4*M)
    (r : Grid (a+1)→ℤ) (hr : ∀ t,((r t:ℤ):Grid (a+1))=t) :
    let T := univ.erase (0:Grid (a+1))
    let m (t : ↥T) := mult h u (level t.val)
    ∃ w : ↥T→ℕ→ℚ, (∀ t j,Prec (-(6*(h:ℤ)*2^(a-level t.val)+4*M*(a+1))) (w t j)) ∧
      ∀ (A : Type) [CommRing A] [Algebra ℚ A] (F : A[X]),F.natDegree≤M*(2^(a+1)-1) →
        F.eval 0=∑ t : ↥T,∑ j∈range (m t),algebraMap ℚ A (w t j)*
          (F.comp (C (algebraMap ℚ A (r t.val:ℚ))+C (algebraMap ℚ A ((2:ℚ)^(a+1)))*X)).coeff j := by
  classical
  intro T m
  obtain ⟨w,hv,hw⟩ := TaperedHermiteWeights.weights r hr h u
  refine ⟨w,?_,?_⟩
  · intro t j
    apply (hv t j).mono
    have lv := level_lt (ne_of_mem_erase t.property)
    have ex : a+1-level t.val=(a-level t.val)+1 := by omega
    have multB : (mult h u (level t.val):ℤ)≤4*(M:ℤ) := by exact_mod_cast (Nat.mul_le_mul_left h (Nat.sub_le u _)).trans high
    unfold TaperedHermiteWeights.loss; rw [ex,pow_succ]
    have H := mul_le_mul_of_nonneg_left multB (show (0:ℤ)≤(a+1:ℕ) by positivity)
    push_cast at H ⊢; nlinarith only [H]
  · intro A _ _ F hd
    apply transfer (fun t : ↥T => (r t.val:ℚ)) ((2:ℚ)^(a+1)) m (M*(2^(a+1)-1)) w _ F hd
    intro f hf; apply hw
    have lim := hf.trans_lt (enough_jets a M h u hm lo)
    exact f.degree_le_natDegree.trans_lt (by exact_mod_cast lim)
end DetDLP.TaperedAlgebraWeights
end

open DetDLP Finset Polynomial

theorem solution (a M h u : ℕ) (hm : 0<M) (lo : 3*M≤h*u) (high : h*u≤4*M)
    (r : ZMod (2^(a+1))→ℤ) (hr : ∀ t,((r t:ℤ):ZMod (2^(a+1)))=t) :
    let T := univ.erase (0:ZMod (2^(a+1)))
    let v (t : ↥T) := padicValNat 2 t.val.val
    let m (t : ↥T) := h*(u-v t)
    ∃ w : ↥T→ℕ→ℚ, (∀ t j,w t j=0 ∨ -(6*(h:ℤ)*2^(a-v t)+4*M*(a+1))≤padicValRat 2 (w t j)) ∧
      ∀ (A : Type) [CommRing A] [Algebra ℚ A] (F : A[X]),F.natDegree≤M*(2^(a+1)-1) →
        F.eval 0=∑ t : ↥T,∑ j∈range (m t),algebraMap ℚ A (w t j)*
          (F.comp (C (algebraMap ℚ A (r t.val:ℚ))+C (algebraMap ℚ A ((2:ℚ)^(a+1)))*X)).coeff j := by
  exact TaperedAlgebraWeights.guarded a M h u hm lo high r hr
