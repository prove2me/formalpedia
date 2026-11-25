-- Prove2me | solution 1 for DetDLP.guard_cleared_finite_residual_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T19:20:22.829801+00:00
-- url     : https://prove2.me/submissions/68bba6bc-95cc-4706-8762-1af3f04f70c1

import Theorems.Thm_DetDLP_terminal_residual_expansion_over_a_prescribed_lattice
import Mathlib
import Definitions.Def_DetDLP_PacketKernel
import Definitions.Def_DetDLP_OrientedPacketInstance
import Theorems.Thm_DetDLP_guarded_recovery_from_actual_packet_samples
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_TerminalBTN
import Theorems.Thm_DetDLP_oriented_packet_slot_layout
import Theorems.Thm_DetDLP_terminal_packing_cell_bounds
import Definitions.Def_DetDLP_FactorBase

section
namespace DetDLP.MonicSpecialization
open Polynomial
variable {A B : Type} [CommRing A] [CommRing B]
variable (φ : A→+*B) {f : A[X]} {g : B[X]} (eq : f.map φ=g)
noncomputable def specialize : AdjoinRoot f→+*AdjoinRoot g :=
  AdjoinRoot.map φ f g (eq.symm ▸ dvd_refl g)

theorem spec_mk (q : A[X]) : specialize φ eq (AdjoinRoot.mk f q)=AdjoinRoot.mk g (q.map φ) := by
  rw [specialize,AdjoinRoot.map,AdjoinRoot.lift_mk,← Polynomial.eval₂_map,← AdjoinRoot.algebraMap_eq,← aeval_def,AdjoinRoot.aeval_eq]

theorem spec_constant (a : A) : specialize φ eq (algebraMap A (AdjoinRoot f) a)=algebraMap B (AdjoinRoot g) (φ a) := by
  change specialize φ eq (AdjoinRoot.mk f (C a))=AdjoinRoot.mk g (C (φ a))
  rw [spec_mk,Polynomial.map_C]

theorem natural (hf : f.Monic) (x : AdjoinRoot f) :
    (AdjoinRoot.modByMonicHom hf x).map φ=AdjoinRoot.modByMonicHom (eq ▸ hf.map φ) (specialize φ eq x) := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  rw [spec_mk,AdjoinRoot.modByMonicHom_mk,AdjoinRoot.modByMonicHom_mk,map_modByMonic φ hf,eq]

theorem surj (h : Function.Surjective φ) : Function.Surjective (specialize φ eq) := by
  intro y; obtain ⟨q,rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨p,rfl⟩ := Polynomial.map_surjective φ h q
  exact ⟨_,spec_mk φ eq p⟩

theorem inj (h : Function.Injective φ) (hf : f.Monic) : Function.Injective (specialize φ eq) := by
  intro x y e
  apply (AdjoinRoot.mk_leftInverse hf).injective
  apply Polynomial.map_injective φ h
  rw [natural φ eq hf,natural φ eq hf,e]

theorem kernel (hf : f.Monic) (r : A) (k : ℕ) (h : ∀ x,φ x = 0 → r^k∣x) (x : AdjoinRoot f) (hx : specialize φ eq x=0) :
    (algebraMap A (AdjoinRoot f) r)^k ∣ x := by
  let p := AdjoinRoot.modByMonicHom hf x
  have zero : p.map φ=0 := by rw [natural φ eq hf,hx,map_zero]
  have all : C (r^k)∣p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro n; apply h; rw [←coeff_map,zero,coeff_zero]
  obtain ⟨v,hv⟩ := all
  refine ⟨AdjoinRoot.mk f v,?_⟩
  calc
    x=AdjoinRoot.mk f p := (AdjoinRoot.mk_leftInverse hf x).symm
    _ = _ := by rw [hv,map_mul]; congr 1; rw [← map_pow]; rfl

end DetDLP.MonicSpecialization
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
end

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

private theorem eval_integral_prec (v : ℤ) (P : ℚ[X]) (hP : ∀ j, Prec v (P.coeff j))
    (x : ℚ) (hx : Prec 0 x) : Prec v (P.eval x) := by
  rw [eval_eq_sum_range]; apply Prec.sum; intro j hj; simpa using (hP j).mul (hx.pow j)

/-- Truncating the geometric packet expansion gives a real weighted row-to-tile
mode formula. Its degree-b coefficient has at least b+1 factors of two. -/
theorem tile_expansion {k : ℕ} (r : Grid k → ℤ) (hr : ∀ x, ((r x:ℤ):Grid k)=x) (h0 : r 0=0)
    (t d d₀ : Grid k) (hd : d≠t) (hd₀ : d₀≠t) (i j p : ℕ) (hp : 0 < p) (hi : level (t-d₀) ≤ i)
    (shift : r d-r d₀=(2:ℤ)^(i+1)*(j:ℤ)) (ζ : ℚ) (hz : Prec 0 ζ) :
    let S := univ.map (repEmbedding r hr)
    let T := (r t:ℚ)+(2:ℚ)^k*ζ
    let W (s : Grid k) := (shiftKernel S (r s:ℚ)).eval T
    let H := (2:ℚ)^(i+1)/(T-(r d₀:ℚ))
    (∀ b : ℕ, Prec ((b:ℤ)+1) (W d₀*H^b)) ∧
      Prec (p:ℤ) (W d-∑ b ∈ range (p-1),(W d₀*H^b)*(j:ℚ)^b) := by
  intro S T W H
  have ne0 := sub_ne_zero.mpr (Ne.symm hd₀)
  have he : ((r t-r d₀:ℤ):Grid k) = t-d₀ := by simp [hr]
  have hdiff : (r t:ℚ)-(r d₀:ℚ) ≠ 0 := by exact_mod_cast (fun h => ne0 (he.symm.trans (by simp [h])) : r t-r d₀ ≠ 0)
  have hval : padicValRat 2 ((r t:ℚ)-(r d₀:ℚ)) = (level (t-d₀):ℤ) := by rw [←Int.cast_sub,padicValRat.of_int,val_rep ne0 he]
  have hk : padicValRat 2 ((2:ℚ)^k) = k := by rw [padicValRat.pow,show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide : 1<2),mul_one]
  have hk' := level_lt ne0
  have hden : T-(r d₀:ℚ) ≠ 0 ∧ padicValRat 2 (T-(r d₀:ℚ)) = (level (t-d₀):ℤ) := by
    have ere : T-(r d₀:ℚ) = ((r t:ℚ)-(r d₀:ℚ))+(2:ℚ)^k*ζ := by dsimp [T]; ring
    rw [ere]
    rcases hz with hz0|hzp
    · simp [hz0,hdiff,hval]
    by_cases hζ : ζ=0
    · simp [hζ,hdiff,hval]
    have hβ : (2:ℚ)^k*ζ ≠ 0 := mul_ne_zero (by positivity) hζ
    have hbig : padicValRat 2 ((r t:ℚ)-(r d₀:ℚ)) < padicValRat 2 ((2:ℚ)^k*ζ) := by
      rw [padicValRat.mul (by positivity) hζ,hk,hval]; omega
    have hsum : (r t:ℚ)-(r d₀:ℚ)+(2:ℚ)^k*ζ ≠ 0 := by
      intro e; have hn := eq_neg_of_add_eq_zero_left e
      rw [hn,padicValRat.neg] at hbig; exact (lt_irrefl _ hbig)
    exact ⟨hsum,(padicValRat.add_eq_of_lt hsum hdiff hβ hbig).trans hval⟩
  have hH : Prec 1 H := by
    right; dsimp [H]; rw [padicValRat.div (by positivity) hden.1,padicValRat.pow,
      show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide : 1<2),mul_one,hden.2]; omega
  have hW (s : Grid k) (hs : s≠t) : Prec 1 (W s) := by
    have hh := local_kernel r hr h0 s t
    simp only [if_neg hs] at hh
    have he := eval_integral_prec _ _ hh ζ hz
    rw [eval_comp] at he
    dsimp only [W,S]
    rw [raw_matches r hr h0]
    simpa only [T,eval_add,eval_C,eval_mul,eval_X] using he.mono (scale_precision hs)
  have hco (b : ℕ) : Prec ((b:ℤ)+1) (W d₀*H^b) := by simpa [add_comm] using (hW d₀ hd₀).mul (hH.pow b)
  refine ⟨hco,?_⟩
  have identical (s : Grid k) : (T-(r s:ℚ))*W s =
      ((∏ x ∈ univ.erase (0:Grid k),-(r x:ℚ))⁻¹) * ∏ x : Grid k,(T-(r x:ℚ)) := by
    dsimp only [W,S]; rw [raw_matches r hr h0]
    simp only [rawKernel,eval_mul,eval_C,eval_prod,eval_sub,eval_X]
    rw [← Finset.mul_prod_erase univ (fun x : Grid k => T-(r x:ℚ)) (mem_univ s)]; ring
  let q := H*(j:ℚ)
  have eq : W d*(1-q)=W d₀ := by
    have hs' : (r d:ℚ)-(r d₀:ℚ)=(2:ℚ)^(i+1)*(j:ℚ) := by exact_mod_cast shift
    have hh := (identical d).trans (identical d₀).symm
    dsimp [q,H]; field_simp [hden.1]; linear_combination hh + W d*hs'
  have hsum (n : ℕ) : W d - ∑ b ∈ range n, (W d₀*H^b)*(j:ℚ)^b = W d*q^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,← sub_sub,ih,←eq,pow_succ]; dsimp [q]; rw [mul_pow]; ring
  rw [hsum]
  have hj : Prec 0 (j:ℚ) := Or.inr (zero_le_padicValRat_of_nat j)
  have hq : Prec 1 q := by simpa [q] using hH.mul hj
  apply Prec.mono _ ((hW d hd).mul (hq.pow (p-1))); omega
end DetDLP.DyadicGrid
end

section

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
end

section
namespace DetDLP.LocalBinaryReduction
open DyadicGrid
abbrev O := localRing

theorem oddDen (x : O) : ¬2 ∣ (x:ℚ).den := by
  have u := (PadicInt.isUnit_den (x:ℚ) (toPadic x).property).map (PadicInt.toZMod : ℤ_[2]→+*ZMod 2)
  simp only [map_natCast] at u
  intro h
  have hz := (ZMod.natCast_eq_zero_iff ..).mpr h
  exact u.ne_zero hz

theorem integer (z : ℤ) : Prec 0 (z:ℚ) := by
  right; simp
theorem inverseDen (x : O) : Prec 0 (((x:ℚ).den:ℚ)⁻¹) := by
  right; rw [padicValRat.inv,←padicValRat_of_nat,padicValNat.eq_zero_of_not_dvd (oddDen x)]; simp

theorem ker (p : ℕ) (x : O) (hx : reduceAt p x=0) : (2:O)^p∣x := by
  have num := reduce_fraction p x
  rw [hx,zero_mul] at num
  have dvd := (ZMod.intCast_zmod_eq_zero_iff_dvd (x:ℚ).num (2^p)).mp num.symm
  obtain ⟨z,hz⟩ := dvd
  let y : O := ⟨(z:ℚ)*((x:ℚ).den:ℚ)⁻¹,by change Prec 0 _; simpa using (integer z).mul (inverseDen x)⟩
  refine ⟨y,?_⟩
  apply Subtype.ext
  change (x:ℚ)=(2:ℚ)^p*((z:ℚ)*((x:ℚ).den:ℚ)⁻¹)
  have hn : ((x:ℚ).num:ℚ)=(2:ℚ)^p*(z:ℚ) := by exact_mod_cast hz
  have hd : ((x:ℚ).den:ℚ)≠0 := by exact_mod_cast (x:ℚ).den_nz
  apply (mul_left_inj' hd).mp
  rw [Rat.mul_den_eq_num,hn]
  field_simp

theorem onto (p : ℕ) : Function.Surjective (reduceAt p) := by
  intro x
  exact ⟨(x.val:O),(map_natCast _ x.val).trans (ZMod.natCast_zmod_val x)⟩
end DetDLP.LocalBinaryReduction
end

section

namespace DetDLP.FiniteJetInterpolation
open Finset Polynomial Matrix
open scoped Polynomial

/-- The weights use only the single grid, and work for every polynomial over the
same coefficient ring (including nilpotent coefficient rings). -/
theorem reconstruct {A : Type*} [CommRing A] (N : ℕ) (v : Fin N → A)
    (hv : ∀ i j,i ≠ j → IsUnit (v i-v j)) :
    ∃ w : Fin N → Fin N → A, ∀ f : A[X], f.natDegree < N →
      ∀ i : Fin N, f.coeff i.val=∑ j,w i j*f.eval (v j) := by
  classical
  let V := vandermonde v
  have units (s : Finset (Fin N)) (f : Fin N → A) (h : ∀ i∈s, IsUnit (f i)) : IsUnit (∏ i∈s,f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]; exact (h _ (by simp)).mul (ih (fun i hi => h _ (by simp [hi])))
  have unit : IsUnit V.det := by
    rw [show V.det=(vandermonde v).det from rfl,det_vandermonde]
    apply units; intro i _
    apply units; intro j hj
    exact hv j i (Finset.mem_Ioi.mp hj).ne'
  refine ⟨(V⁻¹ : Matrix (Fin N) (Fin N) A),?_⟩
  intro f hf i
  let coeffs (j : Fin N) := f.coeff j.val
  have hval : (fun i => f.eval (v i))=V.mulVec coeffs := by
    funext j
    change f.eval₂ (RingHom.id _) (v j) = ∑ k : Fin N,(v j)^k.val*f.coeff k.val
    rw [eval₂_eq_sum_range' _ hf]
    simpa only [RingHom.id_apply,mul_comm] using
      (Fin.sum_univ_eq_sum_range (fun k => (v j)^k*f.coeff k) N).symm
  have eq : V⁻¹.mulVec (fun j => f.eval (v j))=coeffs := by
    rw [hval,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ unit,Matrix.one_mulVec]
  exact (congrFun eq i).symm

abbrev FieldAt (κ : ℕ) := GaloisField 2 κ
abbrev RingAt (p κ : ℕ) := TruncatedWittVector 2 p (FieldAt κ)

noncomputable def sample {κ : ℕ} (p : ℕ) (x : FieldAt κ) : RingAt p κ :=
  WittVector.truncate p (WittVector.teichmuller 2 x)

theorem unit_diff {κ p : ℕ} {x y : FieldAt κ} (h : x≠y) : IsUnit (sample p x-sample p y) := by
  rw [sample,sample,← map_sub]
  apply RingHom.isUnit_map
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  change WittVector.constantCoeff (WittVector.teichmuller 2 x-WittVector.teichmuller 2 y)≠0
  simpa only [map_sub,WittVector.constantCoeff_apply,WittVector.teichmuller_coeff_zero,sub_ne_zero] using h

theorem two_zero (p κ : ℕ) : (2:RingAt p κ)^p=0 := by
  have eq : (2:RingAt p κ)^p=WittVector.truncate p ((2:WittVector 2 (FieldAt κ))^p) := by rw [map_pow]; congr 1
  rw [eq]; ext i
  rw [WittVector.coeff_truncate,TruncatedWittVector.coeff_zero]
  exact WittVector.coeff_p_pow_eq_zero 2 (FieldAt κ) i.isLt.ne

noncomputable def baseHom (p κ : ℕ) : ZMod (2^p) →+* RingAt p κ :=
  ZMod.castHom (m:=ringChar (RingAt p κ)) (ringChar.dvd (by simpa using two_zero p κ)) _

theorem characteristic (p κ : ℕ) : ringChar (RingAt p κ)=2^p := by
  have d : ringChar (RingAt p κ) ∣ 2^p := ringChar.dvd (by simpa using two_zero p κ)
  obtain ⟨i,hip,hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp d
  have h : (2:RingAt p κ)^i=0 := by
    have eq : ((ringChar (RingAt p κ):ℕ):RingAt p κ)=0 := ringChar.Nat.cast_ringChar
    rw [hi] at eq; simpa using eq
  have E := TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero 2 p (FieldAt κ) i hip h
  simpa only [E] using hi

theorem base_injective (p κ : ℕ) : Function.Injective (baseHom p κ) := by
  haveI := ringChar.of_eq (characteristic p κ)
  have eq : baseHom p κ=ZMod.castHom (dvd_refl (2^p)) (RingAt p κ) := by
    apply RingHom.ext_zmod
  rw [eq]; apply ZMod.castHom_injective

theorem size (p κ : ℕ) (hk : 0 < κ) : Nat.card (RingAt p κ)=2^(κ*p) := by
  letI := Fintype.ofFinite (FieldAt κ)
  rw [Nat.card_eq_fintype_card,TruncatedWittVector.card,← Nat.card_eq_fintype_card,GaloisField.card _ _ hk.ne',pow_mul]

theorem tower_compat {κ p q : ℕ} (h : q≤p) (x : FieldAt κ) :
    TruncatedWittVector.truncate h (sample p x)=sample q x := by
  exact TruncatedWittVector.truncate_wittVector_truncate h _

theorem interpolate_tower (κ : ℕ) (hκ : 0 < κ) (N : ℕ) (hN : N ≤ 2^κ) :
    ∃ grid : (p : ℕ) → Fin N → RingAt p κ,
      (∀ p q (h : q≤p) i,TruncatedWittVector.truncate h (grid p i)=grid q i) ∧
      (∀ p, (2:RingAt p κ)^p=0) ∧
      (∀ p,∃ w : Fin N → Fin N → RingAt p κ, ∀ f : Polynomial (RingAt p κ),f.natDegree < N →
        ∀ i : Fin N,f.coeff i.val=∑ j,w i j*f.eval (grid p j)) := by
  classical
  letI := Fintype.ofFinite (FieldAt κ)
  have H : Fintype.card (FieldAt κ)=2^κ := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 κ hκ.ne'
  let emb : Fin N ↪ FieldAt κ := (Fin.castLEEmb (hN.trans_eq H.symm)).trans (Fintype.equivFin (FieldAt κ)).symm.toEmbedding
  exact ⟨fun p i => sample p (emb i),fun p q h i => tower_compat h _,fun p => two_zero p κ,
    fun p => reconstruct N _ (fun i j h => unit_diff (emb.injective.ne h))⟩
end DetDLP.FiniteJetInterpolation
end

section
namespace DetDLP.BinaryExtensionGrid
open Polynomial Finset
open scoped Polynomial IntermediateField
abbrev F2 := ZMod 2
abbrev mod2 := Int.castRingHom F2
noncomputable def low {κ : ℕ} (x : Fin κ→F2) : ℤ[X] := ∑ i,monomial i.val ((x i).val:ℤ)
theorem low_coeff {κ : ℕ} (x : Fin κ→F2) (d : ℕ) :
    (low x).coeff d = if h : d<κ then ((x ⟨d,h⟩).val:ℤ) else 0 := by
  classical
  rw [low,finsetSum_coeff]
  by_cases hd : d<κ
  · rw [dif_pos hd,sum_eq_single (⟨d,hd⟩:Fin κ)]
    · simp
    · intro j hj h; rw [coeff_monomial,if_neg (fun e => h (Fin.ext e))]
    · simp
  · rw [dif_neg hd]; apply sum_eq_zero; intro i _; rw [coeff_monomial,if_neg (by have := i.isLt; omega)]
theorem low_degree {κ : ℕ} (x : Fin κ→F2) : (low x).degree < (κ:WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr; intro d hd; simp [low_coeff,not_lt_of_ge hd]
theorem residue {κ : ℕ} (x : Fin κ→F2) (j : Fin κ) : ((low x).map mod2).coeff j.val=x j := by
  rw [coeff_map,low_coeff,dif_pos j.isLt]; simp [mod2]
theorem modulus (κ : ℕ) (hκ : 0<κ) : ∃ x : Fin κ→F2,
    let f := (X:ℤ[X])^κ+low x
    f.Monic ∧ f.natDegree=κ ∧ Irreducible (f.map mod2) := by
  classical
  let K := GaloisField 2 κ
  obtain ⟨a,ha⟩ := Field.exists_primitive_element F2 K
  have intA : IsIntegral F2 a := IsIntegral.of_finite _ _
  let m := minpoly F2 a
  have hm : m.Monic := minpoly.monic intA
  have hd : m.natDegree=κ := by
    have f := IntermediateField.adjoin.finrank intA
    rw [ha,IntermediateField.finrank_top',GaloisField.finrank 2 hκ.ne'] at f
    exact f.symm
  let x : Fin κ→F2 := fun i => m.coeff i.val
  refine ⟨x,?_⟩; intro f
  have lt := low_degree x
  have mon := (monic_X_pow κ (R:=ℤ)).add_of_left (show (low x).degree < ((X:ℤ[X])^κ).degree by simpa using lt)
  have eq : f.map mod2=m := by
    ext d; change (((X:ℤ[X])^κ+low x).map mod2).coeff d=_
    rw [Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,coeff_add]
    rcases lt_trichotomy d κ with l|e|g
    · rw [coeff_X_pow,if_neg (by omega),zero_add]; exact residue x ⟨d,l⟩
    · subst d
      rw [coeff_map,low_coeff,dif_neg (by omega),map_zero,add_zero,coeff_X_pow]
      simpa [← hd] using hm.coeff_natDegree.symm
    · rw [coeff_X_pow,if_neg (by omega),coeff_map,low_coeff,dif_neg (by omega),map_zero,add_zero,coeff_eq_zero_of_natDegree_lt (hd.trans_lt g)]
  refine ⟨mon,?_,eq ▸ minpoly.irreducible intA⟩
  rw [← hd,← eq,mon.natDegree_map]
theorem unit_eval {p : ℕ} {R : Type*} [CommRing R] (hn : (2:R)^p=0) (z : R) (f g : ℤ[X])
    (zeroF : aeval z f=0) (cp : IsCoprime (g.map mod2) (f.map mod2)) : IsUnit (aeval z g) := by
  obtain ⟨u,v,h⟩ := cp
  have surj : Function.Surjective (Polynomial.map mod2) := Polynomial.map_surjective _ (ZMod.intCast_surjective)
  obtain ⟨U,rfl⟩ := surj u; obtain ⟨V,rfl⟩ := surj v
  let A := U*g+V*f-1
  have eq : A.map mod2=0 := by simp [A,h]
  have hd : C (2:ℤ)∣A := by
    apply (C_dvd_iff_dvd_coeff ..).mpr; intro n
    have E := congrArg (fun p : F2[X] => p.coeff n) eq
    simp only [coeff_map,coeff_zero] at E
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp E
  obtain ⟨H,hH⟩ := hd
  have hv := congrArg (aeval z : ℤ[X]→ₐ[ℤ] R) hH
  simp only [A,map_sub,map_add,map_mul,map_one,zeroF,mul_zero,add_zero,aeval_C,eq_intCast] at hv
  have two : (aeval z : ℤ[X]→ₐ[ℤ] R) (2:ℤ[X])=2 := map_ofNat _ _
  norm_num at hv
  rw [two] at hv
  have nil : IsNilpotent ((2:R)*aeval z H) := ⟨p,by rw [mul_pow,hn,zero_mul]⟩
  have unit : IsUnit (aeval z U*aeval z g) := by
    rw [show aeval z U*aeval z g=2*aeval z H+1 by linear_combination hv]; exact nil.isUnit_add_one
  exact isUnit_of_mul_isUnit_right unit
end DetDLP.BinaryExtensionGrid
end

section

namespace DetDLP.DenseBinaryGrid
open Polynomial Finset BinaryExtensionGrid
abbrev base (p : ℕ) := ZMod (2^p)
noncomputable abbrev fp (f : ℤ[X]) (p : ℕ) := f.map (Int.castRingHom (base p))
abbrev ext (f : ℤ[X]) (p : ℕ) := AdjoinRoot (fp f p)
noncomputable def sample {κ : ℕ} (f : ℤ[X]) (p : ℕ) (x : Fin κ→F2) : ext f p :=
  aeval (AdjoinRoot.root (fp f p)) (low x)

theorem nil (f : ℤ[X]) (p : ℕ) : (2:ext f p)^p=0 := by
  have e : (2:base p)^p=0 := by
    rw [← Nat.cast_ofNat (R:=base p) (n:=2),← Nat.cast_pow]; exact ZMod.natCast_self _
  simpa only [map_pow,map_ofNat,map_zero] using congrArg (algebraMap (base p) (ext f p)) e

theorem zero (f : ℤ[X]) (p : ℕ) : aeval (AdjoinRoot.root (fp f p)) f=0 := by
  rw [AdjoinRoot.aeval_eq_of_algebra]
  exact AdjoinRoot.mk_self

theorem units {κ : ℕ} (f : ℤ[X]) (hf : f.Monic) (hd : f.natDegree=κ)
    (ir : Irreducible (f.map mod2)) (p : ℕ) {x y : Fin κ→F2} (hne : x≠y) :
    IsUnit (sample f p x-sample f p y) := by
  let g := low x-low y
  have nz : g.map mod2≠0 := by
    intro eq; apply hne; funext j
    have e := congrArg (fun q : F2[X] => q.coeff j.val) eq
    simp only [g,Polynomial.map_sub,coeff_sub,residue,coeff_zero,sub_eq_zero] at e
    exact e
  have lt : (g.map mod2).degree < (f.map mod2).degree := by
    rw [hf.degree_map,degree_eq_natDegree hf.ne_zero,hd]
    exact degree_map_le.trans_lt ((degree_sub_le ..).trans_lt (max_lt (low_degree x) (low_degree y)))
  have nd : ¬(f.map mod2)∣(g.map mod2) := (hf.map _).not_dvd_of_degree_lt nz lt
  have u := unit_eval (nil f p) (AdjoinRoot.root (fp f p)) f g (zero f p) ((ir.isCoprime_or_dvd _).resolve_right nd).symm
  change IsUnit ((aeval (AdjoinRoot.root (fp f p)) : ℤ[X]→ₐ[ℤ] ext f p) (low x) - (aeval (AdjoinRoot.root (fp f p)) : ℤ[X]→ₐ[ℤ] ext f p) (low y))
  rw [← map_sub]; exact u

theorem interpolate {κ : ℕ} (f : ℤ[X]) (hf : f.Monic) (hd : f.natDegree=κ)
    (ir : Irreducible (f.map mod2)) (N : ℕ) (hN : N≤2^κ) :
    ∃ emb : Fin N ↪ (Fin κ→F2),∀ p,∃ w : Fin N→Fin N→ext f p,
      ∀ F : Polynomial (ext f p),F.natDegree<N→∀ i : Fin N,
      F.coeff i.val=∑ j,w i j*F.eval (sample f p (emb j)) := by
  classical
  have card : Fintype.card (Fin κ→F2)=2^κ := by simp [F2]
  let e := (Fin.castLEEmb (hN.trans_eq card.symm)).trans (Fintype.equivFin (Fin κ→F2)).symm.toEmbedding
  exact ⟨e,fun p => FiniteJetInterpolation.reconstruct N _ (fun _ _ h => units f hf hd ir p (e.injective.ne h))⟩
end DetDLP.DenseBinaryGrid
end

section

namespace DetDLP.CanonicalGridCoordinates
open Polynomial Finset BinaryExtensionGrid DenseBinaryGrid

noncomputable def lower {p q : ℕ} (h : q≤p) : base p →+* base q :=
  ZMod.castHom (pow_dvd_pow 2 h) _

theorem mapped (f : ℤ[X]) {p q : ℕ} (h : q≤p) :
    (fp f p).map (lower h)=fp f q := by
  rw [fp,Polynomial.map_map]
  congr 1
  apply RingHom.ext_int

noncomputable def reduce (f : ℤ[X]) {p q : ℕ} (h : q≤p) : ext f p →+* ext f q :=
  AdjoinRoot.map (lower h) _ _ ((mapped f h).symm ▸ dvd_refl _)

theorem reduce_mk (f : ℤ[X]) {p q : ℕ} (h : q≤p) (g : (base p)[X]) :
    reduce f h (AdjoinRoot.mk _ g)=AdjoinRoot.mk _ (g.map (lower h)) := by
  rw [reduce,AdjoinRoot.map,AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← aeval_def,AdjoinRoot.aeval_eq]

theorem coherent (f : ℤ[X]) {κ p q : ℕ} (h : q≤p) (x : Fin κ→F2) :
    reduce f h (sample f p x)=sample f q x := by
  simp only [sample,AdjoinRoot.aeval_eq_of_algebra,reduce_mk]
  rw [Polynomial.map_map]
  congr 2
  apply RingHom.ext_int

noncomputable def normal (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (x : ext f p) : (base p)[X] :=
  AdjoinRoot.modByMonicHom (hf.map _) x
noncomputable def word (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (x : ext f p) (i : Fin f.natDegree) : ℕ :=
  ((normal f hf p x).coeff i.val).val
noncomputable def liftWord (f : ℤ[X]) (w : Fin f.natDegree→ℕ) : ℤ[X] :=
  ∑ i,monomial i.val (w i:ℤ)
theorem word_lt (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (x : ext f p) (i : Fin f.natDegree) :
    word f hf p x i<2^p := ZMod.val_lt _

theorem normalized {f : ℤ[X]} (hf : f.Monic) {p : ℕ} (hp : 0<p) (x : ext f p) :
    fp (liftWord f (word f hf p x)) p=normal f hf p x := by
  haveI : Fact (1<2^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have degree : (normal f hf p x).degree<(f.natDegree: WithBot ℕ) := by
    obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective x
    rw [normal,AdjoinRoot.modByMonicHom_mk,← hf.natDegree_map (Int.castRingHom (base p)),
      ← degree_eq_natDegree (hf.map (Int.castRingHom (base p))).ne_zero]
    exact degree_modByMonic_lt _ (hf.map _)
  ext d
  rw [fp,liftWord,Polynomial.map_sum,finsetSum_coeff]
  by_cases H : d<f.natDegree
  · rw [sum_eq_single (⟨d,H⟩:Fin f.natDegree)]
    · simp [word]
    · intro j _ hj; simp [coeff_monomial,show j.val≠d from fun t => hj (Fin.ext t)]
    · simp
  · rw [sum_eq_zero (fun j _ => ?_), (degree_lt_iff_coeff_zero ..).mp degree d (Nat.le_of_not_gt H)]
    simp [coeff_monomial,show j.val≠d by have := j.isLt; omega]

theorem decode {f : ℤ[X]} (hf : f.Monic) {p : ℕ} (hp : 0<p) (x : ext f p) :
    aeval (AdjoinRoot.root (fp f p)) (liftWord f (word f hf p x))=x := by
  rw [AdjoinRoot.aeval_eq_of_algebra]
  change AdjoinRoot.mk _ (fp _ p)=x
  rw [normalized hf hp]
  exact AdjoinRoot.mk_leftInverse (hf.map _) _

theorem lift_again {f : ℤ[X]} (hf : f.Monic) {p q : ℕ} (hp : 0<p) (h : p≤q) (x : ext f p)
    (i : Fin f.natDegree) :
    word f hf q (aeval (AdjoinRoot.root (fp f q)) (liftWord f (word f hf p x))) i=word f hf p x i := by
  haveI : Fact (1<2^q) := ⟨one_lt_pow₀ (by decide) (hp.trans_le h).ne'⟩
  let g := liftWord f (word f hf p x)
  have d : g.degree<(f.natDegree:WithBot ℕ) := by
    unfold g liftWord; simp_rw [← C_mul_X_pow_eq_monomial]; exact degree_sum_fin_lt _
  have lt : (fp g q).degree<(fp f q).degree := by
    rw [hf.degree_map,degree_eq_natDegree hf.ne_zero]; exact degree_map_le.trans_lt d
  rw [AdjoinRoot.aeval_eq_of_algebra]
  change ((normal f hf q (AdjoinRoot.mk _ (fp g q))).coeff i.val).val=_
  rw [normal,AdjoinRoot.modByMonicHom_mk,(modByMonic_eq_self_iff (hf.map _)).mpr lt,fp]
  dsimp only [g]
  rw [liftWord,
    Polynomial.map_sum,finsetSum_coeff,sum_eq_single i]
  · simpa using ZMod.val_natCast_of_lt ((word_lt f hf p x i).trans_le (Nat.pow_le_pow_right (by decide) h))
  · intro j _ ne; simp [coeff_monomial,show j.val≠i.val from fun h => ne (Fin.ext h)]
  · simp
end DetDLP.CanonicalGridCoordinates
end

section
namespace DetDLP.IntegralJetTower
open Polynomial Finset
abbrev O := DyadicGrid.localRing
noncomputable abbrev F (A : Type) [CommRing A] (f : ℤ[X]) := f.map (Int.castRingHom A)
abbrev U (A : Type) [CommRing A] (f : ℤ[X]) := AdjoinRoot (F A f)
noncomputable abbrev polyZ (A : Type) [CommRing A] (f : ℤ[X]) (e : ℕ) := (X:(U A f)[X])^e
abbrev Z (A : Type) [CommRing A] (f : ℤ[X]) (e : ℕ) := AdjoinRoot (polyZ A f e)
variable {A B : Type} [CommRing A] [CommRing B] (φ : A→+*B) (f : ℤ[X]) (e : ℕ)

theorem F_natural : (F A f).map φ=F B f := by
  rw [F,Polynomial.map_map]; congr 1; apply RingHom.ext_int
noncomputable def uMap : U A f→+*U B f := MonicSpecialization.specialize φ (F_natural φ f)
theorem Z_natural : (polyZ A f e).map (uMap φ f)=polyZ B f e := by simp [polyZ]
noncomputable def zMap : Z A f e→+*Z B f e := MonicSpecialization.specialize (uMap φ f) (Z_natural φ f e)
theorem scalars (x : A) :
    zMap φ f e (algebraMap A (Z A f e) x)=algebraMap B (Z B f e) (φ x) := by
  rw [IsScalarTower.algebraMap_apply A (U A f) (Z A f e),IsScalarTower.algebraMap_apply B (U B f) (Z B f e)]
  rw [zMap,MonicSpecialization.spec_constant,uMap,MonicSpecialization.spec_constant]
theorem onto (h : Function.Surjective φ) : Function.Surjective (zMap φ f e) :=
  MonicSpecialization.surj _ _ (MonicSpecialization.surj _ _ h)
theorem inject (hf : f.Monic) (h : Function.Injective φ) : Function.Injective (zMap φ f e) :=
  MonicSpecialization.inj _ _ (MonicSpecialization.inj _ _ h (hf.map _)) (monic_X_pow e)
theorem divides (hf : f.Monic) (k : ℕ) (base : ∀ x,φ x=0→(2:A)^k∣x)
    (x : Z A f e) (hz : zMap φ f e x=0) : (2:Z A f e)^k∣x := by
  have first (y : U A f) (hy : uMap φ f y=0) : (2:U A f)^k∣y := by
    simpa only [map_ofNat] using MonicSpecialization.kernel φ (F_natural φ f) (hf.map _) 2 k base y hy
  simpa only [map_ofNat] using MonicSpecialization.kernel (uMap φ f) (Z_natural φ f e) (monic_X_pow e) 2 k first x hz

noncomputable abbrev inc := zMap O.subtype f e
noncomputable abbrev lattice := (inc f e).range
noncomputable def coords (hf : f.Monic) : Z O f e ≃+* lattice f e :=
  RingEquiv.ofBijective (inc f e).rangeRestrict ⟨fun _ _ h => inject _ f e hf Subtype.val_injective (congrArg Subtype.val h),
    (inc f e).rangeRestrict_surjective⟩

theorem closed (q : ℚ) (hq : q=0 ∨ 0≤padicValRat 2 q) : algebraMap ℚ (Z ℚ f e) q∈lattice f e :=
  ⟨algebraMap O (Z O f e) (⟨q,hq⟩:O),scalars _ f e _⟩
noncomputable def red (hf : f.Monic) (p : ℕ) : lattice f e→+*Z (ZMod (2^p)) f e :=
  (zMap (DyadicGrid.reduceAt p) f e).comp (coords f e hf).symm.toRingHom
theorem red_onto (hf : f.Monic) (p : ℕ) : Function.Surjective (red f e hf p) :=
  (onto _ f e (LocalBinaryReduction.onto p)).comp (coords f e hf).symm.surjective
theorem red_kernel (hf : f.Monic) (p : ℕ) (x : lattice f e) (hz : red f e hf p x=0) :
    (2:lattice f e)^p∣x := by
  obtain ⟨y,eq⟩ := divides _ f e hf p (LocalBinaryReduction.ker p) ((coords f e hf).symm x) hz
  exact ⟨coords f e hf y,by simpa only [RingEquiv.apply_symm_apply,map_mul,map_pow,map_ofNat] using congrArg (coords f e hf) eq⟩

noncomputable def grid {κ : ℕ} (p : ℕ) (x : Fin κ→ZMod 2) : Z (ZMod (2^p)) f e :=
  algebraMap (U (ZMod (2^p)) f) _ (DenseBinaryGrid.sample f p x)
theorem units {κ : ℕ} (hf : f.Monic) (hd : f.natDegree=κ) (ir : Irreducible (F (ZMod 2) f)) (p : ℕ)
    {x y : Fin κ→ZMod 2} (h : x≠y) : IsUnit (grid f e p x-grid f e p y) := by
  unfold grid; rw [← map_sub]; exact (DenseBinaryGrid.units f hf hd ir p h).map _
end DetDLP.IntegralJetTower
end

section
namespace DetDLP.IntegralJetWords
open Polynomial Finset IntegralJetTower
variable (f : ℤ[X]) (e : ℕ)
noncomputable def pack {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) : A[X] :=
  ∑ j,monomial j.val (w j)
theorem cell {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) (j : Fin n) : (pack w).coeff j.val=w j := by
  classical
  rw [pack,finsetSum_coeff,sum_eq_single j]
  · simp
  · intro i _ ne; simp [coeff_monomial,show i.val≠j.val from fun z => ne (Fin.ext z)]
  · simp
theorem short {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) : (pack w).degree<(n:WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr; intro j hj
  rw [pack,finsetSum_coeff]; apply sum_eq_zero; intro i _
  simp [coeff_monomial,show i.val≠j from by have := i.isLt; omega]
theorem normal_pack {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) :
    AdjoinRoot.modByMonicHom (monic_X_pow n) (AdjoinRoot.mk ((X:A[X])^n) (pack w))=pack w := by
  nontriviality A
  rw [AdjoinRoot.modByMonicHom_mk,modByMonic_eq_self_iff (monic_X_pow n),degree_X_pow]
  exact short w
theorem truncate {A : Type} [CommRing A] (n : ℕ) (x : AdjoinRoot ((X:A[X])^n)) :
    AdjoinRoot.mk _ (pack (fun j : Fin n => (AdjoinRoot.modByMonicHom (monic_X_pow n) x).coeff j.val))=x := by
  let h := AdjoinRoot.modByMonicHom (monic_X_pow n) x
  have eq : AdjoinRoot.mk ((X:A[X])^n) (pack (fun j : Fin n => h.coeff j.val))=AdjoinRoot.mk _ h := by
    apply AdjoinRoot.mk_eq_mk.mpr; apply X_pow_dvd_iff.mpr
    intro j hj; rw [coeff_sub,show (pack (fun i : Fin n => h.coeff i.val)).coeff j=h.coeff j from cell _ ⟨j,hj⟩,sub_self]
  exact eq.trans (AdjoinRoot.mk_leftInverse (monic_X_pow n) x)

noncomputable def inner {A : Type} [CommRing A] (w : Fin f.natDegree→ℕ) : U A f :=
  AdjoinRoot.mk _ ((CanonicalGridCoordinates.liftWord f w).map (Int.castRingHom A))
noncomputable def decode {A : Type} [CommRing A] (w : Fin e→Fin f.natDegree→ℕ) : Z A f e :=
  AdjoinRoot.mk _ (pack (fun j => inner f (A:=A) (w j)))
noncomputable def words (hf : f.Monic) (p : ℕ) (x : Z (ZMod (2^p)) f e) (j : Fin e) :=
  CanonicalGridCoordinates.word f hf p ((AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val)
theorem natural {A B : Type} [CommRing A] [CommRing B] (φ : A→+*B) (w : Fin e→Fin f.natDegree→ℕ) :
    zMap φ f e (decode f e w)=decode f e w := by
  change MonicSpecialization.specialize _ _ (AdjoinRoot.mk _ _)=_
  rw [MonicSpecialization.spec_mk]
  apply congrArg (AdjoinRoot.mk _)
  simp only [pack,Polynomial.map_sum,Polynomial.map_monomial]
  apply sum_congr rfl; intro j _
  change monomial _ (MonicSpecialization.specialize _ _ (AdjoinRoot.mk _ _))=monomial _ _
  rw [MonicSpecialization.spec_mk,Polynomial.map_map]
  congr 3; apply RingHom.ext_int

theorem decode_word (hf : f.Monic) (p : ℕ) (hp : 0<p) (x : Z (ZMod (2^p)) f e) :
    decode f e (words f e hf p x)=x := by
  have eq (j : Fin e) : inner f (A:=ZMod (2^p)) (words f e hf p x j)=(AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val := by
    have hh := CanonicalGridCoordinates.decode hf hp ((AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val)
    rw [AdjoinRoot.aeval_eq_of_algebra] at hh; exact hh
  simp only [decode,eq]; exact truncate _ _

noncomputable def lift (hf : f.Monic) (p : ℕ) (x : Z (ZMod (2^p)) f e) : lattice f e :=
  coords f e hf (decode f e (A:=O) (words f e hf p x))
theorem read_lift (hf : f.Monic) {p q : ℕ} (x : Z (ZMod (2^p)) f e) :
    red f e hf q (lift f e hf p x)=decode f e (words f e hf p x) := by
  change zMap _ f e ((coords f e hf).symm ((coords f e hf) _))=_
  rw [RingEquiv.symm_apply_apply,natural]
theorem canonical (hf : f.Monic) {p q : ℕ} (hp : 0<p) (h : p≤q) (x : Z (ZMod (2^p)) f e) :
    words f e hf q (red f e hf q (lift f e hf p x))=words f e hf p x := by
  rw [read_lift]
  funext j
  unfold words decode
  rw [normal_pack,cell]
  have H := CanonicalGridCoordinates.lift_again (f:=f) hf hp h ((AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val)
  rw [AdjoinRoot.aeval_eq_of_algebra] at H; exact funext H
end DetDLP.IntegralJetWords
end

section
namespace DetDLP.PacketPolynomialForm
open OrientedPacketInstance Finset Polynomial
variable {a : ℕ} {P R A : Type} [Fintype P] [CommRing R] [CommRing A]
variable (G : BipartiteMultigraph) (active : P→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
abbrev Grid (a : ℕ) := ZMod (2^(a+1))
def offset (x y : Pos a) : Grid a := (y.val:Grid a)-(x.val:Grid a)
noncomputable def valAt (K : Grid a→R) (x : Fin G.nE→Bool) (e : Fin G.nE) :=
  ∑ f : ↥(active (L e).1), if x (L.symm ⟨(L e).1,f⟩) then K (offset (L e).2.val f.val) else 0
noncomputable def term (K : Grid a→R) (x y : Fin G.nE→Bool) (e : Fin G.nE) :=
  if y e then valAt G active L K x e else 1-valAt G active L K x e
noncomputable def form (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R) (K : Grid a→R) :=
  ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,DeformedContraction.weight T x y*∏ e,term G active L K x y e

theorem map_form (φ : R→+*A) (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R) (K : Grid a→R) :
    φ (form G active L T K)=form G active L (fun v x => φ (T v x)) (fun d => φ (K d)) := by
  classical
  simp [form,term,valAt,DeformedContraction.weight,DeformedContraction.portValue,apply_ite,map_prod,map_sum]

theorem natCast_inj (x y : Pos a) : (x.val:Grid a)=(y.val:Grid a) ↔ x=y := by
  have g : 2^a≤2^(a+1) := Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro eq; apply Fin.ext
    simpa [ZMod.val_natCast_of_lt (x.isLt.trans_le g),ZMod.val_natCast_of_lt (y.isLt.trans_le g)] using congrArg ZMod.val eq
  · rintro rfl; rfl

theorem delta (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R) :
    form G active L T (fun d => if d=0 then 1 else 0)=BTNContract G T := by
  classical
  let K (d : Grid a) := if d=0 then (1:R) else 0
  have bits (x : Fin G.nE→Bool) (e : Fin G.nE) :
      valAt G active L K x e=if x e then 1 else 0 := by
    unfold valAt
    rw [sum_eq_single (L e).2]
    · simp [K,offset]
    · intro f _ ne
      have neq : offset (L e).2.val f.val≠0 := fun h => ne (Subtype.ext ((natCast_inj _ _).mp (sub_eq_zero.mp h)))
      simp [K,neq]
    · simp
  have sel (x y : Fin G.nE→Bool) (e : Fin G.nE) :
      term G active L K x y e=if y e=x e then 1 else 0 := by
    cases hy : y e <;> cases hx : x e <;> simp [term,hy,hx,bits]
  have agrees (x y : Fin G.nE→Bool) :
      (∏ e,term G active L K x y e)=if y=x then 1 else 0 := by
    simp only [sel]; split_ifs with eq
    · simp [eq]
    · obtain ⟨e,ne⟩ : ∃ e,y e≠x e := by by_contra! same; exact eq (funext same)
      exact prod_eq_zero (mem_univ e) (if_neg ne)
  change (∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,DeformedContraction.weight T x y*∏ e,term G active L K x y e)=_
  simp only [agrees,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true]
  unfold BTNContract
  apply sum_congr rfl; intro x _
  simp [DeformedContraction.weight,DeformedContraction.portValue]

theorem degree (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R) (K : Grid a→R[X]) (D : ℕ)
    (bound : ∀ d,(K d).natDegree≤D) :
    (form G active L (fun v x => C (T v x)) K).natDegree≤G.nE*D := by
  have bit (x : Fin G.nE→Bool) (e : Fin G.nE) : (valAt G active L K x e).natDegree≤D := by
    apply natDegree_sum_le_of_forall_le; intro j _
    split_ifs <;> simp [bound]
  have sel (x y : Fin G.nE→Bool) (e : Fin G.nE) : (term G active L K x y e).natDegree≤D := by
    unfold term; split_ifs
    · exact bit x e
    · exact (natDegree_sub_le ..).trans (max_le (by simp) (bit x e))
  have wt (x y : Fin G.nE→Bool) : DeformedContraction.weight (fun v t => C (T v t)) x y=C (DeformedContraction.weight T x y) := by
    simp [DeformedContraction.weight,DeformedContraction.portValue,apply_ite,map_prod]
  apply natDegree_sum_le_of_forall_le; intro x _
  apply natDegree_sum_le_of_forall_le; intro y _
  rw [wt]; apply (natDegree_C_mul_le ..).trans
  exact (natDegree_prod_le ..).trans (by simpa using sum_le_sum (s:=univ) (fun e _ => sel x y e))

theorem residue [DecidableEq P] {p : ℕ} [Algebra (ZMod (2^p)) R] (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R)
    (U : Grid a→(ZMod (2^p))[X]) (z : R) :
    form G active L T (fun d => (U d).eval₂ (algebraMap (ZMod (2^p)) R) z) =
      ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,DeformedContraction.weight T x y*∏ e,selector G active L U z x y e := by
  unfold form
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  congr 1; apply prod_congr rfl; intro e _
  simp [term,valAt,selector,offset,mul_ite]
end DetDLP.PacketPolynomialForm
end

section
namespace DetDLP.CauchyLocalForm
open OrientedPacketInstance Polynomial Finset PacketPolynomialForm
variable {a : ℕ}
abbrev J (a : ℕ) := PacketPolynomialForm.Grid a
noncomputable def shifts (a : ℕ) := univ.image (fun d : J a => (d.valMinAbs:ℚ))
noncomputable def raw (d : J a) := DeformedContraction.shiftKernel (shifts a) (d.valMinAbs:ℚ)
noncomputable def centre (t : J a) : ℚ[X] := C (t.valMinAbs:ℚ)+C ((2:ℚ)^(a+1))*X

theorem raw_at_zero (d : J a) : (raw d).eval 0=if d=0 then 1 else 0 := by
  classical
  have z : (0:ℚ)∈shifts a := mem_image.mpr ⟨0,mem_univ _,by simp⟩
  have ne : (∏ s∈(shifts a).erase 0,-s)≠0 := prod_ne_zero_iff.mpr (fun s hs => neg_ne_zero.mpr (ne_of_mem_erase hs))
  by_cases d0 : d=0
  · subst d; simp [raw,DeformedContraction.shiftKernel,eval_prod,ne]
  · have q : (d.valMinAbs:ℚ)≠0 := by
      intro e; have h : d.valMinAbs=0 := by exact_mod_cast e
      exact d0 (by rw [← ZMod.coe_valMinAbs d,h]; simp)
    simp only [raw,DeformedContraction.shiftKernel,eval_prod,eval_mul,eval_C,eval_sub,eval_X,zero_sub,if_neg d0]
    rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm q,z⟩) (neg_zero),mul_zero]

theorem raw_degree (d : J a) : (raw d).natDegree≤2^(a+1)-1 := by
  have hd : (d.valMinAbs:ℚ)∈shifts a := mem_image.mpr ⟨d,mem_univ _,rfl⟩
  have size : (shifts a).card≤2^(a+1) := by
    apply card_image_le.trans; simp [J,PacketPolynomialForm.Grid]
  apply (natDegree_C_mul_le ..).trans
  apply (natDegree_prod_le ..).trans
  simp only [natDegree_X_sub_C,sum_const_zero,Finset.sum_const,smul_eq_mul,mul_one,card_erase_of_mem hd]
  omega

abbrev O := DyadicGrid.localRing
noncomputable def intKernel (t d : J a) : O[X] :=
  DyadicGrid.residueKernel (fun r => r.valMinAbs) ZMod.coe_valMinAbs (by simp) t d

theorem int_identity (t d : J a) : (intKernel t d).map O.subtype=(raw d).comp (centre t) := by
  let r (e : J a) := e.valMinAbs
  have hr : ∀ e : J a,((r e:ℤ):J a)=e := ZMod.coe_valMinAbs
  have e : shifts a=univ.map (DyadicGrid.repEmbedding r hr) := (Finset.map_eq_image (DyadicGrid.repEmbedding r hr) univ).symm
  change (DyadicGrid.residueKernel r hr (by simp [r]) t d).map O.subtype=_
  rw [DyadicGrid.residueKernel,DyadicGrid.map_liftPoly,raw,e,DyadicGrid.raw_matches r hr (by simp [r])]
  rfl

variable {H : Type} [CommRing H] [Algebra ℚ H] (I : Subring H)
variable (closed : ∀ q : ℚ,(q=0 ∨ 0≤padicValRat 2 q)→algebraMap ℚ H q∈I)
noncomputable def embed : O→+*I :=
  ((algebraMap ℚ H).comp O.subtype).codRestrict I fun x => closed x x.property

theorem entry_reduce {p : ℕ} {A : Type} [CommRing A] [Algebra (ZMod (2^p)) A]
    (φ : I→+*A) (t : J a) (U : J a→(ZMod (2^p))[X]) (rep : Represents t U) (d : J a) :
    ((intKernel t d).map (embed I closed)).map φ = (U d).map (algebraMap (ZMod (2^p)) A) := by
  ext n
  let x := (intKernel t d).coeff n
  let c := (kernel t d).coeff n
  have hc : (x:ℚ)=c := by
    change O.subtype ((intKernel t d).coeff n)=_
    rw [← coeff_map,int_identity]; rfl
  obtain ⟨unit,eq⟩ := rep d n
  change IsUnit (c.den : ZMod (2^p)) at unit
  have eqI : embed I closed x*(c.den:I)=(c.num:I) := by
    apply Subtype.ext
    change algebraMap ℚ H (x:ℚ)*(c.den:H)=(c.num:H)
    rw [hc]
    simpa only [map_mul,map_natCast,map_intCast] using congrArg (algebraMap ℚ H) (Rat.mul_den_eq_num c)
  have left := congrArg φ eqI
  have right := congrArg (algebraMap (ZMod (2^p)) A) eq
  have inv := unit.map (algebraMap (ZMod (2^p)) A)
  simp only [map_natCast] at inv
  simp only [map_mul,map_natCast,map_intCast] at left right
  simp only [coeff_map]
  apply inv.mul_right_cancel
  exact left.trans right.symm

end DetDLP.CauchyLocalForm
end

section
namespace DetDLP.CanonicalPacketKernel
open Polynomial OrientedPacketInstance CauchyLocalForm DyadicGrid
noncomputable def value {a : ℕ} (t : J a) (p : ℕ) (d : J a) : (ZMod (2^p))[X] :=
  (intKernel t d).map (reduceAt p)
theorem valid {a : ℕ} (t : J a) (p : ℕ) : Represents t (value t p) := by
  intro d n c
  let x := (intKernel t d).coeff n
  have eq : (x:ℚ)=c := by
    change O.subtype ((intKernel t d).coeff n)=_
    rw [←coeff_map,int_identity]; rfl
  rw [←eq]
  constructor
  · have unit := (PadicInt.isUnit_den (x:ℚ) (toPadic x).property).map (PadicInt.toZModPow (p:=2) p)
    simpa only [map_natCast] using unit
  · rw [value,coeff_map]; exact reduce_fraction p x
theorem unique {a p : ℕ} (t : J a) {V : J a→(ZMod (2^p))[X]} (hv : Represents t V) :
    V=value t p := by
  funext d; ext n
  obtain ⟨unit,x⟩ := hv d n
  exact unit.mul_right_cancel (x.trans ((valid t p d n).2.symm))
end DetDLP.CanonicalPacketKernel
end

section
namespace DetDLP.ConcreteDyadicRecovery
open Finset Polynomial DetDLP.OrientedPacketInstance

set_option maxRecDepth 6500 in
theorem full {a N : ℕ} (G : BipartiteMultigraph) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
    (P h u κ ell : ℕ) (hP : 0<P) (hκ : 0<κ) (hM : 0<G.nE) (lo : 3*G.nE≤h*u) (hi : h*u≤4*G.nE)
    (room : G.nE*(2^(a+1)-1)+1≤2^κ) :
    let Tm := univ.erase (0:ZMod (2^(a+1)))
    let v (t : ↥Tm) := padicValNat 2 t.val.val
    let m (t : ↥Tm) := h*(u-v t)
    let D (t : ↥Tm) := 2^(a-v t)
    let loss (t : ↥Tm) := 6*h*D t+4*G.nE*(a+1)
    let Q (t : ↥Tm) := P+8*h*D t+8*G.nE*(a+1)
    let n := G.nE*(2^(a+1)-1)+1
    ∃ c : Fin κ→ZMod 2,let f := (X:ℤ[X])^κ+∑ j,monomial j.val ((c j).val:ℤ)
    f.Monic ∧ f.natDegree=κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2))) ∧
    let H₀ := AdjoinRoot (f.map (Int.castRingHom ℚ))
    let H := AdjoinRoot ((X:H₀[X])^ell)
    let K (p : ℕ) := AdjoinRoot (f.map (Int.castRingHom (ZMod (2^p))))
    let R (p : ℕ) := AdjoinRoot ((X:(K p)[X])^ell)
    ∃ (I : Subring H) (π : (p : ℕ)→I→+*R p) (lift : (p : ℕ)→R p→I)
      (word : (p : ℕ)→R p→Fin ell→Fin f.natDegree→ℕ)
      (grid : (p : ℕ)→Fin n→R p),
      (∀ p x j k,word p x j k<2^p) ∧ (∀ p,0<p→∀ x,π p (lift p x)=x) ∧
      (∀ p q,0<p→p≤q→∀ x,word q (π q (lift p x))=word p x) ∧
      (∀ p i j,i≠j→IsUnit (grid p i-grid p j)) ∧
      ∃ U : (t : ↥Tm)→ZMod (2^(a+1))→(ZMod (2^Q t))[X],(∀ t,Represents t.val (U t)) ∧
      ∃ w : ↥Tm→ℕ→ℚ,(∀ t j,w t j=0 ∨ -(loss t:ℤ)≤padicValRat 2 (w t j)) ∧
      ∃ V : (t : ↥Tm)→ℕ→Fin n→R (Q t),∀ T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I,
        let sample (t : ↥Tm) (j : Fin n) := ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v z => π (Q t) (T v z)) x y *
            ∏ e,selector G active L (U t) (grid (Q t) j) x y e
        let jet (t : ↥Tm) (j : ℕ) := lift (Q t) (∑ k,V t j k*sample t k)
        ∃ E : I, (∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*(jet t j:H))-
          BTNContract G (fun v z => (T v z:H))=(2:H)^P*(E:H) := by
  classical
  intro Tm v m D loss Q n
  obtain ⟨c,mon,degree,ir⟩ := BinaryExtensionGrid.modulus κ hκ
  refine ⟨c,?_⟩; intro f
  refine ⟨mon,degree,ir,?_⟩; intro H₀ H K R
  let I := IntegralJetTower.lattice f ell
  let red := IntegralJetTower.red f ell mon
  let can := IntegralJetWords.lift f ell mon
  let word := IntegralJetWords.words f ell mon
  have card : Fintype.card (Fin κ→ZMod 2)=2^κ := by simp
  let e := (Fin.castLEEmb (room.trans_eq card.symm)).trans (Fintype.equivFin (Fin κ→ZMod 2)).symm.toEmbedding
  let grid (p : ℕ) (j : Fin n) := IntegralJetTower.grid f ell p (e j)
  have units (p : ℕ) (i j : Fin n) (ne : i≠j) : IsUnit (grid p i-grid p j) :=
    IntegralJetTower.units f ell mon degree ir p (fun eq => ne (e.injective eq))
  have sec' (p : ℕ) (hp : 0<p) (x : R p) : red p (can p x)=x :=
    (IntegralJetWords.read_lift f ell mon x).trans (IntegralJetWords.decode_word f ell mon p hp x)
  let U (t : ↥Tm) := CanonicalPacketKernel.value t.val (Q t)
  have rep (t : ↥Tm) : Represents t.val (U t) := CanonicalPacketKernel.valid t.val (Q t)
  refine ⟨I,red,can,word,grid,fun p x j k => CanonicalGridCoordinates.word_lt _ mon p _ k,sec',
    fun p q hp h x => IntegralJetWords.canonical f ell mon hp h x,units,U,rep,?_⟩
  obtain ⟨w,bw,recov⟩ := guarded_recovery_from_actual_packet_samples G active L P h u hM lo hi
  have pq (t : ↥Tm) : 0<Q t := by dsimp [Q]; omega
  obtain ⟨V,reconstruct⟩ := recov H I (IntegralJetTower.closed f ell) (fun t => R (Q t))
    (fun t => red (Q t)) (fun t => can (Q t)) (fun t => sec' (Q t) (pq t))
    (fun t => IntegralJetTower.red_kernel f ell mon (Q t)) (fun t => grid (Q t)) (fun t => units (Q t))
  exact ⟨w,bw,V,fun T => reconstruct T U rep⟩
end DetDLP.ConcreteDyadicRecovery
end

section
namespace DetDLP.PrescribedResidualSpecialization
open Finset Polynomial
set_option maxRecDepth 13000 in
set_option maxHeartbeats 1800000 in
theorem full (C : ℕ) :
    ∃ (L₀ : ℕ) (K₁ K₂ : ℝ),0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ {G : BipartiteMultigraph} {b m k S p ell : ℕ}
      (spec : LookupSeparatorSpec G m k S (C*Nat.ceil ((b:ℝ)^((3:ℝ)/4)))),
    let L := Nat.clog 2 S
    let D := Nat.clog 32 (4*m)
    let κ := 4*L
    let g := 64*(S+1)*(L+1)*2^L*64^D
    let U := max (k+32*(L+2)) (2*(S/((L/32).sqrt+1)))
    L₀ ≤ L → 0 < m → b ≤ C*(4*m*k) → S ≤ C*m*b → m ≤ C*blockCount b → 0 < p → p ≤ S →
    ∃ c : Fin κ→ZMod 2,let f := (X:ℤ[X])^κ+∑ j,monomial j.val ((c j).val:ℤ)
    f.Monic ∧ f.natDegree=κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2))) ∧
    let H₀ := AdjoinRoot (f.map (Int.castRingHom ℚ))
    let H := AdjoinRoot ((X:H₀[X])^ell)
    let I := IntegralJetTower.lattice f ell
    (∀ q : ℚ,(q=0 ∨ 0 ≤ padicValRat 2 q)→algebraMap ℚ H q∈I) ∧
    ∀ T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I,
      ∃ (N : ℕ) (w : Fin N→H) (R : Fin N→BipartiteMultigraph)
        (A : (l : Fin N)→(v : Fin (R l).nV)→(Fin ((R l).deg v)→Bool)→I),
        (N:ℝ) ≤ Real.exp (K₁*((b:ℝ)/(L:ℝ)^(7/40:ℝ))+K₂*(L:ℝ)^(13/10:ℝ)) ∧
        (∀ l,(R l).nE=4*m*k ∧ (R l).nV ≤ 4*m+64^D ∧ (R l).maxDeg ≤ U ∧ (2:H)^g*w l∈I) ∧
        ∃ err : I,(∑ l,w l*((BTNContract (R l) (A l):I):H))-((BTNContract G T:I):H)=(2:H)^p*(err:H) := by
  classical
  obtain ⟨lo,K₁,K₂,ha,hb,all⟩ := terminal_residual_expansion_over_a_prescribed_lattice C
  refine ⟨max 1 lo,K₁,K₂,ha,hb,?_⟩
  intro G b m k S p ell spec L D κ g U big hm comp bound blocks hp hpS
  have hL : 1 ≤ L := (le_max_left ..).trans big
  have hκ : 0 < κ := by dsimp only [κ]; omega
  obtain ⟨c,mon,degree,ir⟩ := BinaryExtensionGrid.modulus κ hκ
  refine ⟨c,?_⟩; intro f; refine ⟨mon,degree,ir,?_⟩; intro H₀ H
  let I := IntegralJetTower.lattice f ell
  let R (p : ℕ) := IntegralJetTower.Z (ZMod (2^p)) f ell
  let red := IntegralJetTower.red f ell mon
  let can := IntegralJetWords.lift f ell mon
  have card : Fintype.card (Fin κ→ZMod 2)=2^κ := by simp
  let labels := (finCongr card.symm).trans (Fintype.equivFin (Fin κ→ZMod 2)).symm
  let grid (p : ℕ) (j : Fin (2^κ)) := IntegralJetTower.grid f ell p (labels j)
  have units (p : ℕ) (i j : Fin (2^κ)) (ne : i≠j) : IsUnit (grid p i-grid p j) :=
    IntegralJetTower.units f ell mon degree ir p (fun eq => ne (labels.injective eq))
  have sec' (p : ℕ) (h : 0<p) (x : R p) : red p (can p x)=x :=
    (IntegralJetWords.read_lift f ell mon x).trans (IntegralJetWords.decode_word f ell mon p h x)
  intro lattice; refine ⟨IntegralJetTower.closed f ell,?_⟩; intro T
  exact all (ell:=ell) spec ((le_max_right ..).trans big) hm comp bound blocks hp hpS H I (IntegralJetTower.closed f ell) R red can grid sec'
    (IntegralJetTower.red_kernel f ell mon) units T
end DetDLP.PrescribedResidualSpecialization
end

section
namespace DetDLP.ActiveDepthPrecision
open Filter Finset

theorem absorbs (A k : ℕ) : ∃ N : ℕ,∀ n≥N,A*(n+1)^k≤2^n := by
  let B := A*2^k+1
  have hB : (0:ℝ)<B := by exact_mod_cast (show 0<B by dsimp [B]; omega)
  have little := isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) k (r:=2) (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (little.bound (inv_pos.mpr hB))
  refine ⟨max N 1,fun n hn => ?_⟩
  have h := hN n ((le_max_left ..).trans hn)
  have realB : (n:ℝ)^k≤(B:ℝ)⁻¹*(2:ℝ)^n := by
    simpa only [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg n) _),Real.norm_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) _)] using h
  have aux : (B:ℝ)*(n:ℝ)^k≤(2:ℝ)^n := by
    have H := mul_le_mul_of_nonneg_left realB hB.le
    rwa [← mul_assoc,mul_inv_cancel₀ hB.ne',one_mul] at H
  have natB : B*n^k≤2^n := by exact_mod_cast aux
  have hstep : (n+1)^k≤(2*n)^k := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ A*((2*n)^k) := Nat.mul_le_mul_left _ hstep
    _ ≤ B*n^k := by rw [mul_pow,← mul_assoc]; exact Nat.mul_le_mul_right _ (by dsimp [B]; omega)
    _ ≤ _ := natB

theorem relevant (C B ρ d : ℕ) (hC : 0<C) (hB : 0<B)
    (depth : 2^d≤C*(ρ.sqrt+1)) :
    let u := ρ/(B*2^d)
    ρ+1≤((2*B*C+2)*(u+1))^2 := by
  intro u
  let v := ρ.sqrt
  let f := (u+1)*B*C
  have a : ρ<(u+1)*(B*2^d) := by
    rw [Nat.mul_comm (u+1)]; exact Nat.lt_mul_div_succ _ (by positivity)
  have b := Nat.mul_le_mul_left ((u+1)*B) depth
  have c : v*v<f*(v+1) := by
    calc
      v*v≤ρ := Nat.sqrt_le _
      _ < (u+1)*(B*2^d) := a
      _ ≤ f*(v+1) := by simpa only [f,v,Nat.mul_assoc] using b
  have small : v≤2*f := by
    by_cases hv : v=0
    · omega
    · have h : f*(v+1)≤f*(2*v) := Nat.mul_le_mul_left _ (by omega)
      have z : v*v<(2*f)*v := (c.trans_le h).trans_eq (by ring)
      exact (Nat.lt_of_mul_lt_mul_right z).le
  have sq := Nat.lt_succ_sqrt ρ
  have bound : v+1≤(2*B*C+2)*(u+1) := by dsimp [f] at small; nlinarith only [small,Nat.zero_le u]
  exact (Nat.succ_le_of_lt sq).trans (by simpa [pow_two] using Nat.mul_le_mul bound bound)

theorem active {C B : ℕ} (hC : 0<C) (hB : 0<B) (A j : ℕ) :
    ∃ R : ℕ,∀ (ρ β M d : ℕ),R≤ρ→0<M→β≤M*(ρ.sqrt+1)→M*8^d≤C*β →
      A*(ρ+1)^j≤2^(ρ/(B*2^d)) := by
  let K := 2*B*C+2
  obtain ⟨N,hN⟩ := absorbs (A*K^(2*j)) (2*j)
  refine ⟨(K*(N+1))^2,?_⟩
  intro ρ β M d hρ hm hb hd
  have power : 2^d≤8^d := Nat.pow_le_pow_left (by decide) _
  have depth : 2^d≤C*(ρ.sqrt+1) := by
    apply Nat.le_of_mul_le_mul_left (c:=M) _ hm
    calc
      _≤M*8^d := Nat.mul_le_mul_left _ power
      _≤C*β := hd
      _≤C*(M*(ρ.sqrt+1)) := Nat.mul_le_mul_left _ hb
      _=M*(C*(ρ.sqrt+1)) := by ring
  let u := ρ/(B*2^d)
  have bound : ρ+1≤(K*(u+1))^2 := relevant C B ρ d hC hB depth
  have hu : N≤u := by
    by_contra! h
    have small := Nat.pow_le_pow_left (Nat.mul_le_mul_left K (show u+1≤N+1 by omega)) 2
    omega
  calc
    A*(ρ+1)^j ≤ A*((K*(u+1))^2)^j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)
    _ = (A*K^(2*j))*(u+1)^(2*j) := by rw [← pow_mul,mul_pow]; ring
    _ ≤ _ := hN u hu
end DetDLP.ActiveDepthPrecision
end

section
namespace DetDLP.ContractionPathPrecision

def window (B ρ d : ℕ) := ρ/(B*2^d)
def widthBefore (B ρ : ℕ) : ℕ→ℕ
  | 0 => 0
  | d+1 => widthBefore B ρ d+2*window B ρ d
def mult (M u : ℕ) := (3*M+u-1)/u
def next (p M u a i : ℕ) := p+8*mult M u*2^(a-i)+8*M*(a+1)
theorem window_le (B ρ d : ℕ) : window B ρ d≤ρ := Nat.div_le_self _ _
theorem prefix_mono (B ρ : ℕ) : Monotone (widthBefore B ρ) := by
  apply monotone_nat_of_le_succ
  intro n; simp [widthBefore]
theorem prefix_le (B ρ d : ℕ) : widthBefore B ρ d≤2*d*ρ := by
  induction d with
  | zero => simp [widthBefore]
  | succ d ih =>
    simp only [widthBefore]; have h := window_le B ρ d
    rw [Nat.mul_succ,Nat.add_mul]; omega
theorem mult_total (M u : ℕ) : mult M u*u≤3*M+u := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
theorem mult_le (M u : ℕ) : mult M u≤3*M+1 := by
  by_cases h : u=0
  · simp [mult,h]
  · apply Nat.le_of_mul_le_mul_right (c:=u) _ (Nat.pos_of_ne_zero h)
    have H := mult_total M u
    have h' := Nat.mul_le_mul_left (3*M) (Nat.one_le_iff_ne_zero.mpr h)
    rw [Nat.add_mul]; simp only [one_mul]; omega

theorem add_cap {M X u a A i : ℕ} (hM : M≤X) (ha : a≤A) :
    next 0 M u a i≤64*(X+1)*(A+1)*2^A := by
  have hm : mult M u≤4*(X+1) := by have := mult_le M u; omega
  have hp : 2^(a-i)≤2^A := Nat.pow_le_pow_right (by decide) ((Nat.sub_le _ _).trans ha)
  have hq : 1≤2^A := Nat.one_le_pow _ _ (by decide)
  have hbig := Nat.mul_le_mul_right (4*(X+1)) (show 1≤A+1 by omega)
  have t1 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hm) hp
  have t2 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hM) (Nat.add_le_add_right ha 1)
  have up := Nat.mul_le_mul_left (8*X*(A+1)) hq
  unfold next
  nlinarith only [t1,t2,up,Nat.zero_le ((X+1)*A*2^A),Nat.zero_le ((X+1)*2^A),Nat.zero_le (X*(A+1)*2^A),Nat.zero_le (A*2^A)]

theorem path_cap (B ρ X d : ℕ) (p m i : ℕ→ℕ) (h0 : p 0≤X)
    (size : ∀ j<d,m j≤X)
    (step : ∀ j<d,p (j+1)≤next (p j) (m j) (window B ρ j) (widthBefore B ρ (j+1)) (i j)) :
    p d≤(X+d*(64*(X+1)*(widthBefore B ρ d+1)))*2^(widthBefore B ρ d) := by
  let A := widthBefore B ρ d
  let K := 64*(X+1)*(A+1)
  have aux (j : ℕ) (hj : j≤d) : p j≤X+j*(K*2^A) := by
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have cap := add_cap (i:=i j) (u:=window B ρ j) (size j hj) (prefix_mono B ρ hj)
      have s := step j hj
      have h := ih (by omega)
      change next 0 (m j) _ _ _≤K*2^A at cap
      simp only [next,zero_add] at cap s
      rw [Nat.succ_mul]; omega
  have h := aux d le_rfl
  have pow : 1≤2^A := Nat.one_le_pow _ _ (by decide)
  have hX := Nat.mul_le_mul_left X pow
  change p d≤(X+d*K)*2^A
  rw [Nat.add_mul,Nat.mul_assoc]; omega

theorem envelope {B C ρ β d : ℕ} (hβ : 0<β) (hd : d≤C*(ρ+1))
    (p m i : ℕ→ℕ) (h0 : p 0≤C*β) (size : ∀ j<d,m j≤C*β)
    (step : ∀ j<d,p (j+1)≤next (p j) (m j) (window B ρ j) (widthBefore B ρ (j+1)) (i j)) :
    p d≤(256*(C+1)^3)*β*(ρ+1)^3*2^(widthBefore B ρ d) := by
  apply (path_cap B ρ (C*β) d p m i h0 size step).trans
  apply Nat.mul_le_mul_right
  have x : C*β+1≤(C+1)*β := by nlinarith
  have hpr := prefix_le B ρ d
  have hr := Nat.mul_le_mul_right ρ (Nat.mul_le_mul_left 2 hd)
  have cap : widthBefore B ρ d+1≤3*(C+1)*(ρ+1)^2 := by nlinarith only [hpr,hr,Nat.zero_le C,Nat.zero_le ρ,Nat.zero_le (C*ρ),Nat.zero_le (C*ρ^2),Nat.zero_le (ρ^2)]
  have t := Nat.mul_le_mul hd (Nat.mul_le_mul (Nat.mul_le_mul_left 64 x) cap)
  have one : 1≤(ρ+1)^3 := Nat.one_le_pow _ _ (by omega)
  have rest : C*β≤(C+1)^3*β*(ρ+1)^3 := calc
    _≤(C+1)^3*β := Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le (C^2),Nat.zero_le (C^3)])
    _≤_ := by simpa using Nat.mul_le_mul_left ((C+1)^3*β) one
  calc
    _≤(C+1)^3*β*(ρ+1)^3 + (C*(ρ+1))*(64*((C+1)*β)*(3*(C+1)*(ρ+1)^2)) := Nat.add_le_add rest t
    _≤_ := by
      have h := Nat.mul_le_mul_right (192*(C+1)^2*β*(ρ+1)^3) (Nat.le_succ C)
      nlinarith only [h,Nat.zero_le ((C+1)^3*β*(ρ+1)^3)]

end DetDLP.ContractionPathPrecision
end

section
namespace DetDLP.ActivePackingGeometry
open ContractionPathPrecision

theorem nextWindow (B ρ d : ℕ) : window B ρ (d+1)=window B ρ d/2 := by
  simp [window,pow_succ,Nat.div_div_eq_div_mul,Nat.mul_assoc]
theorem telescopes (B ρ d : ℕ) :
    widthBefore B ρ d+4*window B ρ d≤4*window B ρ 0 := by
  induction d with
  | zero => simp [widthBefore]
  | succ d ih => rw [widthBefore,nextWindow]; omega
theorem width_bound (B ρ d : ℕ) : B*widthBefore B ρ d≤4*ρ := by
  have hh := telescopes B ρ d
  have h := Nat.mul_le_mul_left B (show widthBefore B ρ d≤4*window B ρ 0 by omega)
  have div : B*window B ρ 0≤ρ := by simpa [window] using Nat.mul_div_le ρ B
  calc
    _≤B*(4*window B ρ 0) := h
    _=4*(B*window B ρ 0) := by ring
    _≤_ := Nat.mul_le_mul_left _ div

theorem half_absorbs : ∃ R : ℕ,∀ ρ≥R,(ρ+2)^2≤2^(ρ/2) := by
  obtain ⟨N,hN⟩ := ActiveDepthPrecision.absorbs 16 2
  refine ⟨2*N,fun ρ h => ?_⟩
  have aux : ρ+2≤4*(ρ/2+1) := by omega
  calc
    _≤(4*(ρ/2+1))^2 := Nat.pow_le_pow_left aux _
    _=16*(ρ/2+1)^2 := by ring
    _≤_ := hN _ (by omega)

theorem fit {ρ β M Δ a u : ℕ} (hΔ : 0<Δ) (hM : 0<M)
    (hs : (ρ+2)^2≤2^(ρ/2)) (ha : 48*a≤ρ) (hu : u≤ρ)
    (hsep : 2^ρ*Δ≤β) (hroot : β≤M*(ρ.sqrt+1)) :
    (a+2)*(64^a)^4*Δ≤M ∧ 2^a*(64^a)^2≤M ∧ u≤M := by
  have small : (a+2)*(ρ.sqrt+1)≤2^(ρ/2) := calc
    _≤(ρ+2)*(ρ+2) := Nat.mul_le_mul (by omega) (by have := Nat.sqrt_le_self ρ; omega)
    _≤_ := by simpa [pow_two] using hs
  have pk : (64^a)^4=2^(24*a) := by
    rw [show 64=2^6 by decide,←pow_mul,←pow_mul]; congr 1; ring
  have geom := Nat.mul_le_mul_right (2^(24*a)) small
  have expo : 2^(ρ/2)*2^(24*a)≤2^ρ := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hg : (a+2)*(64^a)^4*Δ≤M := by
    apply Nat.le_of_mul_le_mul_right (c:=ρ.sqrt+1) _ (by omega)
    calc
      _=((a+2)*(ρ.sqrt+1)*2^(24*a))*Δ := by rw [pk]; ring
      _≤2^ρ*Δ := Nat.mul_le_mul_right _ (geom.trans expo)
      _≤_ := hsep.trans hroot
  refine ⟨hg,?_,?_⟩
  · have cap : 2^a*(64^a)^2≤(64^a)^4 := by
      rw [pk,show 64=2^6 by decide,← pow_mul,← pow_mul,← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : 1≤(a+2)*Δ := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have g := Nat.mul_le_mul_left ((64^a)^4) h1
    exact cap.trans ((by simpa only [one_mul,Nat.mul_one,mul_assoc,mul_left_comm,mul_comm] using g : (64^a)^4≤(a+2)*(64^a)^4*Δ).trans hg)
  · apply Nat.le_of_mul_le_mul_right (c:=ρ.sqrt+1) _ (by omega)
    calc
      _≤(ρ+2)*(ρ+2) := Nat.mul_le_mul (by omega) (by have := Nat.sqrt_le_self ρ; omega)
      _≤2^(ρ/2) := by simpa [pow_two] using hs
      _≤2^ρ := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
      _≤2^ρ*Δ := by simpa using Nat.mul_le_mul_left (2^ρ) hΔ
      _≤_ := hsep.trans hroot

theorem full {B : ℕ} (hB : 192≤B) :
    ∃ R : ℕ,∀ (ρ β M Δ d : ℕ),R≤ρ→0<Δ→0<M→2^ρ*Δ≤β→β≤M*(ρ.sqrt+1)→
    let a := widthBefore B ρ (d+1)
    let u := window B ρ d
    (a+2)*(64^a)^4*Δ≤M ∧ 2^a*(64^a)^2≤M ∧ u≤M := by
  obtain ⟨R,h⟩ := half_absorbs
  refine ⟨R,?_⟩; intro ρ β M Δ d hρ hΔ hM hsep hroot a u
  have pr := width_bound B ρ (d+1)
  have small := Nat.mul_le_mul_right a hB
  change B*a≤4*ρ at pr
  exact fit hΔ hM (h _ hρ) (by omega) (window_le B ρ d) hsep hroot
end DetDLP.ActivePackingGeometry
end

section
namespace DetDLP.ScalarPacketParameters
open ContractionPathPrecision

noncomputable def degree (G : BipartiteMultigraph) (β : ℕ) := max G.maxDeg (Nat.ceil ((β:ℝ)^((9:ℝ)/10)))
noncomputable def scale (G : BipartiteMultigraph) (β : ℕ) :=
  max 1 (Nat.floor (Real.logb 2 ((β:ℝ)/(degree G β:ℝ))))

theorem sep (G : BipartiteMultigraph) (β : ℕ) (hβ : 0<β) (hρ : 2≤ scale G β) :
    0<degree G β ∧ 2^(scale G β)*degree G β≤β := by
  let Δ := degree G β
  let y := Real.logb 2 ((β:ℝ)/(Δ:ℝ))
  have betaPos : (0:ℝ)<β := by exact_mod_cast hβ
  have Δreal : (0:ℝ)<(Δ:ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos betaPos ((9:ℝ)/10))
    ((Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil ((β:ℝ)^((9:ℝ)/10))≤Δ from le_max_right ..)))
  have hΔ : 0<Δ := by exact_mod_cast Δreal
  have hy : 0≤ y := by
    by_contra! H
    have fl := Nat.floor_of_nonpos H.le
    change 2≤ max 1 ⌊y⌋₊ at hρ; rw [fl] at hρ; omega
  have fl : (scale G β:ℝ)≤ y := by
    have eq : scale G β=⌊y⌋₊ := by change max 1 ⌊y⌋₊=_; change 2≤ max 1 ⌊y⌋₊ at hρ; omega
    rw [eq]; exact Nat.floor_le hy
  have l := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (div_pos betaPos Δreal)).mp fl
  rw [Real.rpow_natCast] at l
  exact ⟨hΔ,by exact_mod_cast ((le_div_iff₀ Δreal).mp l)⟩

theorem packet_degree (G : BipartiteMultigraph) (β a ρ : ℕ) (hβ : 2≤β)
    (hρ : 2^ρ≤β) (ha : 2*(a+1)≤ρ) : 2*2^a≤degree G β := by
  let n := 2^(a+1)
  have hsq : n^2≤β := calc
    _ = 2^((a+1)*2) := (pow_mul ..).symm
    _ ≤ 2^ρ := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ _ := hρ
  have hb : (1:ℝ)≤β := by exact_mod_cast (show 1≤β by omega)
  have sq : (n:ℝ)^2≤(β:ℝ) := by exact_mod_cast hsq
  have le : (n:ℝ)≤Real.sqrt β := (Real.le_sqrt (by positivity) (by positivity)).mpr sq
  rw [Real.sqrt_eq_rpow] at le
  have A := Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1:ℝ)/2≤9/10)
  have hi := (le.trans A).trans (Nat.le_ceil _)
  have nat : n≤Nat.ceil ((β:ℝ)^((9:ℝ)/10)) := by exact_mod_cast hi
  calc
    _ = n := by dsimp [n]; rw [pow_succ,Nat.mul_comm]
    _ ≤ _ := nat.trans (le_max_right ..)

theorem full (C B : ℕ) (hb : 192≤B) :
    ∃ R : ℕ,∀ (G : BipartiteMultigraph) (β M d : ℕ),
    let Δ := degree G β
    let ρ := scale G β
    let a := widthBefore B ρ (d+1)
    let u := window B ρ d
    2≤β→R≤ρ→0<M→M≤C*β→β≤M*(ρ.sqrt+1)→
      (a+2)*(64^a)^4*Δ≤M ∧ 2^a*(64^a)^2≤M ∧ u≤M ∧ 2*2^a≤Δ ∧
        M*(2^(a+1)-1)+1≤2^(4*Nat.clog 2 β) := by
  obtain ⟨K,hK⟩ := ActivePackingGeometry.full hb
  refine ⟨max (max K C) 4,?_⟩
  intro G β M d Δ ρ a u hb' hρ hm hmax hroot
  obtain ⟨hΔ,space⟩ := sep G β (by omega) (by change 2≤ρ; omega)
  have pow : 2^ρ≤β := (Nat.le_mul_of_pos_right _ hΔ).trans space
  have fit := hK ρ β M Δ d (by omega) hΔ hm space hroot
  have pr := ActivePackingGeometry.width_bound B ρ (d+1)
  have left := Nat.mul_le_mul_right a hb
  change B*a≤4*ρ at pr
  have deg := packet_degree G β a ρ hb' pow (by omega)
  refine ⟨fit.1,fit.2.1,fit.2.2,deg,?_⟩
  have aux : ∀ j : ℕ,j≤2^j := by
    intro j; induction j with
    | zero => decide
    | succ j ih => rw [pow_succ]; have := @Nat.one_le_two_pow j; omega
  have small : C≤β := (show C≤ρ by omega).trans ((aux ρ).trans pow)
  have count : 2^(a+1)-1≤β := (Nat.sub_le _ _).trans
    ((Nat.pow_le_pow_right (by decide) (by omega : a+1≤ρ)).trans pow)
  have bounds := Nat.mul_le_mul (hmax.trans (Nat.mul_le_mul_right β small)) count
  have adv : M*(2^(a+1)-1)+1≤β^4 := by
    have grow := Nat.mul_le_mul_left (β^3) hb'
    have pos : 1≤β^3 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [bounds,grow,pos]
  have g := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) β) 4
  rw [← pow_mul,Nat.mul_comm (Nat.clog 2 β)] at g; exact adv.trans g
end DetDLP.ScalarPacketParameters
end

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

namespace DetDLP.TerminalCoreCut
open Finset
variable (G : BipartiteMultigraph) (L : Finset (Fin G.nV))

def boundary (e : Fin G.nE) : Prop := (G.endpoints e).1∈L ∨ (G.endpoints e).2∈L
instance (e : Fin G.nE) : Decidable (boundary G L e) := inferInstanceAs (Decidable (_ ∨ _))
abbrev B := {e : Fin G.nE // boundary G L e}
abbrev I := {e : Fin G.nE // ¬boundary G L e}
abbrev V := {v : Fin G.nV // v∉L}

noncomputable def vertEquiv := Fintype.equivFin (V G L)
noncomputable def edgeEquiv := Fintype.equivFin (I G L)

def incident (v : Fin G.nV) (e : Fin G.nE) : Prop := (G.endpoints e).1=v ∨ (G.endpoints e).2=v
theorem atPort (v : Fin G.nV) (i : Fin (G.deg v)) : incident G v ((G.ports v).get i) := by
  simpa [BipartiteMultigraph.ports,incident] using List.get_mem (G.ports v) i

noncomputable def core : BipartiteMultigraph where
  nV := Fintype.card (V G L)
  nE := Fintype.card (I G L)
  endpoints j :=
    let e := (edgeEquiv G L).symm j
    (vertEquiv G L ⟨(G.endpoints e.val).1,fun h => e.property (Or.inl h)⟩,
     vertEquiv G L ⟨(G.endpoints e.val).2,fun h => e.property (Or.inr h)⟩)
  side v := G.side ((vertEquiv G L).symm v).val
  bipartite j := by simp; apply G.bipartite

theorem core_inc (v : V G L) (e : I G L) :
    incident (core G L) (vertEquiv G L v) (edgeEquiv G L e) ↔ incident G v.val e.val := by
  simp [incident,core,Subtype.ext_iff]

noncomputable def joinBits (η : B G L→Bool) (x : I G L→Bool) (e : Fin G.nE) : Bool :=
  if h : boundary G L e then η ⟨e,h⟩ else x ⟨e,h⟩

variable {R : Type} [CommRing R] (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→R)
def lookupTensor (η : B G L→Bool) (v : ↥L) : R := T v.val fun j =>
  let e := (G.ports v.val).get j
  η ⟨e,by
    rcases atPort G v.val j with h|h
    · exact Or.inl ((congrArg (fun v => v∈L) h).mpr v.property)
    · exact Or.inr ((congrArg (fun v => v∈L) h).mpr v.property)⟩

def lifted (η : B G L→Bool) (v : V G L) (read : I G L→Bool) : R :=
  T v.val fun j =>
    let e := (G.ports v.val).get j
    if h : boundary G L e then η ⟨e,h⟩ else read ⟨e,h⟩

noncomputable def coreTensor (η : B G L→Bool) (v : Fin (core G L).nV)
    (α : Fin ((core G L).deg v)→Bool) : R :=
  lifted G L T η ((vertEquiv G L).symm v) fun e =>
    ResidualChildGraph.supplied (core G L) v α (edgeEquiv G L e)

set_option backward.isDefEq.respectTransparency false in
theorem coreEntry (v : V G L) (η : B G L→Bool) (x : I G L→Bool) :
    coreTensor G L T η (vertEquiv G L v) (fun j =>
      x ((edgeEquiv G L).symm (((core G L).ports (vertEquiv G L v)).get j))) =
    T v.val (fun j => joinBits G L η x ((G.ports v.val).get j)) := by
  unfold coreTensor
  rw [(vertEquiv G L).symm_apply_apply v]
  unfold lifted
  apply congrArg (T v.val); funext j
  let e := (G.ports v.val).get j
  by_cases h : boundary G L e
  · dsimp only [e] at h; simp only [joinBits,dif_pos h]
  · dsimp only [e] at h; simp only [joinBits,dif_neg h]
    have d := (core_inc G L v ⟨e,h⟩).mpr (atPort G _ j)
    have mem : edgeEquiv G L ⟨e,h⟩∈(core G L).ports (vertEquiv G L v) := by
      simpa [BipartiteMultigraph.ports,incident] using d
    rw [ResidualChildGraph.supplied,dif_pos mem,List.idxOf_get,Equiv.symm_apply_apply]

theorem coreValue (η : B G L→Bool) :
    BTNContract (core G L) (coreTensor G L T η) =
      ∑ x : I G L→Bool,∏ v : V G L,T v.val (fun j => joinBits G L η x ((G.ports v.val).get j)) := by
  classical
  let e := edgeEquiv G L
  let re := e.arrowCongr (Equiv.refl Bool)
  unfold BTNContract; symm
  apply Fintype.sum_equiv re; intro x
  apply Fintype.prod_equiv (vertEquiv G L); intro v
  exact (coreEntry G L T v η x).symm

private theorem sameProduct {A : Type} (a b : Fintype A) (f g : A→R) (h : ∀ x,f x=g x) :
    (@univ A a).prod f=(@univ A b).prod g := by
  cases Subsingleton.elim a b
  exact prod_congr rfl fun x _ => h x

theorem cut :
    BTNContract G T = ∑ η : B G L→Bool,(∏ v : {v : Fin G.nV // v∈L},lookupTensor G L T η v)*
      BTNContract (core G L) (coreTensor G L T η) := by
  classical
  let W (x : Fin G.nE→Bool) (v : Fin G.nV) := T v (fun j => x ((G.ports v).get j))
  let e := Equiv.piEquivPiSubtypeProd (boundary G L) (fun _ => Bool)
  have eq (z : (B G L→Bool)×(I G L→Bool)) : e.symm z=joinBits G L z.1 z.2 := by
    funext j; by_cases h : boundary G L j <;> simp [e,Equiv.piEquivPiSubtypeProd,joinBits,h]
  change ∑ x,∏ v,W x v=_
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  apply sum_congr rfl; intro η _
  rw [coreValue,mul_sum]; apply sum_congr rfl; intro x _
  rw [eq]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : Fin G.nV => v∈L)]
  congr 1
  apply sameProduct; intro v
  unfold W lookupTensor; apply congrArg (T v.val); funext j
  have h : boundary G L ((G.ports v.val).get j) := by
    rcases atPort G v.val j with h|h
    · exact Or.inl ((congrArg (fun v => v∈L) h).mpr v.property)
    · exact Or.inr ((congrArg (fun v => v∈L) h).mpr v.property)
  simp [joinBits,h]
end DetDLP.TerminalCoreCut
end

section

namespace DetDLP.TerminalCoreGeometry
open TerminalCoreCut Finset
variable {G : BipartiteMultigraph} {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D)
abbrev L := s.lookupVerts
abbrev terminal := ↥s.termSubdivVerts

def host (e : B G s.lookupVerts) : terminal s :=
  if h : (G.endpoints e.val).1∈s.lookupVerts then
    ⟨_,(s.lookup_edges_to_subdiv e.val).1 h⟩
  else ⟨_,(s.lookup_edges_to_subdiv e.val).2 (e.property.resolve_left h)⟩

def crosses (v : Fin G.nV) (e : Fin G.nE) : Prop :=
  ((G.endpoints e).1=v ∧ (G.endpoints e).2∈s.lookupVerts) ∨
  ((G.endpoints e).2=v ∧ (G.endpoints e).1∈s.lookupVerts)

theorem host_spec (e : B G s.lookupVerts) : crosses s (host s e).val e.val := by
  by_cases h : (G.endpoints e.val).1∈s.lookupVerts
  · exact Or.inr ⟨by simp [host,h],h⟩
  · exact Or.inl ⟨by simp [host,h],e.property.resolve_left h⟩

theorem host_unique {v : Fin G.nV} (hv : v∉s.lookupVerts) (e : B G s.lookupVerts) :
    incident G v e.val ↔ (host s e).val=v := by
  obtain ⟨a,b⟩|⟨a,b⟩ := host_spec s e
  · constructor
    · rintro (h|h)
      · exact a.symm.trans h
      · exact False.elim (hv (h ▸ b))
    · intro h; exact Or.inl (a.trans h)
  · constructor
    · rintro (h|h)
      · exact False.elim (hv (h ▸ b))
      · exact a.symm.trans h
    · intro h; exact Or.inr (a.trans h)

theorem uniqueEdge (v : terminal s) : ∃! e : Fin G.nE,crosses s v.val e := by
  simpa [crosses] using card_eq_one_iff_existsUnique.mp (s.subdiv_one_lookup_edge v.val v.property)

theorem host_bijective : Function.Bijective (host s) := by
  constructor
  · intro e e' h
    apply Subtype.ext
    obtain ⟨a,_,ha⟩ := uniqueEdge s (host s e)
    exact (ha _ (host_spec s e)).trans (ha _ (h ▸ host_spec s e')).symm
  · intro v
    obtain ⟨e,he,_⟩ := uniqueEdge s v
    have vb : v.val∉s.lookupVerts := fun H => Finset.disjoint_left.mp s.disjoint_verts H v.property
    obtain ⟨h,hl⟩|⟨h,hl⟩ := he
    · let b : B G s.lookupVerts := ⟨e,Or.inr hl⟩
      exact ⟨b,Subtype.ext ((host_unique s vb b).mp (Or.inl h))⟩
    · let b : B G s.lookupVerts := ⟨e,Or.inl hl⟩
      exact ⟨b,Subtype.ext ((host_unique s vb b).mp (Or.inr h))⟩

theorem boundary_card : Fintype.card (B G s.lookupVerts)=4*m*k := by
  rw [Fintype.card_congr (Equiv.ofBijective _ (host_bijective s))]
  exact (Fintype.card_coe _).trans s.card_termSubdiv

theorem core_edges : (core G s.lookupVerts).nE≤S := by
  change Fintype.card (I G s.lookupVerts)≤S
  rw [Fintype.card_subtype]
  simpa [boundary,not_or] using s.core_edges_le

theorem core_vertices : (core G s.lookupVerts).nV≤G.nV := by
  exact (Fintype.card_subtype_le (fun v : Fin G.nV => v∉s.lookupVerts)).trans_eq (Fintype.card_fin G.nV)

theorem ports_inj (H : BipartiteMultigraph) (v : Fin H.nV) :
    Function.Injective ((H.ports v).get) := by
  have hn : (H.ports v).Nodup := (List.nodup_finRange _).filter _
  exact hn.injective_get

theorem core_degrees (v : V G s.lookupVerts) :
    (core G s.lookupVerts).deg (vertEquiv G s.lookupVerts v)≤G.deg v.val := by
  let H := core G s.lookupVerts
  let w := vertEquiv G s.lookupVerts v
  let read (j : Fin (H.deg w)) := (edgeEquiv G s.lookupVerts).symm ((H.ports w).get j)
  have old (j : Fin (H.deg w)) : (read j).val∈G.ports v.val := by
    have h := atPort H w j
    have e := (core_inc G s.lookupVerts v (read j)).mp ((congrArg (incident H w) ((edgeEquiv G s.lookupVerts).apply_symm_apply ((H.ports w).get j))).mpr h)
    simpa [BipartiteMultigraph.ports,incident] using e
  let idx (j : Fin (H.deg w)) : Fin (G.deg v.val) :=
    ⟨(G.ports v.val).idxOf (read j).val,List.idxOf_lt_length_iff.mpr (old j)⟩
  have inj : Function.Injective idx := by
    intro a b h
    have eq := congrArg (G.ports v.val).get h
    change (G.ports v.val).get ⟨_,_⟩=(G.ports v.val).get ⟨_,_⟩ at eq
    simp only [idx,List.idxOf_get] at eq
    apply ports_inj H w
    apply (edgeEquiv G s.lookupVerts).symm.injective
    exact Subtype.ext eq
  simpa using Fintype.card_le_of_injective idx inj

theorem max_degree : (core G s.lookupVerts).maxDeg≤D := by
  apply Finset.sup_le; intro j _
  obtain ⟨v,rfl⟩ := (vertEquiv G s.lookupVerts).surjective j
  exact (core_degrees s v).trans (s.core_deg_le v.val v.property)
end DetDLP.TerminalCoreGeometry
end

section
namespace DetDLP.ContractionPortCounts
open Finset OrientedPacketInstance
variable {a r : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable (i : Fin a) (tag : P→Fin r×Fin r) (active : P→Finset (Pos a))
variable (G : BipartiteMultigraph) (layout : Fin G.nE ≃ Address active) (grp : Fin G.nV→Fin r)
abbrev Ports (g : Fin r) := Assigned i tag active g
abbrev Compat := ∀ e d,group i (tag (layout e).1) d (layout e).2.val.val=grp (endpoint G e d)
variable (align : Compat i tag active G layout grp)

theorem endpoint_side (e : Fin G.nE) (d : Bool) : G.side (endpoint G e d)=d := by
  unfold endpoint
  have h := G.bipartite e
  split_ifs with hd
  · exact hd
  · cases hr : G.side (G.endpoints e).1 <;> cases hl : G.side (G.endpoints e).2 <;> cases d <;> simp_all

def edge {g : Fin r} (e : Ports i tag active g) : Fin G.nE := layout.symm ⟨e.val.1,e.val.2.1,e.property.1⟩
include align in
theorem identify {g : Fin r} (e : Ports i tag active g) :
    grp (endpoint G (edge i tag active G layout e) e.val.2.2)=g := by
  let address : Address active := ⟨e.val.1,e.val.2.1,e.property.1⟩
  exact (align (layout.symm address) e.val.2.2).symm.trans
    ((congrArg (fun z : Address active => group i (tag z.1) e.val.2.2 z.2.val.val) (layout.apply_symm_apply address)).trans e.property.2)

theorem recover_address {g : Fin r} (e : Ports i tag active g) :
    layout (edge i tag active G layout e)=⟨e.val.1,e.val.2.1,e.property.1⟩ :=
  layout.apply_symm_apply _

theorem unique_port {g : Fin r} {e f : Ports i tag active g}
    (he : edge i tag active G layout e=edge i tag active G layout f) (hd : e.val.2.2=f.val.2.2) : e=f := by
  have u := congrArg layout he
  rw [recover_address,recover_address] at u
  have hq := congrArg (fun v : Address active => v.1) u
  have hk := congrArg (fun v : Address active => v.2.val) u
  exact Subtype.ext (Prod.ext hq (Prod.ext hk hd))

def marked (z : Address active) (d : Bool) : Σ g,Ports i tag active g :=
  ⟨_,⟨(z.1,z.2.val,d),z.2.property,rfl⟩⟩
def portsEquiv : (Σ g,Ports i tag active g) ≃ (Fin G.nE×Bool) where
  toFun e := (edge i tag active G layout e.2,e.2.val.2.2)
  invFun z := marked i tag active (layout z.1) z.2
  left_inv e := by
    obtain ⟨g,⟨⟨q,k,d⟩,hk,hg⟩⟩ := e
    dsimp only at hg
    subst g; exact congrArg (fun u => marked i tag active u d) (layout.apply_symm_apply ⟨q,k,hk⟩)
  right_inv e := by
    obtain ⟨j,d⟩ := e
    exact Prod.ext (layout.symm_apply_apply _) rfl

include layout in
theorem mass : (∑ g,Fintype.card (Ports i tag active g))=2*G.nE := by
  rw [← Fintype.card_sigma,Fintype.card_congr (portsEquiv i tag active G layout)]; simp [mul_comm]

def sidePorts (g : Fin r) (d : Bool) := {e : Fin G.nE // grp (endpoint G e d)=g}
instance (g : Fin r) (d : Bool) : Fintype (sidePorts G grp g d) := inferInstanceAs (Fintype {e : Fin G.nE // _})
include align in
theorem group_cap (g : Fin r) :
    Fintype.card (Ports i tag active g)≤Fintype.card (sidePorts G grp g false)+Fintype.card (sidePorts G grp g true) := by
  let f (e : Ports i tag active g) : (sidePorts G grp g false) ⊕ (sidePorts G grp g true) :=
    if hd : e.val.2.2=true then .inr ⟨edge i tag active G layout e,hd ▸ identify i tag active G layout grp align e⟩
    else .inl ⟨edge i tag active G layout e,(Bool.eq_false_iff.mpr hd) ▸ identify i tag active G layout grp align e⟩
  have hf : Function.Injective f := by
    intro e k H
    obtain h|h := Bool.eq_false_or_eq_true e.val.2.2 <;> obtain l|l := Bool.eq_false_or_eq_true k.val.2.2 <;>
      simp [f,h,l] at H <;> apply unique_port i tag active G layout _ (h.trans l.symm)
    · exact congrArg (fun x : sidePorts G grp g true => x.val) (Sum.inr.inj H)
    · exact congrArg (fun x : sidePorts G grp g false => x.val) (Sum.inl.inj H)
  simpa using Fintype.card_le_of_injective f hf

theorem packet_cap (g : Fin r) (q : P) :
    Fintype.card {e : Ports i tag active g // e.val.1=q}≤2*2^a := by
  let f (e : {e : Ports i tag active g // e.val.1=q}) := e.val.val.2
  have H : Function.Injective f := by intro e k h; exact Subtype.ext (Subtype.ext (Prod.ext (e.property.trans k.property.symm) h))
  simpa [f,Pos,mul_comm] using Fintype.card_le_of_injective f H

theorem owner_cap (g : Fin r) (v : Fin G.nV) :
    Fintype.card {e : Ports i tag active g // endpoint G (edge i tag active G layout e) e.val.2.2=v}≤G.deg v := by
  let J := {e : Ports i tag active g // endpoint G (edge i tag active G layout e) e.val.2.2=v}
  have mem (e : J) : edge i tag active G layout e.val∈G.ports v := by
    have hv := e.property
    simp only [endpoint] at hv
    simp only [BipartiteMultigraph.ports,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    split at hv <;> tauto
  let f (e : J) : Fin (G.deg v) := ⟨(G.ports v).idxOf (edge i tag active G layout e.val),List.idxOf_lt_length_iff.mpr (mem e)⟩
  have H : Function.Injective f := by
    intro e k h; apply Subtype.ext
    have E := congrArg (G.ports v).get h
    change (G.ports v).get ⟨_,_⟩=(G.ports v).get ⟨_,_⟩ at E
    simp only [List.idxOf_get] at E
    have both (e : J) : e.val.val.2.2=G.side v :=
      (endpoint_side G _ _).symm.trans (congrArg G.side e.property)
    exact unique_port i tag active G layout E ((both e).trans (both k).symm)
  simpa using Fintype.card_le_of_injective f H
end DetDLP.ContractionPortCounts
end

section

namespace DetDLP.LocalLabelSearch
open Finset

/-- Each penalty depends on at most four vertex labels. -/
structure Term (n q : ℕ) where
  arity : ℕ
  small : arity ≤ 4
  vertex : Fin arity → Fin n
  distinct : Function.Injective vertex
  penalty : (Fin arity → Fin q) → ℕ

abbrev Partial (n q : ℕ) := Fin n → Option (Fin q)

def termScore {n q : ℕ} (t : Term n q) (s : Partial n q) : ℕ :=
  q^(4-t.arity) * ∑ z : Fin t.arity → Fin q,
    t.penalty (fun h => (s (t.vertex h)).getD (z h))

def score {n q : ℕ} (T : List (Term n q)) (s : Partial n q) : ℕ :=
  (T.map (termScore · s)).sum

private def swapAt {q r : ℕ} (h : Fin r) : (Fin q × (Fin r → Fin q)) ≃ (Fin q × (Fin r → Fin q)) where
  toFun x := (x.2 h, Function.update x.2 h x.1)
  invFun x := (x.2 h, Function.update x.2 h x.1)
  left_inv x := by simp
  right_inv x := by simp

private theorem term_average {n q : ℕ} (t : Term n q) (s : Partial n q)
    (v : Fin n) (fresh : s v = none) :
    ∑ x : Fin q, termScore t (Function.update s v (some x)) = q * termScore t s := by
  classical
  let f (z : Fin t.arity → Fin q) := t.penalty fun h => (s (t.vertex h)).getD (z h)
  by_cases hm : ∃ h, t.vertex h = v
  · obtain ⟨h,rfl⟩ := hm
    have he (x : Fin q) (z : Fin t.arity → Fin q) :
        t.penalty (fun a => (Function.update s (t.vertex h) (some x) (t.vertex a)).getD (z a)) =
        f (Function.update z h x) := by
      congr 1
      funext a
      by_cases ha : a = h
      · simp [ha,fresh]
      · simp [Function.update_of_ne ha,Function.update_of_ne (t.distinct.ne ha)]
    have hsum : ∑ x : Fin q, ∑ z : Fin t.arity → Fin q, f (Function.update z h x) =
        q * ∑ z : Fin t.arity → Fin q, f z := by
      let F (a : Fin q × (Fin t.arity → Fin q)) := f a.2
      calc
        _ = ∑ a : Fin q × (Fin t.arity → Fin q), F (swapAt h a) := Fintype.sum_prod_type _ |>.symm
        _ = ∑ a : Fin q × (Fin t.arity → Fin q), F a := (swapAt h).sum_comp F
        _ = _ := by rw [Fintype.sum_prod_type]; simp [F]
    unfold termScore
    simp_rw [he]
    rw [← mul_sum,hsum]
    dsimp only [f]
    ring
  · have he (x : Fin q) : termScore t (Function.update s v (some x)) = termScore t s := by
      unfold termScore
      congr 1
      apply sum_congr rfl
      intro z _
      congr 1; funext h
      rw [Function.update_of_ne (fun h' => hm ⟨h,h'⟩)]
    simp [he]

theorem score_average {n q : ℕ} (T : List (Term n q)) (s : Partial n q)
    (v : Fin n) (h : s v = none) :
    ∑ x : Fin q, score T (Function.update s v (some x)) = q * score T s := by
  induction T with
  | nil => simp [score]
  | cons t ts ih =>
    simp only [score,List.map_cons,List.sum_cons] at ih ⊢
    rw [sum_add_distrib,term_average t s v h,ih,Nat.mul_add]

private def better {q : ℕ} (f : Fin q → ℕ) (x y : Fin q) := if f y < f x then y else x

private theorem fold_min {q : ℕ} (f : Fin q → ℕ) (xs : List (Fin q)) (start : Fin q) :
    let z := xs.foldl (better f) start
    f z ≤ f start ∧ ∀ x ∈ xs, f z ≤ f x := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h0,h1⟩ := ih (better f start x)
    have hl : f (better f start x) ≤ f start ∧ f (better f start x) ≤ f x := by
      unfold better; split <;> omega
    exact ⟨h0.trans hl.1,fun y h => by
      rcases List.mem_cons.mp h with rfl|h
      · exact h0.trans hl.2
      · exact h1 y h⟩

def chooseLabel {n q : ℕ} [NeZero q] (T : List (Term n q)) (s : Partial n q) (v : Fin n) :=
  let cost (x : Fin q) := score T (Function.update s v (some x))
  (List.finRange q).foldl (better cost) 0

theorem chooseLabel_le {n q : ℕ} [NeZero q] (T : List (Term n q)) (s : Partial n q) (v : Fin n)
    (hf : s v = none) :
    score T (Function.update s v (some (chooseLabel T s v))) ≤ score T s := by
  let f (x : Fin q) := score T (Function.update s v (some x))
  let x := chooseLabel T s v
  have hl (y : Fin q) : f x ≤ f y :=
    (fold_min f (List.finRange q) 0).2 y (by simp)
  have hs : q*f x ≤ q*score T s := by
    rw [← score_average T s v hf,← show (∑ _ : Fin q, f x)=q*f x by simp]
    exact sum_le_sum (fun y _ => hl y)
  exact Nat.le_of_mul_le_mul_left hs (Nat.pos_of_ne_zero (NeZero.ne q))

def fixLabels {n q : ℕ} [NeZero q] (T : List (Term n q)) : ℕ → Partial n q
  | 0 => fun _ => none
  | k+1 =>
    let s := fixLabels T k
    if h : k < n then Function.update s ⟨k,h⟩ (some (chooseLabel T s ⟨k,h⟩)) else s

theorem fixLabels_spec {n q : ℕ} [NeZero q] (T : List (Term n q)) (k : ℕ) (hk : k ≤ n) :
    (∀ i : Fin n, (fixLabels T k i).isSome ↔ i.val < k) ∧
    score T (fixLabels T k) ≤ score T (fun _ => none) := by
  induction k with
  | zero => simp [fixLabels]
  | succ k ih =>
    have h : k < n := by omega
    obtain ⟨hset,hscore⟩ := ih (by omega)
    let v : Fin n := ⟨k,h⟩
    have hf : fixLabels T k v = none := by
      cases he : fixLabels T k v with
      | none => rfl
      | some x => have hh := (hset v).mp (by simp [he]); exact False.elim (lt_irrefl k hh)
    simp only [fixLabels,dif_pos h]
    refine ⟨fun i => ?_,(chooseLabel_le T _ v hf).trans hscore⟩
    by_cases he : i = v
    · subst i; simp [v]
    · rw [Function.update_of_ne he,hset]
      have hv : i.val ≠ k := fun e => he (Fin.ext e)
      omega

def labeling {n q : ℕ} [NeZero q] (T : List (Term n q)) : Fin n → Fin q :=
  fun v => (fixLabels T n v).getD 0

/-- The executable search attains at most the average score of all assignments;
each trial inspects at most q^4 local tuples per term. -/
theorem labeling_bound {n q : ℕ} [NeZero q] (T : List (Term n q)) :
    q^4 * (T.map (fun t => t.penalty (fun h => labeling T (t.vertex h)))).sum ≤
    score T (fun _ => none) := by
  obtain ⟨hfill,h⟩ := fixLabels_spec T n le_rfl
  have hs (v : Fin n) : fixLabels T n v = some (labeling T v) := by
    have hv := (hfill v).mpr v.isLt
    cases he : fixLabels T n v <;> simp_all [labeling]
  have ht (t : Term n q) : termScore t (fixLabels T n) = q^4 * t.penalty (fun h => labeling T (t.vertex h)) := by
    simp [termScore,hs,Fintype.card_fun,← mul_assoc,← pow_add, Nat.sub_add_cancel t.small]
  have sum_eq (ts : List (Term n q)) :
      score ts (fixLabels T n) = q^4*(ts.map (fun t => t.penalty (fun h => labeling T (t.vertex h)))).sum := by
    induction ts with
    | nil => simp [score]
    | cons t ts ih =>
      simp only [score,List.map_cons,List.sum_cons] at ih ⊢
      rw [ht,ih,Nat.mul_add]
  rw [sum_eq] at h
  exact h

end DetDLP.LocalLabelSearch
end

section

namespace DetDLP.EdgeLabelPartition
open Finset LocalLabelSearch

private def left (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
private def right (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2

private theorem left_side (G : BipartiteMultigraph) (e : Fin G.nE) : G.side (left G e) = false := by
  have h := G.bipartite e
  cases ha : G.side (G.endpoints e).1 <;> cases hb : G.side (G.endpoints e).2 <;> simp_all [left]
private theorem right_side (G : BipartiteMultigraph) (e : Fin G.nE) : G.side (right G e) = true := by
  have h := G.bipartite e
  cases ha : G.side (G.endpoints e).1 <;> cases hb : G.side (G.endpoints e).2 <;> simp_all [right]
private theorem lr_ne (G : BipartiteMultigraph) (e f : Fin G.nE) : left G e ≠ right G f := by
  intro h
  have he := left_side G e
  rw [h,right_side] at he
  contradiction

private def eqTwo {q : ℕ} (z : Fin 2 → Fin q) : ℕ := if z 0 = z 1 then 1 else 0
private def eqFour {q : ℕ} (z : Fin 4 → Fin q) : ℕ :=
  if z 0 = z 1 ∧ z 2 = z 3 then 1 else 0

private theorem sum_eqTwo (q : ℕ) : ∑ z : Fin 2 → Fin q, eqTwo z = q := by
  classical
  let e : {z : Fin 2 → Fin q // z 0 = z 1} ≃ Fin q :=
    { toFun z := z.1 0, invFun x := ⟨![x,x],rfl⟩
      left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> simp [z.property]
      right_inv _ := rfl }
  have hh := Fintype.card_congr e
  simpa [eqTwo,Fintype.card_subtype,Finset.sum_boole] using hh

private theorem sum_eqFour (q : ℕ) : ∑ z : Fin 4 → Fin q, eqFour z = q^2 := by
  classical
  let e : {z : Fin 4 → Fin q // z 0 = z 1 ∧ z 2 = z 3} ≃ Fin q × Fin q :=
    { toFun z := (z.1 0,z.1 2), invFun x := ⟨![x.1,x.1,x.2,x.2],rfl,rfl⟩
      left_inv z := by apply Subtype.ext; funext i; fin_cases i <;> simp [z.property.1,z.property.2]
      right_inv _ := rfl }
  have hh := Fintype.card_congr e
  simpa [eqFour,Fintype.card_subtype,Finset.sum_boole,pow_two] using hh

private def constantTerm (n q : ℕ) : Term n q :=
  ⟨0,by decide,Fin.elim0,fun x => Fin.elim0 x,fun _ => 1⟩

private def pairTerm {n q : ℕ} (x y : Fin n) (h : x ≠ y) : Term n q :=
  ⟨2,by decide,![x,y],by intro i j; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm h],eqTwo⟩

private def fourTerm (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE)
    (hl : left G e ≠ left G f) (hr : right G e ≠ right G f) : Term G.nV q :=
  ⟨4,by decide,![left G e,left G f,right G e,right G f],by
      intro x y
      fin_cases x <;> fin_cases y <;> simp_all [lr_ne,Ne.symm hl,Ne.symm hr,Ne.symm (lr_ne G _ _)],eqFour⟩

private def edgeTerm (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE) : Term G.nV q :=
  if hl : left G e = left G f then
    if hr : right G e = right G f then constantTerm _ _ else pairTerm _ _ hr
  else if hr : right G e = right G f then pairTerm _ _ hl
  else fourTerm G q e f hl hr

private def pairCollision (G : BipartiteMultigraph) {q : ℕ} (e f : Fin G.nE) (L : Fin G.nV → Fin q) : ℕ :=
  if (L (left G e),L (right G e)) = (L (left G f),L (right G f)) then 1 else 0

private theorem cost_edge (G : BipartiteMultigraph) (q : ℕ) (e f : Fin G.nE)
    (L : Fin G.nV → Fin q) :
    (edgeTerm G q e f).penalty (fun i => L ((edgeTerm G q e f).vertex i)) =
    pairCollision G e f L := by
  by_cases hl : left G e = left G f
  · by_cases hr : right G e = right G f
    · have he : edgeTerm G q e f = constantTerm _ _ := by rw [edgeTerm,dif_pos hl,dif_pos hr]
      rw [he]; simp [constantTerm,pairCollision,hl,hr]
    · have he : edgeTerm G q e f = pairTerm _ _ hr := by rw [edgeTerm,dif_pos hl,dif_neg hr]
      rw [he]; simp [pairTerm,pairCollision,eqTwo,hl]
  · by_cases hr : right G e = right G f
    · have he : edgeTerm G q e f = pairTerm _ _ hl := by rw [edgeTerm,dif_neg hl,dif_pos hr]
      rw [he]; simp [pairTerm,pairCollision,eqTwo,hr]
    · have he : edgeTerm G q e f = fourTerm G q e f hl hr := by rw [edgeTerm,dif_neg hl,dif_neg hr]
      rw [he]; simp [fourTerm,pairCollision,eqFour,Prod.ext_iff]
      by_cases h : L (left G e) = L (left G f) <;> by_cases k : L (right G e) = L (right G f) <;> simp_all [h,k]

private theorem initial_edge (G : BipartiteMultigraph) (q : ℕ) [NeZero q] (e f : Fin G.nE) :
    termScore (edgeTerm G q e f) (fun _ => none) ≤
      q^2 + (if left G e = left G f ∨ right G e = right G f then q^4 else 0) := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hm : q^2*q ≤ q^4 := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right hq (by decide)
  have hs2 : (∑ z : Fin 2 → Fin q, eqTwo (fun h => z h)) = q := sum_eqTwo q
  have hs4 : (∑ z : Fin 4 → Fin q, eqFour (fun h => z h)) = q^2 := sum_eqFour q
  have hs0 : (∑ _ : Fin 0 → Fin q, 1 : ℕ) = 1 := by simp [Fintype.card_fun]
  have hc : termScore (constantTerm G.nV q) (fun _ => none) = q^4 := by
    change q^(4-0) * (∑ _ : Fin 0 → Fin q, 1 : ℕ) = q^4
    rw [hs0]; simp
  have hp (x y : Fin G.nV) (h : x ≠ y) : termScore (pairTerm (q := q) x y h) (fun _ => none) = q^2*q := by
    change q^2 * (∑ z : Fin 2 → Fin q, eqTwo z) = _
    rw [sum_eqTwo]
  by_cases hl : left G e = left G f
  · by_cases hr : right G e = right G f
    · rw [edgeTerm,dif_pos hl,dif_pos hr,hc,if_pos (Or.inl hl)]; omega
    · rw [edgeTerm,dif_pos hl,dif_neg hr,hp,if_pos (Or.inl hl)]; omega
  · by_cases hr : right G e = right G f
    · rw [edgeTerm,dif_neg hl,dif_pos hr,hp,if_pos (Or.inr hr)]; omega
    · rw [edgeTerm,dif_neg hl,dif_neg hr,if_neg (by tauto),add_zero]
      change q^(4-4) * (∑ z : Fin 4 → Fin q, eqFour z) ≤ _
      rw [sum_eqFour]; simp

private def edgePairs (G : BipartiteMultigraph) :=
  (List.finRange G.nE).flatMap fun e => (List.finRange G.nE).map fun f => (e,f)

private def terms (G : BipartiteMultigraph) (q : ℕ) :=
  (edgePairs G).map fun p => edgeTerm G q p.1 p.2

private theorem pair_sum {n : ℕ} (f : Fin n × Fin n → ℕ) :
    (((List.finRange n).flatMap fun e => (List.finRange n).map fun z => (e,z)).map f).sum =
    ∑ e, ∑ z, f (e,z) := by
  have hf (l : List (Fin n)) : (l.flatMap (fun a => (List.finRange n).map (fun z => f (a,z)))).sum =
      (l.map fun a => ((List.finRange n).map fun z => f (a,z)).sum).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simpa [List.map_flatMap,List.map_map,Function.comp_def,Fin.sum_univ_def] using hf (List.finRange n)

private theorem shared_subset (G : BipartiteMultigraph) (e f : Fin G.nE)
    (h : left G e = left G f ∨ right G e = right G f) :
    f ∈ G.ports (left G e) ∨ f ∈ G.ports (right G e) := by
  rcases h with hl|hr
  · left; rw [hl]; cases h : G.side (G.endpoints f).1 <;> simp [BipartiteMultigraph.ports,left,h]
  · right; rw [hr]; cases h : G.side (G.endpoints f).1 <;> simp [BipartiteMultigraph.ports,right,h]

private theorem ports_card (G : BipartiteMultigraph) (v : Fin G.nV) :
    (G.ports v).toFinset.card ≤ G.maxDeg := by
  refine (List.toFinset_card_le _).trans ?_
  change G.deg v ≤ (univ : Finset (Fin G.nV)).sup G.deg
  exact Finset.le_sup (f := G.deg) (Finset.mem_univ v)

private theorem shared_card (G : BipartiteMultigraph) (e : Fin G.nE) :
    (univ.filter fun f => left G e = left G f ∨ right G e = right G f).card ≤ 2*G.maxDeg := by
  let S := (G.ports (left G e)).toFinset
  let T := (G.ports (right G e)).toFinset
  have h : (univ.filter fun f => left G e = left G f ∨ right G e = right G f) ⊆ S ∪ T := by
    intro f hf
    simpa [S,T] using shared_subset G e f (mem_filter.mp hf).2
  calc
    _ ≤ (S ∪ T).card := card_le_card h
    _ ≤ S.card+T.card := card_union_le _ _
    _ ≤ _ := by have := ports_card G (left G e); have := ports_card G (right G e); dsimp [S,T]; omega

/-- Ordered pairs of edges sharing both endpoint labels. -/
def collisions (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) : ℕ :=
  ∑ e : Fin G.nE, ∑ f : Fin G.nE, pairCollision G e f L

def labels (G : BipartiteMultigraph) (q : ℕ) [NeZero q] : Fin G.nV → Fin q := labeling (terms G q)

private theorem initial_edge_sum (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    score (terms G q) (fun _ => none) ≤ G.nE*(G.nE*q^2+2*G.maxDeg*q^4) := by
  have per (e : Fin G.nE) :
      (∑ f : Fin G.nE, termScore (edgeTerm G q e f) (fun _ => none)) ≤
        G.nE*q^2 + 2*G.maxDeg*q^4 := by
    calc
      _ ≤ ∑ f : Fin G.nE, (q^2 + if left G e = left G f ∨ right G e = right G f then q^4 else 0) :=
        sum_le_sum fun f _ => initial_edge G q e f
      _ ≤ _ := by
        rw [sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,add_zero]
        simp only [Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        simpa using Nat.add_le_add_left (Nat.mul_le_mul_right (q^4) (shared_card G e)) (G.nE*q^2)
  have hs := sum_le_sum (s := univ) (fun e _ => per e)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_cast at hs
  simpa only [score,terms,edgePairs,List.map_map,Function.comp_def,pair_sum] using hs
private def finalScore {n q : ℕ} (ts : List (Term n q)) (L : Fin n → Fin q) :=
  (ts.map (fun t => t.penalty (fun i => L (t.vertex i)))).sum

private theorem edge_final (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    finalScore (terms G q) L = collisions G L := by
  simp only [finalScore,terms,edgePairs,List.map_map,Function.comp_def,cost_edge,pair_sum,collisions]

theorem collision_bound (G : BipartiteMultigraph) (q : ℕ) [NeZero q] :
    q^2 * collisions G (labels G q) ≤ G.nE^2+2*G.nE*G.maxDeg*q^2 := by
  have hl := labeling_bound (terms G q)
  change q^4 * finalScore (terms G q) (labels G q) ≤ _ at hl
  rw [edge_final] at hl
  have hu := hl.trans (initial_edge_sum G q)
  have hcancel : q^2 * (q^2 * collisions G (labels G q)) ≤
      q^2 * (G.nE^2+2*G.nE*G.maxDeg*q^2) := by
    norm_cast at hu
    nlinarith only [hu]
  exact Nat.le_of_mul_le_mul_left hcancel (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
private def edgeCell (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (e : Fin G.nE) :=
  (L (left G e),L (right G e))

def cellSize (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (c : Fin q × Fin q) : ℕ :=
  ∑ e, if edgeCell G L e = c then 1 else 0

theorem cell_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c = G.nE := by
  unfold cellSize
  rw [sum_comm]; simp

theorem cell_square_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c ^ 2 = collisions G L := by
  have hp (c : Fin q × Fin q) : cellSize G L c ^2 =
      ∑ e, if edgeCell G L e = c then cellSize G L c else 0 := by
    calc
      _ = (∑ e, if edgeCell G L e = c then 1 else 0)*cellSize G L c := by rw [pow_two]; rfl
      _ = _ := by rw [sum_mul]; simp [ite_mul]
  simp_rw [hp]; rw [sum_comm]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold cellSize collisions pairCollision edgeCell
  apply sum_congr rfl; intro e he
  apply sum_congr rfl; intro f hf
  split_ifs <;> simp_all [eq_comm]

theorem cell_cap (G : BipartiteMultigraph) (q : ℕ) [NeZero q] (c : Fin q × Fin q)
    (hm : 2*G.maxDeg*q^4 ≤ G.nE) :
    q^2*cellSize G (labels G q) c ≤ 2*G.nE := by
  let X (g : Fin q × Fin q) : ℤ := cellSize G (labels G q) g
  let M : ℤ := G.nE
  let Q : ℤ := q
  let D : ℤ := G.maxDeg
  have hsum : ∑ g, X g = M := by dsimp only [X,M]; exact_mod_cast cell_sum G (labels G q)
  have henergy : Q^2*(∑ g, X g ^2) ≤ M^2+2*M*D*Q^2 := by
    have h := collision_bound G q
    rw [← cell_square_sum] at h
    dsimp only [Q,X,M,D]; exact_mod_cast h
  have hcard : (Fintype.card (Fin q × Fin q) : ℤ) = Q^2 := by simp [Q,pow_two]
  have hvar : ∑ g, (Q^2*X g-M)^2 = Q^4*∑ g, X g^2-Q^2*M^2 := by
    calc
      _ = ∑ g, (Q^4*X g^2-(2*Q^2*M)*X g+M^2) := by apply sum_congr rfl; intros; ring
      _ = _ := by rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hsum,sum_const,card_univ,nsmul_eq_mul,hcard]; ring
  have hsingle := Finset.single_le_sum (f := fun g => (Q^2*X g-M)^2)
    (fun g _ => sq_nonneg _) (mem_univ c)
  rw [hvar] at hsingle
  have he := mul_le_mul_of_nonneg_left henergy (sq_nonneg Q)
  have hm' : 2*D*Q^4 ≤ M := by dsimp only [D,Q,M]; exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_left hm' (show 0 ≤ M by dsimp [M]; positivity)
  have hx : 0 ≤ Q^2*X c := by dsimp [Q,X]; positivity
  have h : Q^2 * X c ≤ 2*M := by
    by_contra! hf
    nlinarith only [hsingle,he,hh,mul_pos (sub_pos.mpr hf) (show 0 < Q^2*X c by dsimp [M] at hf; omega)]
  dsimp only [Q,X,M] at h
  exact_mod_cast h

private def weighted {n q : ℕ} (w : ℕ) (t : Term n q) : Term n q :=
  { t with penalty := fun z => w*t.penalty z }

private theorem weight_score {n q : ℕ} (w : ℕ) (ts : List (Term n q)) (p : Partial n q) :
    score (ts.map (weighted w)) p = w * score ts p := by
  induction ts with
  | nil => simp [score]
  | cons t ts ih =>
    have ht : termScore (weighted w t) p = w*termScore t p := by
      unfold termScore
      change q^(4-t.arity) * (∑ z : Fin t.arity → Fin q, w*t.penalty (fun h => (p (t.vertex h)).getD (z h))) = _
      rw [← mul_sum,mul_left_comm]
    simp only [score,List.map_cons,List.sum_cons] at ih ⊢
    rw [ht,ih,Nat.mul_add]

private theorem weight_final {n q : ℕ} (w : ℕ) (ts : List (Term n q)) (L : Fin n → Fin q) :
    finalScore (ts.map (weighted w)) L = w * finalScore ts L := by
  induction ts with
  | nil => simp [finalScore]
  | cons t ts ih => simp only [finalScore,List.map_cons,List.sum_cons,weighted] at ih ⊢; rw [ih,Nat.mul_add]

private def digitMatch {q s : ℕ} (d : Fin q → Fin s) (z : Fin 2 → Fin q) : ℕ :=
  if d (z 0) = d (z 1) then 1 else 0

private def legTerm {n q s : ℕ} (d : Fin q → Fin s) (x y : Fin n) : Term n q :=
  if h : x = y then constantTerm _ _ else
    { (pairTerm (q := q) x y h) with penalty := digitMatch d }

private theorem leg_final {n q s : ℕ} (d : Fin q → Fin s) (x y : Fin n) (L : Fin n → Fin q) :
    (legTerm d x y).penalty (fun i => L ((legTerm d x y).vertex i)) =
      if d (L x) = d (L y) then 1 else 0 := by
  by_cases h : x = y
  · have he : legTerm d x y = constantTerm n q := by rw [legTerm,dif_pos h]
    rw [he]; simp [constantTerm,h]
  · have he : legTerm d x y = { (pairTerm (q := q) x y h) with penalty := digitMatch d } := by rw [legTerm,dif_neg h]
    rw [he]; simp [pairTerm,digitMatch]

private theorem leg_initial {n q s : ℕ} (d : Fin q → Fin s)
    (hd : s * (∑ z, digitMatch d z) ≤ q^2) (x y : Fin n) :
    s * termScore (legTerm d x y) (fun _ => none) ≤
       q^4 + (if x = y then s*q^4 else 0) := by
  by_cases h : x = y
  · have he : legTerm d x y = constantTerm n q := by rw [legTerm,dif_pos h]
    rw [he,if_pos h]
    have hs0 : (∑ _ : Fin 0 → Fin q, 1 : ℕ) = 1 := by simp
    change s*(q^(4-0)*(∑ _ : Fin 0 → Fin q, 1 : ℕ)) ≤ _
    rw [hs0]; simp
  · simp only [legTerm,dif_neg h,if_neg h,add_zero]
    change s*(q^2*(∑ z, digitMatch d z)) ≤ q^4
    have hi := Nat.mul_le_mul_left (q^2) hd
    nlinarith only [hi]

private def legTerms {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n) :=
  (List.finRange a).flatMap fun i =>
    ((List.finRange b).flatMap fun x => (List.finRange b).map fun y => (x,y)).map
      fun p => legTerm (d i) (host p.1) (host p.2)

private theorem flat_sum {α γ : Type*} (F : α → List γ) (H : γ → ℕ) (l : List α) :
    ((l.flatMap F).map H).sum = (l.map fun x => ((F x).map H).sum).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem leg_cost_sum {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (H : Term n q → ℕ) :
    ((legTerms d host).map H).sum = ∑ i, ∑ x, ∑ y, H (legTerm (d i) (host x) (host y)) := by
  rw [legTerms,flat_sum,← Fin.sum_univ_def]
  simp only [List.map_map,Function.comp_def,pair_sum]

def terminalCollisions {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (L : Fin n → Fin q) : ℕ :=
  ∑ i, ∑ x, ∑ y, if d i (L (host x)) = d i (L (host y)) then 1 else 0

private theorem terminal_initial {a n q s b : ℕ} (d : Fin a → Fin q → Fin s) (host : Fin b → Fin n)
    (τ : ℕ) (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hd : ∀ i, s * (∑ z, digitMatch (d i) z) ≤ q^2) :
    s * score (legTerms d host) (fun _ => none) ≤ a*(b*(b*q^4+τ*(s*q^4))) := by
  have per (i : Fin a) (x : Fin b) :
      (∑ y, s * termScore (legTerm (d i) (host x) (host y)) (fun _ => none)) ≤
        b*q^4+τ*(s*q^4) := by
    calc
      _ ≤ ∑ y, (q^4 + if host x = host y then s*q^4 else 0) := sum_le_sum fun y _ => leg_initial _ (hd i) _ _
      _ ≤ _ := by
        rw [sum_add_distrib,Finset.sum_ite,Finset.sum_const_zero,add_zero]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (ht x)) _
  unfold score
  rw [leg_cost_sum]
  simp_rw [mul_sum]
  have hh := sum_le_sum (s := univ) (fun i _ => sum_le_sum (s := univ) (fun x _ => per i x))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact_mod_cast hh

/-- Simultaneous edge and terminal collision control, with arbitrary integral objective weights. -/
theorem joint_collision_bound (G : BipartiteMultigraph) (q : ℕ) [NeZero q] {a s b : ℕ}
    (d : Fin a → Fin q → Fin s) (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hd : ∀ i, s * (∑ z, digitMatch (d i) z) ≤ q^2) :
    ∃ L : Fin G.nV → Fin q,
      s*q^2*(w*collisions G L + v*terminalCollisions d host L) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*q^2) + v*a*b*q^2*(b+τ*s) := by
  let E := terms G q
  let T := legTerms d host
  let ts := E.map (weighted w) ++ T.map (weighted v)
  let L := labeling ts
  refine ⟨L,?_⟩
  have he := initial_edge_sum G q
  have ht' := terminal_initial d host τ ht hd
  have hl := labeling_bound ts
  have hfin : finalScore ts L = w*collisions G L + v*terminalCollisions d host L := by
    change finalScore (_++_) L = _
    simp only [finalScore,List.map_append,List.sum_append]
    change finalScore (E.map _) L + finalScore (T.map _) L = _
    rw [weight_final,weight_final,edge_final]
    simp only [T,finalScore,leg_cost_sum,leg_final,terminalCollisions]
  have hinit : score ts (fun _ => none) = w*score E (fun _ => none)+v*score T (fun _ => none) := by
    simp only [ts,score,List.map_append,List.sum_append]
    exact congrArg₂ (·+·) (weight_score w E _) (weight_score v T _)
  change q^4 * finalScore ts L ≤ score ts (fun _ => none) at hl
  rw [hfin,hinit] at hl
  have R := Nat.mul_le_mul_left s hl
  have F := Nat.mul_le_mul_left (s*w) he
  have H := Nat.mul_le_mul_left v ht'
  change s * (q^4 * _) ≤ s*(w*score (terms G q) _ + v*score (legTerms d host) _) at R
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < q^2 from pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _)
  nlinarith only [R,F,H]


private theorem coord_balanced {q s : ℕ} {R : Type*} [Fintype R]
    (e : Fin q ≃ Fin s × R) :
    s * (∑ z, digitMatch (fun t => (e t).1) z) = q^2 := by
  classical
  let P (z : Fin 2 → Fin q) := (e (z 0)).1 = (e (z 1)).1
  let equiv : {z // P z} ≃ Fin s × (R × R) := {
    toFun := fun z => ((e (z.1 0)).1,(e (z.1 0)).2,(e (z.1 1)).2)
    invFun := fun t => ⟨![e.symm (t.1,t.2.1),e.symm (t.1,t.2.2)],by simp [P]⟩
    left_inv := by
      intro z; apply Subtype.ext; funext k
      fin_cases k
      · simp
      · have hh := z.property
        change (e (z.1 0)).1 = (e (z.1 1)).1 at hh
        simp [hh]
    right_inv := by intro t; simp }
  have hcount : (∑ z, digitMatch (fun t => (e t).1) z) = s*Fintype.card R^2 := by
    simpa [digitMatch,P,Fintype.card_subtype,pow_two,mul_assoc] using Fintype.card_congr equiv
  have hq : q = s*Fintype.card R := by simpa using Fintype.card_congr e
  rw [hcount,hq]; ring

/-- Ordered label cells and base-s digit legs can be balanced with one vertex assignment. -/
theorem digit_collision_bound (G : BipartiteMultigraph) (s : ℕ) [NeZero s] (a : ℕ)
    {b : ℕ} (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ) :
    ∃ L : Fin G.nV → Fin (s^a),
      s*(s^a)^2*(w*collisions G L +
          v*terminalCollisions (fun i z => finFunctionFinEquiv.symm z i) host L) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*(s^a)^2) + v*a*b*(s^a)^2*(b+τ*s) := by
  apply joint_collision_bound G _ _ _ _ _ _ ht
  intro i
  let e : Fin (s^a) ≃ Fin s × ({j : Fin a // j ≠ i} → Fin s) :=
    finFunctionFinEquiv.symm.trans (Equiv.funSplitAt i (Fin s))
  exact (coord_balanced e).le

end DetDLP.EdgeLabelPartition
end

section

namespace DetDLP.PacketSlotLayout
open Finset

abbrev SymbolPair (r : ℕ) := Fin r × Fin r
def flip {r : ℕ} (s : SymbolPair r × Bool) : SymbolPair r × Bool :=
  let (x,y) := s.1
  if x < y then (if s.2 then (y,x) else (x,y),false)
  else if y < x then (if s.2 then (x,y) else (y,x),true)
  else ((x,y),s.2)

theorem flip_twice {r : ℕ} (s : SymbolPair r × Bool) : flip (flip s)=s := by
  obtain ⟨⟨x,y⟩,b⟩ := s
  rcases lt_trichotomy x y with h|rfl|h <;> cases b <;>
    simp_all [flip,not_lt_of_gt]

def orient {r : ℕ} (p : SymbolPair r) (b : Bool) : SymbolPair r :=
  if b then (max p.1 p.2,min p.1 p.2) else (min p.1 p.2,max p.1 p.2)

theorem flip_orients {r : ℕ} (s : SymbolPair r × Bool) : orient (flip s).1 (flip s).2 = s.1 := by
  obtain ⟨⟨x,y⟩,b⟩ := s
  rcases lt_trichotomy x y with h|rfl|h <;> cases b <;>
    simp_all [flip,orient,not_lt_of_gt,min_eq_left,min_eq_right,max_eq_left,max_eq_right,le_of_lt]

abbrev Cell (r a : ℕ) := Fin a → SymbolPair r
def unpackBits {a : ℕ} (s : Fin (2^a)) (i : Fin a) : Bool := finTwoEquiv (finFunctionFinEquiv.symm s i)
def packBits {a : ℕ} (s : Fin a → Bool) : Fin (2^a) := finFunctionFinEquiv (fun i => finTwoEquiv.symm (s i))
@[simp] theorem unpack_pack {a : ℕ} (s : Fin a → Bool) (i : Fin a) : unpackBits (packBits s) i=s i := by
  simp [unpackBits,packBits]
@[simp] theorem pack_unpack {a : ℕ} (s : Fin (2^a)) : packBits (unpackBits s)=s := by
  simp [unpackBits,packBits]
theorem bits_eq {a} (s : Fin (2^a)) (i : Fin a) : unpackBits s i=s.val.testBit i.val := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change ((_ : Fin 2) == 1)=_
  change decide ((finFunctionFinEquiv.symm s i:Fin 2)=1)=_
  congr 1; exact propext Fin.ext_iff

def shuffle {r a : ℕ} (z : Cell r a × Fin (2^a)) : Cell r a × Fin (2^a) :=
  let f (i : Fin a) := flip (z.1 i,unpackBits z.2 i)
  (fun i => (f i).1, packBits (fun i => (f i).2))
theorem shuffle_twice {r a : ℕ} (z : Cell r a × Fin (2^a)) : shuffle (shuffle z)=z := by
  obtain ⟨c,s⟩ := z
  have e (i : Fin a) := flip_twice (c i,unpackBits s i)
  apply Prod.ext
  · funext i; simpa [shuffle] using congrArg Prod.fst (e i)
  · apply_fun unpackBits using fun x y h => by rw [← pack_unpack x,← pack_unpack y,h]
    funext i; simpa [shuffle] using congrArg Prod.snd (e i)

theorem slot_label {r a : ℕ} (z : Cell r a × Fin (2^a)) (i : Fin a) :
    orient ((shuffle z).1 i) ((shuffle z).2.val.testBit i.val)=z.1 i := by
  rw [← bits_eq]; simpa [shuffle] using flip_orients (z.1 i,unpackBits z.2 i)

def fiber {M r a : ℕ} (c : Fin M → Cell r a) (p : Cell r a) :=
  univ.filter (fun e => c e=p)
def rankAt {M r a : ℕ} (c : Fin M → Cell r a) (e : Fin M) : Fin (fiber c (c e)).card :=
  ((fiber c (c e)).orderIsoOfFin rfl).symm ⟨e,by simp [fiber]⟩

theorem rank_unique {M r a : ℕ} (c : Fin M → Cell r a) (e f : Fin M)
    (hc : c e=c f) (hr : (rankAt c e).val=(rankAt c f).val) : e=f := by
  let p := c f
  have em : e ∈ fiber c p := by simp [fiber,p,hc]
  have fm : f ∈ fiber c p := by simp [fiber,p]
  let iso := ((fiber c p).orderIsoOfFin rfl).symm
  have h1 : (iso ⟨e,em⟩).val = (rankAt c e).val := by simp [iso,rankAt,Finset.orderIsoOfFin_symm_apply,p,hc]
  have h2 : (iso ⟨f,fm⟩).val = (rankAt c f).val := rfl
  exact congrArg Subtype.val (iso.injective (Fin.ext (h1.trans (hr.trans h2.symm))))

def blocks (M D L : ℕ) := (2*M/D)/L+1

theorem layout {M r a : ℕ} (hr : 0 < r) (c : Fin M → Cell r a)
    (hcap : ∀ z,(r^a)^2*(fiber c z).card ≤ 2*M) (hpad : 2^a*(r^a)^2 ≤ M) :
    let L := 2^a
    let D := (r^a)^2
    let B := blocks M D L
    ∃ pos : Fin M → (Fin B × Cell r a) × Fin L, Function.Injective pos ∧
      (∀ e i,orient ((pos e).1.2 i) ((pos e).2.val.testBit i.val)=c e i) ∧
      Fintype.card (Fin B × Cell r a)*L ≤ 3*M := by
  intro L D B
  have hL : 0 < L := pow_pos (by decide) _
  have hD : 0 < D := pow_pos (pow_pos hr _) _
  have rankbound (e : Fin M) : (rankAt c e).val < B*L := by
    have hi := (rankAt c e).isLt
    have hb : (fiber c (c e)).card ≤ 2*M/D := (Nat.le_div_iff_mul_le hD).mpr (by simpa [D,mul_comm] using hcap (c e))
    exact (hi.trans_le hb).trans_le ((Nat.lt_mul_div_succ (2*M/D) hL).le.trans_eq (Nat.mul_comm ..))
  let chunk (e : Fin M) : Fin B := ⟨(rankAt c e).val/L,(Nat.div_lt_iff_lt_mul hL).mpr (rankbound e)⟩
  let slot (e : Fin M) : Fin L := ⟨(rankAt c e).val%L,Nat.mod_lt _ hL⟩
  let pos (e : Fin M) := ((chunk e,(shuffle (c e,slot e)).1),(shuffle (c e,slot e)).2)
  refine ⟨pos,?_,fun e i => slot_label (c e,slot e) i,?_⟩
  · intro e f h
    have hch := congrArg (fun z => z.1.1.val) h
    have hs := congrArg (fun z => (z.1.2,z.2)) h
    change shuffle (c e,slot e) = shuffle (c f,slot f) at hs
    have eq := congrArg shuffle hs; rw [shuffle_twice,shuffle_twice] at eq
    apply rank_unique c e f (congrArg Prod.fst eq)
    have hmod := congrArg (fun z => z.2.val) eq
    change (rankAt c e).val/L=(rankAt c f).val/L at hch
    change (rankAt c e).val%L=(rankAt c f).val%L at hmod
    rw [← Nat.mod_add_div (rankAt c e).val L,← Nat.mod_add_div (rankAt c f).val L,hch,hmod]
  · have C : Fintype.card (Cell r a) = D := by simp [Cell,SymbolPair,D,pow_two,mul_pow]
    rw [Fintype.card_prod,Fintype.card_fin,C]
    have hq := Nat.div_mul_le_self (2*M/D) L
    have hd := Nat.div_mul_le_self (2*M) D
    have H := (Nat.mul_le_mul_right D hq).trans hd
    change (2*M/D/L+1)*D*L ≤ 3*M
    change L*D ≤ M at hpad
    nlinarith only [H,hpad]

def pick {r a} (right : Bool) (i : Fin a) (z : Cell r a) := if right then (z i).2 else (z i).1

def swapLabels {r a} (x y : Fin r) (z : Cell r a) : Cell r a :=
  fun i => (Equiv.swap x y (z i).1,Equiv.swap x y (z i).2)

theorem pick_swap {r a} (u : Bool) (i : Fin a) (x y : Fin r) (z : Cell r a) :
    pick u i (swapLabels x y z)=Equiv.swap x y (pick u i z) := by cases u <;> rfl

def fiberEq {r a} (u : Bool) (i : Fin a) (x y : Fin r) :
    {z : Cell r a // pick u i z=x} ≃ {z : Cell r a // pick u i z=y} where
  toFun z := ⟨swapLabels x y z.val,by rw [pick_swap,z.property,Equiv.swap_apply_left]⟩
  invFun z := ⟨swapLabels x y z.val,by rw [pick_swap,z.property,Equiv.swap_apply_right]⟩
  left_inv z := by ext j <;> simp [swapLabels]
  right_inv z := by ext j <;> simp [swapLabels]

theorem class_card {r a} (u : Bool) (i : Fin a) (g : Fin r) :
    r*Fintype.card {z : Cell r a // pick u i z=g}=(r^a)^2 := by
  have H := Fintype.card_congr (Equiv.sigmaFiberEquiv (pick u i : Cell r a → Fin r))
  rw [Fintype.card_sigma] at H
  have hh (s : Fin r) := Fintype.card_congr (fiberEq u i s g)
  simp_rw [hh] at H
  simpa [Cell,SymbolPair,pow_two,mul_pow] using H

theorem symbol_cap {M r a} (hr : 0 < r) (c : Fin M → Cell r a)
    (hc : ∀ z,(r^a)^2*(fiber c z).card ≤ 2*M) (u : Bool) (i : Fin a) (g : Fin r) :
    r*Fintype.card {e : Fin M // pick u i (c e)=g} ≤ 2*M := by
  let D := (r^a)^2
  let T := 2*M/D
  have hD : 0 < D := pow_pos (pow_pos hr _) _
  have h (e : Fin M) : (rankAt c e).val < T :=
    (rankAt c e).isLt.trans_le ((Nat.le_div_iff_mul_le hD).mpr (by simpa [D,mul_comm] using hc (c e)))
  let f (e : {e : Fin M // pick u i (c e)=g}) : {z : Cell r a // pick u i z=g} × Fin T :=
    (⟨c e.val,e.property⟩,⟨(rankAt c e.val).val,h e.val⟩)
  have hf : Function.Injective f := by
    intro e d h
    exact Subtype.ext (rank_unique c _ _ (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h))
  have H := Nat.mul_le_mul_left r (Fintype.card_le_of_injective f hf)
  rw [Fintype.card_prod,Fintype.card_fin,← Nat.mul_assoc,class_card] at H
  exact H.trans (by simpa [T,D,mul_comm] using Nat.div_mul_le_self (2*M) D)

def labelCell {r a : ℕ} (s : Fin (r^a) × Fin (r^a)) : Cell r a :=
  fun i => (finFunctionFinEquiv.symm s.1 i,finFunctionFinEquiv.symm s.2 i)

def cellLabel {r a : ℕ} (s : Cell r a) : Fin (r^a) × Fin (r^a) :=
  (finFunctionFinEquiv (fun i => (s i).1),finFunctionFinEquiv (fun i => (s i).2))

@[simp] theorem cell_label {r a : ℕ} (s : Cell r a) : labelCell (cellLabel s)=s := by
  funext i; simp [cellLabel,labelCell]
@[simp] theorem label_cell {r a : ℕ} (s : Fin (r^a) × Fin (r^a)) : cellLabel (labelCell s)=s := by
  simp [labelCell,cellLabel]

def endpoints (G : BipartiteMultigraph) (e : Fin G.nE) : Fin G.nV × Fin G.nV :=
  if G.side (G.endpoints e).1 then (G.endpoints e).swap else G.endpoints e

def edgeLabels (G : BipartiteMultigraph) {r a : ℕ} (L : Fin G.nV → Fin (r^a)) (e : Fin G.nE) : Cell r a :=
  labelCell (L (endpoints G e).1,L (endpoints G e).2)

theorem graph_cap (G : BipartiteMultigraph) {r a : ℕ} (L : Fin G.nV → Fin (r^a))
    (h : ∀ z,(r^a)^2*EdgeLabelPartition.cellSize G L z ≤ 2*G.nE) :
    ∀ z,(r^a)^2*(fiber (edgeLabels G L) z).card ≤ 2*G.nE := by
  intro z
  have eq (e : Fin G.nE) : (edgeLabels G L e=z) ↔
      ((L (endpoints G e).1,L (endpoints G e).2)=cellLabel z) := by
    constructor
    · intro he; simpa only [edgeLabels,label_cell] using congrArg cellLabel he
    · intro he; simpa only [edgeLabels,cell_label] using congrArg labelCell he
  have hh := h (cellLabel z)
  unfold EdgeLabelPartition.cellSize at hh
  rw [Finset.sum_boole] at hh
  convert hh using 2
  congr 1
  ext e
  simp only [fiber,Finset.mem_filter,Finset.mem_univ,true_and,eq]
  change _ ↔ (L (if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1),
    L (if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2))=cellLabel z
  cases hs : G.side (G.endpoints e).1 <;> simp [endpoints,hs]

end DetDLP.PacketSlotLayout
end

section

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
end

section

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
end

section

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
namespace DetDLP.LiveTerminalPorts
open Finset TerminalCoreCut TerminalCoreGeometry
variable {G : BipartiteMultigraph} {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D)
def inCore (v : ↥s.termSubdivVerts) : V G s.lookupVerts :=
  ⟨v.val,fun h => disjoint_left.mp s.disjoint_verts h v.property⟩

theorem surviving_edge (v : ↥s.termSubdivVerts) :
    ∃ e : I G s.lookupVerts,incident G v.val e.val := by
  classical
  have deg := s.subdiv_deg v.val v.property
  let i : Fin (G.deg v.val) := ⟨0,by omega⟩
  let j : Fin (G.deg v.val) := ⟨1,by omega⟩
  let e := (G.ports v.val).get i
  let f := (G.ports v.val).get j
  by_cases he : boundary G s.lookupVerts e
  · by_cases hf : boundary G s.lookupVerts f
    · let E : B G s.lookupVerts := ⟨e,he⟩
      let F : B G s.lookupVerts := ⟨f,hf⟩
      have hE := (host_unique s (inCore s v).property E).mp (atPort G v.val i)
      have hF := (host_unique s (inCore s v).property F).mp (atPort G v.val j)
      have eq : E=F := (host_bijective s).1 (Subtype.ext (hE.trans hF.symm))
      have ij := ports_inj G v.val (congrArg Subtype.val eq)
      exact False.elim (by have val := congrArg Fin.val ij; change 0=1 at val; omega)
    · exact ⟨⟨f,hf⟩,atPort G v.val j⟩
  · exact ⟨⟨e,he⟩,atPort G v.val i⟩

noncomputable def coreHost (e : B G s.lookupVerts) := vertEquiv G s.lookupVerts (inCore s (host s e))
theorem coreHost_inj : Function.Injective (coreHost s) := by
  intro e f h
  apply (host_bijective s).1
  apply Subtype.ext
  exact congrArg (fun v : V G s.lookupVerts => v.val) ((vertEquiv G s.lookupVerts).injective h)
private theorem edge_mem (H : BipartiteMultigraph) (v : Fin H.nV) (e : Fin H.nE)
    (h : incident H v e) : e∈H.ports v := by
  simpa [BipartiteMultigraph.ports,incident] using h
theorem coreHost_live (e : B G s.lookupVerts) : 0<(core G s.lookupVerts).deg (coreHost s e) := by
  let v := host s e
  obtain ⟨edge,inc⟩ := surviving_edge s v
  have H := (core_inc G s.lookupVerts (inCore s v) edge).mpr inc
  apply List.length_pos_of_mem (a:=edgeEquiv G s.lookupVerts edge)
  exact edge_mem _ _ _ H

theorem mass {E : Type} [Fintype E] (H : BipartiteMultigraph) (hosts : E→Fin H.nV)
    (one : Function.Injective hosts) (live : ∀ e,0<H.deg (hosts e)) : Fintype.card E≤2*H.nE := by
  let port (e : E) : Fin H.nE := (H.ports (hosts e)).get ⟨0,live e⟩
  let read (e : E) := (port e,H.side (hosts e))
  have id (e : E) : OrientedOriginalPorts.endpoint H (read e).1 (read e).2=hosts e :=
    OrientedOriginalPorts.incident H (hosts e) ⟨0,live e⟩
  have inj : Function.Injective read := by
    intro e f h; apply one
    exact (id e).symm.trans ((congrArg (fun pair : Fin H.nE×Bool => OrientedOriginalPorts.endpoint H pair.1 pair.2) h).trans (id f))
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective read inj

end DetDLP.LiveTerminalPorts

namespace DetDLP.LiveTerminalPorts
open Finset PacketSlotLayout PacketSelectorForms PacketPortFibers OrientedOriginalPorts
variable {a r : ℕ} {P : Type} [Fintype P] [DecidableEq P]
variable (i : Fin a) (tag : P→SymbolPair r) (real : P→Finset (Slot a))
variable (G : BipartiteMultigraph) (L : Fin G.nE ≃ Slots real) (grp : Fin G.nV→Fin r)
variable (align : Compatible i tag real G L grp)

noncomputable abbrev child (g : Fin r) :=
  ResidualChildGraph.network (owner i tag real G L grp align g) (packetId i tag real g)
noncomputable def retain (g : Fin r) (v : vertex G grp g) : Fin (child i tag real G L grp align g).nV :=
  Fintype.equivFin (vertex G grp g ⊕ P) (.inl v)

theorem retained_degree (v : Fin G.nV) :
    (child i tag real G L grp align (grp v)).deg (retain i tag real G L grp align (grp v) ⟨v,rfl⟩)=G.deg v := by
  classical
  let own := owner i tag real G L grp align (grp v)
  let v' : vertex G grp (grp v) := ⟨v,rfl⟩
  change (ResidualChildGraph.network own _).deg (Fintype.equivFin _ (Sum.inl v'))=_
  rw [ResidualChildGraph.degree]
  simp only [Sum.inl.injEq,Sum.inr_ne_inl,or_false]
  let ports := edgeAt i tag real G L grp align v
  have recover (j : Fin (G.deg v)) :
      physical real G L (ports j).val.val (ports j).val.property.1=(G.ports v).get j := by
    exact L.symm_apply_apply _
  have inj : Function.Injective ports := by
    intro x y eq
    apply TerminalCoreGeometry.ports_inj G v
    exact (recover x).symm.trans ((congrArg (fun s : ResidualChildGraph.fiber own v' => physical real G L s.val.val s.val.property.1) eq).trans (recover y))
  have bottom : G.deg v≤Fintype.card (ResidualChildGraph.fiber own v') := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ports inj
  apply Nat.le_antisymm _ bottom
  let cast : ResidualChildGraph.fiber own v' → {e : ContractionPortCounts.Ports i tag real (grp v) //
    OrientedPacketInstance.endpoint G (ContractionPortCounts.edge i tag real G L e) e.val.2.2=v} :=
      fun e => ⟨e.val,congrArg Subtype.val e.property⟩
  have hcast : Function.Injective cast := by
    intro e k eq; apply Subtype.ext; exact Subtype.mk.inj eq
  have top := Fintype.card_le_of_injective cast hcast
  exact top.trans (ContractionPortCounts.owner_cap i tag real G L (grp v) v)

theorem retained_hosts {B : Type} [Fintype B] (host : B→Fin G.nV) (one : Function.Injective host)
    (alive : ∀ x,0<G.deg (host x)) (g : Fin r) :
    let A := {x : B // grp (host x)=g}
    ∃ f : A→Fin (child i tag real G L grp align g).nV,Function.Injective f ∧
      (∀ x,(child i tag real G L grp align g).deg (f x)=G.deg (host x.val)) ∧
      Fintype.card A≤2*(child i tag real G L grp align g).nE := by
  intro A
  let f (x : A) := retain i tag real G L grp align g ⟨host x.val,x.property⟩
  have inj : Function.Injective f := by
    intro x y eq; apply Subtype.ext; apply one
    have e := (Fintype.equivFin (vertex G grp g ⊕ P)).injective eq
    exact congrArg Subtype.val (Sum.inl.inj e)
  have degree (x : A) : (child i tag real G L grp align g).deg (f x)=G.deg (host x.val) := by
    obtain ⟨x,rfl⟩ := x
    exact retained_degree i tag real G L grp align (host x)
  exact ⟨f,inj,degree,mass _ f inj (fun x => (alive x.val).trans_le (degree x).ge)⟩
end DetDLP.LiveTerminalPorts
end

section
namespace DetDLP.TerminalReattachment
open TerminalCoreCut Finset
variable {G : BipartiteMultigraph} {m k S D : ℕ} (s : LookupSeparatorSpec G m k S D)
abbrev Look := ↥s.lookupVerts
abbrev Ed := B G s.lookupVerts
def owner (e : Ed s) : Look s :=
  if h : (G.endpoints e.val).1∈s.lookupVerts then ⟨_,h⟩ else ⟨_,e.property.resolve_left h⟩

theorem uniqueOwner (v : Look s) (e : Ed s) : incident G v.val e.val ↔ owner s e=v := by
  have dis := Finset.disjoint_left.mp s.disjoint_verts v.property
  by_cases h : (G.endpoints e.val).1∈s.lookupVerts
  · have other := (s.lookup_edges_to_subdiv e.val).1 h
    simp only [owner,dif_pos h,incident,Subtype.ext_iff]
    exact or_iff_left (fun eq => dis (eq ▸ other))
  · simp only [owner,dif_neg h,incident,Subtype.ext_iff]
    exact or_iff_right (fun eq => h (eq ▸ v.property))

def originalEdge (v : Look s) (j : Fin (G.deg v.val)) : Ed s :=
  ⟨(G.ports v.val).get j,by
    rcases atPort G v.val j with h|h
    · exact Or.inl (h.symm ▸ v.property)
    · exact Or.inr (h.symm ▸ v.property)⟩

def localPort (v : Look s) : Fin (G.deg v.val) ≃ ResidualChildGraph.fiber (owner s) v where
  toFun i := ⟨originalEdge s v i,(uniqueOwner s v _).mp (atPort G v.val i)⟩
  invFun e := ⟨(G.ports v.val).idxOf e.val.val,List.idxOf_lt_length_iff.mpr (by
    have inc := (uniqueOwner s v e.val).mpr e.property
    simpa [BipartiteMultigraph.ports,incident] using inc)⟩
  left_inv i := by apply TerminalCoreGeometry.ports_inj G v.val; exact List.idxOf_get _
  right_inv e := by apply Subtype.ext; apply Subtype.ext; exact List.idxOf_get _

variable {n : ℕ} (atLeaf : Ed s→Fin n)
noncomputable abbrev graph := ResidualChildGraph.network (owner s) atLeaf
noncomputable def vertex : Look s ⊕ Fin n ≃ Fin (graph s atLeaf).nV := Fintype.equivFin _
theorem leftDeg (v : Look s) : (graph s atLeaf).deg (vertex s atLeaf (.inl v))=k := by
  have hd := ResidualChildGraph.degree (owner s) atLeaf (.inl v)
  have eq : Fintype.card (ResidualChildGraph.fiber (owner s) v)=G.deg v.val := by
    simpa using (Fintype.card_congr (localPort s v)).symm
  change (ResidualChildGraph.network (owner s) atLeaf).deg (Fintype.equivFin _ (.inl v))=k
  rw [hd]; simpa only [Sum.inl.injEq,Sum.inr_ne_inl,or_false] using eq.trans (s.lookup_deg v.val v.property)

theorem rightDeg (j : Fin n) :
    (graph s atLeaf).deg (vertex s atLeaf (.inr j))=Fintype.card (ResidualChildGraph.fiber atLeaf j) := by
  change (ResidualChildGraph.network (owner s) atLeaf).deg (Fintype.equivFin _ (.inr j))=_
  rw [ResidualChildGraph.degree]; simp only [Sum.inl_ne_inr,Sum.inr.injEq,false_or]

theorem maximum (upper : ℕ) (cap : ∀ j,Fintype.card (ResidualChildGraph.fiber atLeaf j)≤upper) :
    (graph s atLeaf).maxDeg ≤ max k upper := by
  apply Finset.sup_le; intro w _
  obtain ⟨v,rfl⟩ := (vertex s atLeaf).surjective w
  cases v with
  | inl v => rw [leftDeg]; exact le_max_left .. 
  | inr j => rw [rightDeg]; exact (cap j).trans (le_max_right ..)

theorem attach (R : Type) [CommRing R]
    (T : (v : Look s)→(Fin (G.deg v.val)→Bool)→R)
    (F : (j : Fin n)→(ResidualChildGraph.fiber atLeaf j→Bool)→R) :
    ∃ A : (v : Fin (graph s atLeaf).nV)→(Fin ((graph s atLeaf).deg v)→Bool)→R,
    BTNContract (graph s atLeaf) A =
      ∑ x : Ed s→Bool,(∏ v,T v (fun j => x (originalEdge s v j)))*
        ∏ j,F j (fun e => x e.val) := by
  let old (v : Look s) (bits : ResidualChildGraph.fiber (owner s) v→Bool) :=
    T v (fun j => bits (localPort s v j))
  exact ⟨_,ResidualChildGraph.contract (owner s) atLeaf old F⟩
end DetDLP.TerminalReattachment
end

section
namespace DetDLP.StoppedArity
open Finset
theorem path (b : ℕ→ℕ) (d A : ℕ) (steps : ∀ j,j<d → 32*b (j+1)≤b j+512*(A+2)) :
    b d≤b 0/32^d+32*(A+2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have before := ih (fun j hj => steps j (by omega))
    have last := steps d (by omega)
    let t := 32*(A+2)
    have h : b (d+1)*32 ≤ b 0/32^d + t*32 := by dsimp [t]; omega
    have ineq := (Nat.le_div_iff_mul_le (by decide : 0<32)).mpr h
    rw [Nat.add_mul_div_right _ _ (by decide : 0<32),Nat.div_div_eq_div_mul,←pow_succ] at ineq
    exact ineq

theorem exit_bound (b : ℕ→ℕ) (d A m k H M : ℕ) (hm : 0 < m) (initial : b 0=4*m*k)
    (steps : ∀ j,j<d → 32*b (j+1)≤b j+512*(A+2))
    (exits : d=Nat.clog 32 (4*m) ∨ M≤H) (live : b d≤2*M) :
    b d ≤ max (k+32*(A+2)) (2*H) := by
  rcases exits with hd | he
  · have bb := path b d A steps
    rw [initial] at bb
    have bound : 4*m≤32^d := hd ▸ Nat.le_pow_clog (by decide) _
    have pos : 0<4*m := by omega
    have frac := Nat.div_le_div_left bound pos (a:=4*m*k)
    rw [Nat.mul_comm (4*m) k,Nat.mul_div_cancel _ pos] at frac
    rw [Nat.mul_comm (4*m) k] at bb
    exact (bb.trans (Nat.add_le_add_right frac _)).trans (le_max_left ..)
  · exact (live.trans (Nat.mul_le_mul_left _ he)).trans (le_max_right ..)
end DetDLP.StoppedArity
end

section
namespace DetDLP.OriginalContractionLayout
open OrientedPacketInstance ContractionPortCounts Finset

theorem activate {E P : Type} [Fintype E] [DecidableEq P] {a : ℕ} (pos : E→P×Pos a) (inj : Function.Injective pos) :
    ∃ active : P→Finset (Pos a),∃ layout : E≃Address active,∀ e,
      ((layout e).1,(layout e).2.val)=pos e := by
  classical
  let active (q : P) := univ.filter (fun k : Pos a => ∃ e,pos e=(q,k))
  let f (e : E) : Address active := ⟨(pos e).1,(pos e).2,by simp [active]⟩
  have H : Function.Bijective f := by
    constructor
    · intro e e' h
      exact inj (congrArg (fun j : Address active => (j.1,j.2.val)) h)
    · rintro ⟨q,k,hk⟩
      obtain ⟨e,eq⟩ := (mem_filter.mp hk).2
      refine ⟨e,?_⟩
      have mono : Function.Injective (fun x : Address active => (x.1,x.2.val)) := by
        rintro ⟨y,j,hj⟩ ⟨y',j',hj'⟩ eq
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        rfl
      exact mono eq
  exact ⟨active,Equiv.ofBijective f H,fun _ => rfl⟩

theorem of_labels (G : BipartiteMultigraph) {r a : ℕ} [NeZero r]
    (lab : Fin G.nV→Fin (r^a)) (bounds : ∀ z,(r^a)^2*EdgeLabelPartition.cellSize G lab z≤2*G.nE)
    (hpad : 2^a*(r^a)^2≤G.nE) :
    let grp (i : Fin a) (v : Fin G.nV) : Fin r := finFunctionFinEquiv.symm (lab v) i
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active) (tag : Fin N→Fin a→Fin r×Fin r),
      N*2^a≤3*G.nE ∧ (∀ i,Compat i (fun q => tag q i) active G L (grp i)) ∧
      ∀ i d g,r*Fintype.card (sidePorts G (grp i) g d)≤2*G.nE := by
  classical
  intro grp
  let sides := PacketSlotLayout.endpoints G
  let cells := PacketSlotLayout.edgeLabels G (r:=r) (a:=a) lab
  have caps := PacketSlotLayout.graph_cap G (r:=r) (a:=a) lab bounds
  have hr := Nat.pos_of_ne_zero (NeZero.ne r)
  let n := PacketSlotLayout.blocks G.nE ((r^a)^2) (2^a)
  obtain ⟨pos,inj,orient,cap⟩ := PacketSlotLayout.layout hr cells caps hpad
  let P := Fin n×(Fin a→Fin r×Fin r)
  let idx := Fintype.equivFin P
  let tag (j : Fin (Fintype.card P)) := (idx.symm j).2
  let pos' (e : Fin G.nE) := (idx (pos e).1,(pos e).2)
  have h : Function.Injective pos' := by
    intro e e' eq
    exact inj (Prod.ext (idx.injective (congrArg Prod.fst eq)) (congrArg (fun x : Fin (Fintype.card P)×Pos a => x.2) eq))
  obtain ⟨active,L,hL⟩ := activate pos' h
  have endpoint_eq (e : Fin G.nE) (d : Bool) :
      endpoint G e d=if d then (sides e).2 else (sides e).1 := by
    cases d <;> cases h : G.side (G.endpoints e).1 <;> simp [endpoint,sides,PacketSlotLayout.endpoints,h]
  refine ⟨_,active,L,tag,cap,?_,?_⟩
  · intro i e d
    have q : tag (L e).1 i=(pos e).1.2 i := by
      rw [show (L e).1=idx (pos e).1 from congrArg Prod.fst (hL e)]
      simp [tag]
    have k : (L e).2.val=(pos e).2 := congrArg Prod.snd (hL e)
    have O := (orient e i).symm
    change (grp i (sides e).1,grp i (sides e).2)=_ at O
    rw [endpoint_eq,k,group]
    simp only [q]
    cases d
    · exact (congrArg Prod.fst O).symm
    · exact (congrArg Prod.snd O).symm
  · intro i d g
    have eq : (fun e => grp i (endpoint G e d)=g)=(fun e => grp i (if d then (sides e).2 else (sides e).1)=g) := by
      funext e; rw [endpoint_eq]
    change r*Fintype.card {e : Fin G.nE // grp i (endpoint G e d)=g}≤_
    have conv := Equiv.subtypeEquivRight (fun e => iff_of_eq (congrFun eq e))
    calc
      _ = r*Fintype.card {e : Fin G.nE // grp i (if d then (sides e).2 else (sides e).1)=g} :=
        congrArg (r*·) (Fintype.card_congr conv)
      _ ≤ _ := by
        have H := PacketSlotLayout.symbol_cap hr cells caps d i g
        cases d <;> exact H

theorem layout (G : BipartiteMultigraph) (r a : ℕ) [NeZero r]
    (hs : 2*G.maxDeg*(r^a)^4≤G.nE) (hp : 2^a*(r^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin r×Fin r) (grp : Fin a→Fin G.nV→Fin r),
      N*2^a≤3*G.nE ∧
      (∀ i,Compat i (fun q => tag q i) active G L (grp i)) ∧
      ∀ i d g,r*Fintype.card (sidePorts G (grp i) g d)≤2*G.nE := by
  classical
  let lab := EdgeLabelPartition.labels G (r^a)
  obtain ⟨N,active,L,tag,cap,align,small⟩ := of_labels G (r:=r) (a:=a) lab
    (fun z => EdgeLabelPartition.cell_cap G _ z hs) hp
  exact ⟨N,active,L,tag,_,cap,align,small⟩

theorem terminal_layout (G : BipartiteMultigraph) {a b : ℕ} (host : Fin b→Fin G.nV) (τ : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x=host y).card≤τ) (hb : 0<b*τ) (hm : 0<G.nE*G.maxDeg)
    (hs : (a+2)*(64^a)^4*G.maxDeg≤G.nE) (hp : 2^a*(64^a)^2≤G.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin G.nV→Fin 64),
      N*2^a≤3*G.nE ∧
      (∀ i,Compat i (fun q => tag q i) active G L (grp i)) ∧
      (∀ i d g,64*Fintype.card (sidePorts G (grp i) g d)≤2*G.nE) ∧
      ∀ i g,32*(univ.filter fun x => grp i (host x)=g).card≤b+512*(a+2)*τ := by
  classical
  obtain ⟨lab,caps,small⟩ := terminal_packing_cell_bounds G a host τ ht hb hm hs
  obtain ⟨N,active,L,tag,cap,align,sideCap⟩ := of_labels G (r:=64) (a:=a) lab caps hp
  refine ⟨N,active,L,tag,_,cap,align,sideCap,?_⟩
  intro i g; simpa [sum_boole] using small i g
end DetDLP.OriginalContractionLayout
end

section
namespace DetDLP.PartialTerminalTree
open Finset ContractionPortCounts OrientedPacketInstance
structure Node where
  graph : BipartiteMultigraph
  legs : ℕ
  host : Fin legs→Fin graph.nV
  one : Function.Injective host
  live : ∀ x,0<graph.deg (host x)
theorem mass (s : Node) : s.legs ≤ 2*s.graph.nE := by
  simpa using LiveTerminalPorts.mass s.graph s.host s.one s.live
noncomputable def root {G : BipartiteMultigraph} {m k S D : ℕ} (spec : LookupSeparatorSpec G m k S D) : Node :=
  let eq := Fintype.equivFin (TerminalCoreCut.B G spec.lookupVerts)
  ⟨TerminalCoreCut.core G spec.lookupVerts,_,(LiveTerminalPorts.coreHost spec) ∘ eq.symm,
    (LiveTerminalPorts.coreHost_inj spec).comp eq.symm.injective,fun j => LiveTerminalPorts.coreHost_live spec (eq.symm j)⟩

theorem split (s : Node) (a : ℕ) (hm : 0<s.graph.nE*s.graph.maxDeg)
    (hs : (a+2)*(64^a)^4*s.graph.maxDeg ≤ s.graph.nE)
    (hp : 2^a*(64^a)^2 ≤ s.graph.nE) :
    ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin s.graph.nE ≃ Address active)
      (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin s.graph.nV→Fin 64)
      (align : ∀ i,Compat i (fun q => tag q i) active s.graph L (grp i))
      (children : Fin a→Fin 64→Node),
      ∀ i,
        (∀ g,(children i g).graph=LiveTerminalPorts.child i (fun q => tag q i) active s.graph L (grp i) (align i) g) ∧
        (∀ g,32*(children i g).legs ≤ s.legs+512*(a+2)) ∧
        (∑ g,(children i g).graph.nE)=2*s.graph.nE ∧
        (∀ g,16*(children i g).graph.nE ≤ s.graph.nE) ∧
        (∀ g,(children i g).graph.maxDeg  ≤  max s.graph.maxDeg (2*2^a)) ∧
        Nonempty (Fin s.legs ≃ ((g : Fin 64) × Fin (children i g).legs)) := by
  classical
  obtain ⟨N,active,L,tag,grp,_,align,cap,leg⟩ :
      ∃ (N : ℕ) (active : Fin N→Finset (Pos a)) (L : Fin s.graph.nE ≃ Address active)
        (tag : Fin N→Fin a→Fin 64×Fin 64) (grp : Fin a→Fin s.graph.nV→Fin 64),
        N*2^a ≤ 3*s.graph.nE ∧ (∀ i,Compat i (fun q => tag q i) active s.graph L (grp i)) ∧
        (∀ i d g,64*Fintype.card (sidePorts s.graph (grp i) g d) ≤ 2*s.graph.nE) ∧
        ∀ i g,32*(univ.filter fun x => grp i (s.host x)=g).card ≤ s.legs+512*(a+2) := by
    by_cases h : s.legs=0
    · have small : 2*s.graph.maxDeg*(64^a)^4 ≤ s.graph.nE := by
        calc
          _=2*((64^a)^4*s.graph.maxDeg) := by ring
          _ ≤ (a+2)*((64^a)^4*s.graph.maxDeg) := Nat.mul_le_mul_right _ (by omega)
          _ ≤ _ := by simpa [mul_assoc] using hs
      obtain ⟨N,A,L,t,g,x,y,z⟩ := OriginalContractionLayout.layout s.graph 64 a small hp
      refine ⟨N,A,L,t,g,x,y,z,fun i v => ?_⟩
      have em : IsEmpty (Fin s.legs) := ⟨fun x => by have := x.isLt; omega⟩
      letI := em
      simp
    · have occ (x : Fin s.legs) : (univ.filter fun y => s.host x = s.host y).card ≤ 1 := by
        apply card_le_one.mpr; intro y hy z hz
        exact s.one (((mem_filter.mp hy).2).symm.trans (mem_filter.mp hz).2)
      simpa only [Nat.mul_one] using OriginalContractionLayout.terminal_layout s.graph s.host 1 occ (by omega) hm hs hp
  let ports (i : Fin a) (g : Fin 64) := {x : Fin s.legs // grp i (s.host x)=g}
  let eq (i : Fin a) (g : Fin 64) := Fintype.equivFin (ports i g)
  let H (i : Fin a) (g : Fin 64) := LiveTerminalPorts.child i (fun q => tag q i) active s.graph L (grp i) (align i) g
  have live (i : Fin a) (g : Fin 64) := LiveTerminalPorts.retained_hosts i (fun q => tag q i) active s.graph L (grp i)
    (align i) s.host s.one s.live g
  choose f inj deg _ using live
  let nodes (i : Fin a) (g : Fin 64) : Node := ⟨H i g,Fintype.card (ports i g),f i g ∘ (eq i g).symm,
    (inj i g).comp (eq i g).symm.injective,fun x => (s.live _).trans_le (deg i g ((eq i g).symm x)).ge⟩
  refine ⟨N,active,L,tag,grp,align,nodes,?_⟩; intro i
  refine ⟨fun _ => rfl,?_,?_,?_,?_,?_⟩
  · intro g; change 32*Fintype.card (ports i g) ≤ _; rw [Fintype.card_subtype]; exact leg i g
  · exact ContractionPortCounts.mass i (fun q => tag q i) active s.graph L
  · intro g
    have x := group_cap i (fun q => tag q i) active s.graph L (grp i) (align i) g
    have y := cap i false g
    have z := cap i true g
    change 16*Fintype.card (Ports i (fun q => tag q i) active g) ≤ _
    omega
  · intro g; apply Finset.sup_le; intro w _
    let V := OrientedOriginalPorts.vertex s.graph (grp i) g
    obtain ⟨l,rfl⟩ := (Fintype.equivFin (V ⊕ Fin N)).surjective w
    cases l with
    | inl v =>
      obtain ⟨v,hg⟩ := v; subst g
      exact (LiveTerminalPorts.retained_degree i (fun q => tag q i) active s.graph L (grp i) (align i) v).le.trans
        ((le_sup (f:=s.graph.deg) (mem_univ v)).trans (le_max_left ..))
    | inr q =>
      change (ResidualChildGraph.network _ _).deg (Fintype.equivFin _ (.inr q)) ≤ _
      rw [ResidualChildGraph.degree]
      simp only [Sum.inl_ne_inr,Sum.inr.injEq,false_or]
      exact (packet_cap i (fun q => tag q i) active g q).trans (le_max_right ..)
  · exact ⟨(Equiv.sigmaFiberEquiv (fun x : Fin s.legs => grp i (s.host x))).symm.trans
      (Equiv.sigmaCongrRight (fun g => eq i g))⟩
end DetDLP.PartialTerminalTree
end

section
namespace DetDLP.TerminalCoreScale
open TerminalCoreCut ScalarPacketParameters
theorem ceil_power (x n j : ℕ) (r : ℝ) (hr : 0 ≤ r) (hx : x ≤ 2^n) (h : (n:ℝ)*r ≤ j) :
    Nat.ceil ((x:ℝ)^r) ≤ 2^j := by
  apply Nat.ceil_le.mpr
  have xx : (x:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hx
  calc
    _ ≤ ((2:ℝ)^n)^r := Real.rpow_le_rpow (Nat.cast_nonneg _) xx hr
    _ = (2:ℝ)^((n:ℝ)*r) := (Real.rpow_natCast_mul (by norm_num) _ _).symm
    _ ≤ (2:ℝ)^(j:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = _ := by norm_cast
theorem mass {G : BipartiteMultigraph} {m k S D C b : ℕ} (spec : LookupSeparatorSpec G m k S D)
    (hb : b ≤ C*(4*m*k)) : b ≤ 2*C*S := by
  let s := PartialTerminalTree.root spec
  have bound := PartialTerminalTree.mass s
  change Fintype.card (TerminalCoreCut.B G spec.lookupVerts) ≤ 2*(core G spec.lookupVerts).nE at bound
  rw [TerminalCoreGeometry.boundary_card spec] at bound
  have H := Nat.mul_le_mul_left C (bound.trans (Nat.mul_le_mul_left _ (TerminalCoreGeometry.core_edges spec)))
  exact (hb.trans H).trans_eq (by ring)

theorem scale_bounds {G : BipartiteMultigraph} {m k S C b : ℕ}
    (spec : LookupSeparatorSpec G m k S (C*Nat.ceil ((b:ℝ)^((3:ℝ)/4))))
    (hb : b ≤ C*(4*m*k)) (big : 32*(32+2*C) ≤ Nat.clog 2 S) :
    let root := core G spec.lookupVerts
    let lam := Nat.clog 2 S
    let ρ := scale root S
    lam/32 ≤ ρ ∧ ρ ≤ lam ∧ degree root S ≤ 2^(30*(lam/32)) := by
  intro root lam ρ
  let u := lam/32
  have hu : 32+2*C ≤ u := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have smallC : 2*C ≤ 2^u := (by omega : 2*C ≤ u).trans ((Nat.lt_two_pow_self : u<2^u).le)
  have upper : S ≤ 2^(33*u) := (Nat.le_pow_clog (by decide : 1<2) S).trans (Nat.pow_le_pow_right (by decide) (by dsimp [lam,u] at *; omega))
  have bi : b ≤ 2^(34*u) := calc
    _ ≤ (2*C)*S := mass spec hb
    _ ≤ 2^u*2^(33*u) := Nat.mul_le_mul smallC upper
    _ = _ := by rw [←pow_add]; congr 1; omega
  have bc := ceil_power b (34*u) (26*u) (3/4) (by norm_num) bi (by push_cast; linarith)
  have sc := ceil_power S (33*u) (30*u) (9/10) (by norm_num) upper (by push_cast; linarith)
  have deg : degree root S ≤ 2^(30*u) := by
    apply max_le _ sc
    calc
      root.maxDeg ≤ C*Nat.ceil ((b:ℝ)^((3:ℝ)/4)) := TerminalCoreGeometry.max_degree spec
      _ ≤ 2^u*2^(26*u) := Nat.mul_le_mul (by omega) bc
      _ ≤ _ := by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have nontrivClog : ∀ z : ℕ,z ≤ 1 → Nat.clog 2 z=0 := by intro z hz; interval_cases z <;> decide
  have hs : 1 < S := by by_contra! h; rw [nontrivClog S h] at big; omega
  have floorS := Nat.pow_pred_clog_lt_self (b:=2) (x:=S) (by decide) hs
  have sep : 2^u*degree root S ≤ S := calc
    _ ≤ 2^u*2^(30*u) := Nat.mul_le_mul_left _ deg
    _ ≤ 2^(lam-1) := by rw [←pow_add]; apply Nat.pow_le_pow_right (by decide); dsimp only [u]; omega
    _ ≤ S := floorS.le
  have Dpos : 0<degree root S := by
    have bpos : 0<(S:ℝ) := by exact_mod_cast (by omega : 0<S)
    have q := (Real.rpow_pos_of_pos bpos ((9:ℝ)/10)).trans_le (Nat.le_ceil _)
    exact (by exact_mod_cast q : 0 < Nat.ceil ((S:ℝ)^((9:ℝ)/10))).trans_le (le_max_right ..)
  have DP : (0:ℝ)<(degree root S:ℝ) := by exact_mod_cast Dpos
  have SP : (0:ℝ)<S := by exact_mod_cast (by omega : 0<S)
  have rate : u ≤ ρ := by
    apply le_trans _ (le_max_right ..)
    apply Nat.le_floor
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (div_pos SP DP)).mpr
    rw [Real.rpow_natCast]; apply (le_div_iff₀ DP).mpr; exact_mod_cast sep
  have upρ : ρ ≤ lam := by
    have nontriv : 2 ≤ ρ := by omega
    have bound := (ScalarPacketParameters.sep root S (by omega) nontriv).2
    have comp : 2^ρ ≤ 2^lam := ((Nat.le_mul_of_pos_right _ Dpos).trans bound).trans (Nat.le_pow_clog (by decide) S)
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp comp
  exact ⟨rate,upρ,deg⟩
end DetDLP.TerminalCoreScale
end

section
namespace DetDLP.ClearResidualWeights
open Finset
theorem clear {H B : Type} [CommRing H] [CommRing B] (I : Subring H) (φ : I→+*B) (g p N : ℕ)
    (zero : (2:B)^(p+g)=0) (w : Fin N→H) (v : Fin N→I) (y : I)
    (hw : ∀ j,(2:H)^g*w j∈I) (eq : ∃ err : I,(∑ j,w j*(v j:H))-(y:H)=(2:H)^p*(err:H)) :
    (∑ j,φ ⟨(2:H)^g*w j,hw j⟩*φ (v j))=(2:B)^g*φ y := by
  classical
  obtain ⟨err,eq⟩ := eq
  let u (j : Fin N) : I := ⟨(2:H)^g*w j,hw j⟩
  have full : (∑ j,u j*v j)-(2:I)^g*y=(2:I)^(p+g)*err := by
    apply Subtype.ext
    change I.subtype ((∑ j,u j*v j)-(2:I)^g*y)=I.subtype ((2:I)^(p+g)*err)
    simp only [map_sub,map_sum,map_mul,map_pow,map_ofNat,Subring.subtype_apply]
    calc
      _ = (2:H)^g*((∑ j,w j*(v j:H))-(y:H)) := by
        rw [mul_sub,Finset.mul_sum]
        congr 1
        apply sum_congr rfl; intro j _; change (2:H)^g*w j*(v j:H)=_; ring
      _ = _ := by rw [eq,pow_add]; ring
  have lift := congrArg φ full
  simpa only [map_sub,map_sum,map_mul,map_pow,map_ofNat,zero,zero_mul,sub_eq_zero,u] using lift
theorem zero {q : ℕ} (B : Type) [CommRing B] [Algebra (ZMod (2^q)) B] : (2:B)^q=0 := by
  have h : (2:ZMod (2^q))^q=0 := by
    rw [←Nat.cast_ofNat (R:=ZMod (2^q)) (n:=2),←Nat.cast_pow]; exact ZMod.natCast_self ..
  simpa only [map_pow,map_zero,map_ofNat] using congrArg (algebraMap (ZMod (2^q)) B) h
end DetDLP.ClearResidualWeights
end

section
namespace DetDLP.TerminalBlockEstimate
abbrev lam := Nat.clog 2
theorem blocks (S b C m : ℕ) (hs : 2 ≤ S) (mass : b ≤ 2*C*S) (hc : 2*C+2 ≤ lam S)
    (blocks : m ≤ C*blockCount b) :
    (m:ℝ) ≤ 4*(C:ℝ)*(lam S:ℝ)^(1/4:ℝ) := by
  let L := lam S
  have scale : b+2 ≤ 2^(2*L) := calc
    _ ≤ (2*C+2)*S := by rw [Nat.add_mul]; omega
    _ ≤ (2^L)*(2^L) := Nat.mul_le_mul (hc.trans (Nat.lt_two_pow_self : L<2^L).le) (Nat.le_pow_clog (by decide) S)
    _ = _ := by rw [←pow_add,two_mul]
  have logN := Nat.clog_le_of_le_pow scale
  let t := (L:ℝ)^(1/4:ℝ)
  have one : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) (by norm_num)
  have cap : ((Nat.clog 2 (b+2):ℕ):ℝ)^(1/4:ℝ) ≤ 2*t := calc
    _ ≤ ((2:ℝ)*L)^(1/4:ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast logN) (by norm_num)
    _ = (2:ℝ)^(1/4:ℝ)*t := Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by dsimp [t]; positivity)
  have rounding := Nat.ceil_lt_add_one (show 0 ≤ ((Nat.clog 2 (b+2):ℕ):ℝ)^(1/4:ℝ) by positivity)
  have ma : (blockCount b:ℝ) ≤ 4*t := by unfold blockCount; rw [Nat.cast_max]; apply max_le <;> push_cast <;> linarith
  calc
    _ ≤ (C:ℝ)*(blockCount b:ℝ) := by exact_mod_cast blocks
    _ ≤ (C:ℝ)*(4*t) := mul_le_mul_of_nonneg_left ma (Nat.cast_nonneg _)
    _ = _ := by ring
end DetDLP.TerminalBlockEstimate
end

section
namespace DetDLP.ResidualDegreeRate
theorem cubic (L : ℕ) (big : 16 ≤ L) : L^3 ≤ 2^(L-1) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le big
  clear big
  induction u with
  | zero => decide
  | succ u ih =>
    rw [show 16+(u+1)-1=(16+u-1)+1 by omega,pow_succ]
    apply le_trans _ (Nat.mul_le_mul_right 2 ih)
    nlinarith [Nat.zero_le (u^3),Nat.zero_le (u^2)]
theorem blocks_square (L m C : ℕ) (blocks : (m:ℝ) ≤ 4*(C:ℝ)*(L:ℝ)^(1/4:ℝ)) :
    m*m ≤ 96*C^2*((L/32).sqrt+1) := by
  let d := (L/32).sqrt+1
  have localBound := Nat.lt_succ_sqrt' (L/32)
  change L/32 < d^2 at localBound
  have LL : L ≤ 36*d^2 := by omega
  have R : (L:ℝ) ≤ (6*(d:ℝ))^2 := by
    have eq : 36*d^2=(6*d)^2 := by ring
    rw [eq] at LL; exact_mod_cast LL
  have root := Real.sqrt_le_sqrt R
  rw [Real.sqrt_sq (by positivity)] at root
  have square := mul_self_le_mul_self (Nat.cast_nonneg m) blocks
  have id : ((L:ℝ)^(1/4:ℝ))*((L:ℝ)^(1/4:ℝ))=Real.sqrt L := by
    rw [←Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.sqrt_eq_rpow]; norm_num
  have s : (m:ℝ)*m ≤ 16*(C:ℝ)^2*(Real.sqrt L) := by
    calc
      _ ≤ _ := square
      _ = _ := by rw [←id]; ring
  have h := mul_le_mul_of_nonneg_left root (show 0 ≤ 16*(C:ℝ)^2 by positivity)
  have rr : (m:ℝ)*m ≤ 96*(C:ℝ)^2*d := by linarith only [s,h]
  exact_mod_cast rr
theorem full (S b C m k : ℕ) (hs : 2 ≤ S) (big : 16+2*C ≤ Nat.clog 2 S)
    (mass : b ≤ 2*C*S) (blocks : m ≤ C*blockCount b) (sum : S ≤ C*m*b) (edges : 4*m*k ≤ C*b) :
    let L := Nat.clog 2 S
    let U := max (k+32*(L+2)) (2*(S/((L/32).sqrt+1)))
    U*m ≤ (1217*(C+1)^3)*b := by
  intro L U
  let d := (L/32).sqrt+1
  have hL : 16 ≤ L := by dsimp only [L]; omega
  have dpos : 0 < d := Nat.succ_pos _
  have mb := TerminalBlockEstimate.blocks S b C m hs mass (by change 2*C+2 ≤ L; omega) blocks
  change (m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ) at mb
  have ms : m*m ≤ 96*C^2*d := blocks_square L m C mb
  have mL : m ≤ 4*C*L := by
    have gain : (L:ℝ)^(1/4:ℝ) ≤ L := Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ L)) (by norm_num)
    exact_mod_cast mb.trans (mul_le_mul_of_nonneg_left gain (by positivity))
  have poly : L^3 ≤ S := (cubic L hL).trans (Nat.pow_pred_clog_lt_self (by decide) hs).le
  have room : L^2 ≤ 4*C^2*b := by
    apply Nat.le_of_mul_le_mul_left (c:=L) _ (by omega)
    calc
      L*L^2 = L^3 := by ring
      _ ≤ C*m*b := poly.trans sum
      _ ≤ C*(4*C*L)*b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ mL)
      _ = _ := by ring
  have look : (k+32*(L+2))*m ≤ (1217*(C+1)^3)*b := by
    have x : 32*(L+2)*m ≤ 256*C*L^2 := calc
      _ ≤ 32*(2*L)*(4*C*L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) mL
      _ = _ := by ring
    have top := x.trans (Nat.mul_le_mul_left (256*C) room)
    have kk : k*m ≤ C*b := by nlinarith only [edges,Nat.zero_le (k*m)]
    rw [Nat.add_mul]
    nlinarith only [top,kk,Nat.zero_le (C^3*b),Nat.zero_le (C^2*b),Nat.zero_le (C*b)]
  have stop : 2*(S/d)*m ≤ (1217*(C+1)^3)*b := by
    have x : (2*(S/d)*m)*d ≤ 2*S*m := calc
      _ = 2*((S/d)*d)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..))
    have y : 2*S*m ≤ 192*C^3*b*d := calc
      _ ≤ 2*(C*m*b)*m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ sum)
      _ = (2*C*b)*(m*m) := by ring
      _ ≤ (2*C*b)*(96*C^2*d) := Nat.mul_le_mul_left _ ms
      _ = _ := by ring
    have t : 2*(S/d)*m ≤ 192*C^3*b := Nat.le_of_mul_le_mul_right (x.trans y) dpos
    nlinarith only [t,Nat.zero_le (C^3*b),Nat.zero_le (C^2*b),Nat.zero_le (C*b)]
  change max _ _ * m ≤ _
  rcases le_total (k+32*(L+2)) (2*(S/d)) with h|h
  · rw [max_eq_right h]; exact stop
  · rw [max_eq_left h]; exact look
end DetDLP.ResidualDegreeRate
end

section
namespace DetDLP.ResidualScalarScale
open ScalarPacketParameters
theorem quartic (L : ℕ) (h : 32 ≤ L) : L^4 ≤ 2^(L-1) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction u with
  | zero => decide
  | succ u ih =>
    rw [show 32+(u+1)-1=(32+u-1)+1 by omega,pow_succ]
    apply le_trans _ (Nat.mul_le_mul_right 2 ih)
    nlinarith only [Nat.zero_le (u^4),Nat.zero_le (u^3),Nat.zero_le (u^2),Nat.zero_le u]
theorem ceiling (S b C m : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ S) (big : 32+2*C ≤ Nat.clog 2 S)
    (mass : b ≤ 2*C*S) (blocks : m ≤ C*blockCount b) (sum : S ≤ C*m*b) :
    Nat.ceil ((b:ℝ)^((9:ℝ)/10))*m ≤ 32*(C+1)^3*b := by
  let L := Nat.clog 2 S
  have hL : 32 ≤ L := by dsimp only [L]; omega
  have mb := TerminalBlockEstimate.blocks S b C m hs mass (by change 2*C+2 ≤ L; omega) blocks
  change (m:ℝ) ≤ 4*C*(L:ℝ)^(1/4:ℝ) at mb
  have mL : m ≤ 4*C*L := by
    have gain : (L:ℝ)^(1/4:ℝ) ≤ L := Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1 ≤ L)) (by norm_num)
    exact_mod_cast mb.trans (mul_le_mul_of_nonneg_left gain (by positivity))
  have poly : L^4 ≤ S := (quartic L hL).trans (Nat.pow_pred_clog_lt_self (by decide) hs).le
  have room : L^3 ≤ (4*(C+1)^2)*b := by
    apply Nat.le_of_mul_le_mul_left (c:=L) _ (by omega)
    calc
      L*L^3 = L^4 := by ring
      _ ≤ C*m*b := poly.trans sum
      _ ≤ C*(4*C*L)*b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ mL)
      _ ≤ _ := by nlinarith only [Nat.zero_le (L*b),Nat.zero_le (C*L*b)]
  let H := 4*((C:ℝ)+1)^2
  have hH : 1 ≤ H := by dsimp only [H]; nlinarith [(Nat.cast_nonneg C : (0:ℝ) ≤ C),sq_nonneg (C:ℝ)]
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  have root : (L:ℝ)^(1/4:ℝ) ≤ H*(b:ℝ)^(1/10:ℝ) := calc
    _ = ((L:ℝ)^3)^(1/12:ℝ) := by rw [←Real.rpow_natCast_mul (Nat.cast_nonneg _)]; norm_num
    _ ≤ (H*b)^(1/12:ℝ) := Real.rpow_le_rpow (by positivity) (by dsimp only [H]; exact_mod_cast room) (by norm_num)
    _ = H^(1/12:ℝ)*(b:ℝ)^(1/12:ℝ) := Real.mul_rpow (by linarith) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul (Real.rpow_le_self_of_one_le hH (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hb' (by norm_num)) (by positivity) (by linarith)
  have cap := Nat.ceil_lt_add_one (show 0 ≤ (b:ℝ)^((9:ℝ)/10) by positivity)
  have one := Real.one_le_rpow hb' (show (0:ℝ) ≤ 9/10 by norm_num)
  have bh : (Nat.ceil ((b:ℝ)^((9:ℝ)/10)):ℝ) ≤ 2*(b:ℝ)^(9/10:ℝ) := by linarith only [cap,one]
  have mh := mb.trans (mul_le_mul_of_nonneg_left root (by positivity))
  have eq : (b:ℝ)^(9/10:ℝ)*(b:ℝ)^(1/10:ℝ)=b := by rw [←Real.rpow_add' (Nat.cast_nonneg _) (by norm_num)]; norm_num
  have finish : (Nat.ceil ((b:ℝ)^((9:ℝ)/10)):ℝ)*m ≤ 32*((C:ℝ)+1)^3*b := calc
    _ ≤ (2*(b:ℝ)^(9/10:ℝ))*(4*C*(H*(b:ℝ)^(1/10:ℝ))) := mul_le_mul bh mh (Nat.cast_nonneg _) (by positivity)
    _ = 8*C*H*b := by calc
        _ = 8*C*H*((b:ℝ)^(9/10:ℝ)*(b:ℝ)^(1/10:ℝ)) := by ring
        _ = _ := by rw [eq]
    _ ≤ _ := by dsimp only [H]; nlinarith only [mul_nonneg (sq_nonneg ((C:ℝ)+1)) (Nat.cast_nonneg b)]
  exact_mod_cast finish

theorem logarithm (G : BipartiteMultigraph) (b m A : ℕ) (hb : 0 < b) (hm : 0 < m)
    (h : degree G b*m ≤ A*b) : logSafe m ≤ ((A:ℝ)+2)*(scale G b:ℝ) := by
  let D := degree G b
  let R := scale G b
  have hr : 1 ≤ R := le_max_left ..
  have hp : (0:ℝ) < b := by exact_mod_cast hb
  have hd : 0 < D := by
    have p := (Real.rpow_pos_of_pos hp ((9:ℝ)/10)).trans_le (Nat.le_ceil _)
    exact (by exact_mod_cast p : 0 < Nat.ceil ((b:ℝ)^((9:ℝ)/10))).trans_le (le_max_right ..)
  have dp : (0:ℝ) < D := by exact_mod_cast hd
  have rat : (b:ℝ)/D < (2:ℝ)^((R:ℝ)+1) := by
    apply (Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos hp dp)).mp
    calc
      _ < ((Nat.floor (Real.logb 2 ((b:ℝ)/D)):ℕ):ℝ)+1 := Nat.lt_floor_add_one _
      _ ≤ _ := by gcongr; exact_mod_cast (le_max_right 1 _ : Nat.floor (Real.logb 2 ((b:ℝ)/D)) ≤ R)
  have ar : (A:ℝ) ≤ (2:ℝ)^A := by exact_mod_cast (Nat.lt_two_pow_self : A<2^A).le
  have ms : (m:ℝ) ≤ (A:ℝ)*((b:ℝ)/D) := by
    rw [←mul_div_assoc,le_div_iff₀ dp,mul_comm (m:ℝ)]
    exact_mod_cast h
  have rate : (m:ℝ) ≤ (2:ℝ)^(((A:ℝ)+2)*R) := calc
    _ ≤ (2:ℝ)^A*((2:ℝ)^((R:ℝ)+1)) := ms.trans (mul_le_mul ar rat.le (by positivity) (by positivity))
    _ = (2:ℝ)^((A:ℝ)+(R:ℝ)+1) := by rw [add_assoc,Real.rpow_add (x:=2) (y:=(A:ℝ)) (by norm_num),Real.rpow_natCast]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have rr : (1:ℝ) ≤ R := by exact_mod_cast hr
      nlinarith [mul_nonneg (Nat.cast_nonneg A) (sub_nonneg.mpr rr)]
  have room : (1:ℝ) ≤ ((A:ℝ)+2)*R := by
    have rr : (1:ℝ) ≤ R := by exact_mod_cast hr
    nlinarith [mul_nonneg (Nat.cast_nonneg A : (0:ℝ) ≤ A) (Nat.cast_nonneg R)]
  apply max_le room
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (lt_max_of_lt_left (by norm_num : (0:ℝ)<2))).mpr
  exact max_le (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) room) rate
end DetDLP.ResidualScalarScale
end

section
namespace DetDLP.FiniteResidualContraction
open Finset Polynomial
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem full (C : ℕ) :
    ∃ (L₀ : ℕ) (K₁ K₂ : ℝ),0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ {G : BipartiteMultigraph} {b m k S p ell : ℕ}
      (spec : LookupSeparatorSpec G m k S (C*Nat.ceil ((b:ℝ)^((3:ℝ)/4)))),
    let L := Nat.clog 2 S
    let D := Nat.clog 32 (4*m)
    let κ := 4*L
    let g := 64*(S+1)*(L+1)*2^L*64^D
    let J := 1217*(C+1)^3
    L₀ ≤ L → 0 < b → 0 < m → b ≤ C*(4*m*k) → 4*m*k ≤ C*b → S ≤ C*m*b → m ≤ C*blockCount b → 0 < p → p ≤ S →
    ∃ c : Fin κ→ZMod 2,let f := (X:ℤ[X])^κ+∑ j,monomial j.val ((c j).val:ℤ)
    f.Monic ∧ f.natDegree=κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2))) ∧
    let B₀ := AdjoinRoot (f.map (Int.castRingHom (ZMod (2^(p+g)))))
    let B := AdjoinRoot ((X:B₀[X])^ell)
    ∀ T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→B,
      ∃ (N : ℕ) (w : Fin N→B) (R : Fin N→BipartiteMultigraph)
        (A : (j : Fin N)→(v : Fin (R j).nV)→(Fin ((R j).deg v)→Bool)→B),
        (N:ℝ) ≤ Real.exp (K₁*((b:ℝ)/(L:ℝ)^(7/40:ℝ))+K₂*(L:ℝ)^(13/10:ℝ)) ∧
        (∀ j,(R j).nE=4*m*k ∧ (R j).nV ≤ 4*m+64^D ∧
          let Δ := max (R j).maxDeg (Nat.ceil ((b:ℝ)^((9:ℝ)/10)))
          let ρ := max 1 (Nat.floor (Real.logb 2 ((b:ℝ)/(Δ:ℝ))))
          Δ*m ≤ J*b ∧ logSafe m ≤ ((J:ℝ)+2)*ρ) ∧
        (∑ j,w j*BTNContract (R j) (A j))=(2:B)^g*BTNContract G T := by
  classical
  obtain ⟨lo,K₁,K₂,ka,kb,expand⟩ := PrescribedResidualSpecialization.full C
  refine ⟨max lo (32+2*C),K₁,K₂,ka,kb,?_⟩
  intro G b m k S p ell spec L D κ g J big hb hm comp edges size blocks hp hps
  have big₁ := (le_max_left ..).trans big
  have big₂ : 32+2*C ≤ L := (le_max_right ..).trans big
  obtain ⟨c,hc⟩ := expand spec big₁ hm comp size blocks hp hps
  refine ⟨c,?_⟩
  intro f; obtain ⟨mon,deg,irr,_,ev⟩ := hc
  refine ⟨mon,deg,irr,?_⟩; intro B₀ B T
  let I := IntegralJetTower.lattice f ell
  let red : I→+*B := IntegralJetTower.red f ell mon (p+g)
  let lift : B→I := IntegralJetWords.lift f ell mon (p+g)
  have sec (x : B) : red (lift x)=x :=
    (IntegralJetWords.read_lift f ell mon x).trans (IntegralJetWords.decode_word f ell mon (p+g) (by omega) x)
  let T' (v : Fin G.nV) (z : Fin (G.deg v)→Bool) := lift (T v z)
  obtain ⟨N,w,R,A,count,props,eq⟩ := ev T'
  let w' (j : Fin N) : I := ⟨_,(props j).2.2.2⟩
  let A' (j : Fin N) (v : Fin (R j).nV) (z : Fin ((R j).deg v)→Bool) := red (A j v z)
  refine ⟨N,fun j => red (w' j),R,A',count,?_,?_⟩
  · have hs : 2 ≤ S := by
      by_contra! small
      have tiny : ∀ n : ℕ,n < 2 → Nat.clog 2 n=0 := by intro n hn; interval_cases n <;> decide
      have z := tiny S small
      change 32+2*C ≤ Nat.clog 2 S at big₂; omega
    have mass := TerminalCoreScale.mass spec comp
    have high := ResidualDegreeRate.full S b C m k hs (by change 16+2*C ≤ L; omega) mass blocks size edges
    have ceiling := ResidualScalarScale.ceiling S b C m hb hs big₂ mass blocks size
    intro j
    obtain ⟨hE,hV,hD,_⟩ := props j
    have mx := (Nat.mul_le_mul_right m hD).trans high
    let D' := ScalarPacketParameters.degree (R j) b
    have good : D'*m ≤ J*b := by
      have ce : Nat.ceil ((b:ℝ)^((9:ℝ)/10))*m ≤ J*b :=
        ceiling.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 32 ≤ 1217)))
      change (max _ _)*m ≤ _
      rcases le_total (R j).maxDeg (Nat.ceil ((b:ℝ)^((9:ℝ)/10))) with hl|hr
      · rw [max_eq_right hl]; exact ce
      · rw [max_eq_left hr]; exact mx
    exact ⟨hE,hV,good,ResidualScalarScale.logarithm (R j) b m J hb hm good⟩
  · have all := ClearResidualWeights.clear I red g p N (ClearResidualWeights.zero B) w
      (fun j => BTNContract (R j) (A j)) (BTNContract G T') (fun j => (props j).2.2.2) eq
    have val (j) : red (BTNContract (R j) (A j))=BTNContract (R j) (A' j) := by simp [BTNContract,A']
    have orig : red (BTNContract G T')=BTNContract G T := by simp [BTNContract,T',sec]
    simpa only [w',val,orig] using all
end DetDLP.FiniteResidualContraction
end

open DetDLP Finset Polynomial
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem solution (C : ℕ) :
    ∃ (L₀ : ℕ) (K₁ K₂ : ℝ),0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ {G : BipartiteMultigraph} {b m k S p ell : ℕ}
      (spec : LookupSeparatorSpec G m k S (C*Nat.ceil ((b:ℝ)^((3:ℝ)/4)))),
    let L := Nat.clog 2 S
    let D := Nat.clog 32 (4*m)
    let κ := 4*L
    let g := 64*(S+1)*(L+1)*2^L*64^D
    let J := 1217*(C+1)^3
    L₀ ≤ L → 0 < b → 0 < m → b ≤ C*(4*m*k) → 4*m*k ≤ C*b → S ≤ C*m*b → m ≤ C*blockCount b → 0 < p → p ≤ S →
    ∃ c : Fin κ→ZMod 2,let f := (X:ℤ[X])^κ+∑ j,monomial j.val ((c j).val:ℤ)
    f.Monic ∧ f.natDegree=κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2))) ∧
    let B₀ := AdjoinRoot (f.map (Int.castRingHom (ZMod (2^(p+g)))))
    let B := AdjoinRoot ((X:B₀[X])^ell)
    ∀ T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→B,
      ∃ (N : ℕ) (w : Fin N→B) (R : Fin N→BipartiteMultigraph)
        (A : (j : Fin N)→(v : Fin (R j).nV)→(Fin ((R j).deg v)→Bool)→B),
        (N:ℝ) ≤ Real.exp (K₁*((b:ℝ)/(L:ℝ)^(7/40:ℝ))+K₂*(L:ℝ)^(13/10:ℝ)) ∧
        (∀ j,(R j).nE=4*m*k ∧ (R j).nV ≤ 4*m+64^D ∧
          let Δ := max (R j).maxDeg (Nat.ceil ((b:ℝ)^((9:ℝ)/10)))
          let ρ := max 1 (Nat.floor (Real.logb 2 ((b:ℝ)/(Δ:ℝ))))
          Δ*m ≤ J*b ∧ logSafe m ≤ ((J:ℝ)+2)*ρ) ∧
        (∑ j,w j*BTNContract (R j) (A j))=(2:B)^g*BTNContract G T := by
  exact FiniteResidualContraction.full C
