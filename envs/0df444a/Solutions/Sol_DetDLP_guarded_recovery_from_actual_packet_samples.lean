-- Prove2me | solution 1 for DetDLP.guarded_recovery_from_actual_packet_samples
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:43:51.506627+00:00
-- url     : https://prove2.me/submissions/2a64c7f4-9e1b-4d2e-a600-83a39eb80741

import Definitions.Def_DetDLP_OrientedPacketInstance
import Mathlib
import Definitions.Def_DetDLP_PacketKernel
import Theorems.Thm_DetDLP_tapered_hermite_recovery_weights

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
namespace DetDLP.IntegralPacketSample
open Finset Polynomial OrientedPacketInstance PacketPolynomialForm CauchyLocalForm
variable {a N : ℕ} (G : BipartiteMultigraph) (active : Fin N→Finset (Pos a)) (L : Fin G.nE≃Address active)
variable {H : Type} [CommRing H] [Algebra ℚ H] (I : Subring H)
variable (closed : ∀ q : ℚ,(q=0 ∨ 0≤padicValRat 2 q)→algebraMap ℚ H q∈I)
variable (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I)

noncomputable def parent : H[X] :=
  form G active L (fun v x => C (T v x:H)) (fun d => (raw d).map (algebraMap ℚ H))
theorem origin : (parent G active L I T).eval 0 = BTNContract G (fun v x => (T v x:H)) := by
  have h := map_form G active L (Polynomial.evalRingHom (0:H)) (fun v x => C (T v x:H))
    (fun d => (raw d).map (algebraMap ℚ H))
  change (parent G active L I T).eval 0=_ at h
  rw [h]
  convert delta G active L (fun v x => (T v x:H)) using 2
  · simp
  · funext d
    change ((raw d).map _).eval 0=_
    rw [← coeff_zero_eq_eval_zero,coeff_map,coeff_zero_eq_eval_zero,raw_at_zero]
    split_ifs <;> simp
theorem degree_bound : (parent G active L I T).natDegree≤G.nE*(2^(a+1)-1) :=
  degree G active L (fun v x => (T v x:H)) _ _ (fun d => natDegree_map_le.trans (raw_degree d))

noncomputable def localPoly (t : J a) : I[X] :=
  form G active L (fun v x => C (T v x)) (fun d => (intKernel t d).map (embed I closed))

theorem exact_local (t : J a) :
    (localPoly G active L I closed T t).map I.subtype=(parent G active L I T).comp ((centre t).map (algebraMap ℚ H)) := by
  let C₁ := (centre t).map (algebraMap ℚ H)
  let g := algebraMap ℚ H
  have left := map_form G active L (Polynomial.mapRingHom I.subtype) (fun v x => C (T v x))
    (fun d => (intKernel t d).map (embed I closed))
  have right := map_form G active L (Polynomial.compRingHom C₁) (fun v x => C (T v x:H))
    (fun d => (raw d).map g)
  change (localPoly G active L I closed T t).map I.subtype=_ at left
  change (parent G active L I T).comp C₁=_ at right
  rw [left,right]
  congr 1
  · funext v x; simp [C₁]
  · funext d
    change (((intKernel t d).map (embed I closed)).map I.subtype)=((raw d).map g).comp C₁
    have maps : I.subtype.comp (embed I closed)=g.comp O.subtype := rfl
    rw [Polynomial.map_map,maps,← Polynomial.map_map,int_identity,Polynomial.map_comp]

theorem local_degree (t : J a) :
    (localPoly G active L I closed T t).natDegree≤G.nE*(2^(a+1)-1) := by
  have cap : (centre t).natDegree≤1 := by
    unfold centre; rw [add_comm]; exact natDegree_linear_le
  rw [← natDegree_map_eq_of_injective (f:=I.subtype) Subtype.val_injective,exact_local]
  have h := Nat.mul_le_mul (degree_bound G active L I T) (natDegree_map_le.trans cap :
    ((centre t).map (algebraMap ℚ H)).natDegree≤1)
  exact natDegree_comp_le.trans (by simpa using h)

theorem finite_local {p : ℕ} (t : J a) (U : J a→(ZMod (2^p))[X]) (rep : Represents t U)
    (R : Type) [CommRing R] [Algebra (ZMod (2^p)) R] (φ : I→+*R) (z : R) :
    (localPoly G active L I closed T t).eval₂ φ z =
      ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,DeformedContraction.weight (fun v e => φ (T v e)) x y*
        ∏ e,OrientedPacketInstance.selector G active L U z x y e := by
  let e := Polynomial.eval₂RingHom φ z
  have left := map_form G active L e (fun v b => C (T v b))
    (fun d => (intKernel t d).map (embed I closed))
  change (localPoly G active L I closed T t).eval₂ φ z=_ at left
  rw [left,← residue G active L]
  congr 1
  · funext v b; simp [e]
  · funext d
    change ((intKernel t d).map (embed I closed)).eval₂ φ z=_
    rw [← eval_map,entry_reduce I closed φ t U rep,eval_map]
end DetDLP.IntegralPacketSample
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
namespace DetDLP.SampleJetLift
open Polynomial Finset
variable {I R : Type} [CommRing I] [CommRing R]
theorem weights (N : ℕ) (φ : I→+*R) (grid : Fin N→R) (units : ∀ i j,i≠j→IsUnit (grid i-grid j)) :
    ∃ w : ℕ→Fin N→R,∀ f : I[X],f.natDegree<N→∀ j,
    φ (f.coeff j)=∑ k,w j k*f.eval₂ φ (grid k) := by
  classical
  obtain ⟨w,hw⟩ := FiniteJetInterpolation.reconstruct N grid units
  refine ⟨fun j => if h : j<N then w ⟨j,h⟩ else fun _ => 0,?_⟩
  intro f hf j
  by_cases hj : j<N
  · have h := hw (f.map φ) (natDegree_map_le.trans_lt hf) ⟨j,hj⟩
    simpa only [dif_pos hj,coeff_map,eval_map] using h
  · simp [hj,coeff_eq_zero_of_natDegree_lt (hf.trans_le (Nat.le_of_not_gt hj))]
end DetDLP.SampleJetLift
end

section
namespace DetDLP.GuardedRootSum
open Finset DyadicGrid
variable {H : Type} [CommRing H] [Algebra ℚ H] (I : Subring H)
variable (closed : ∀ q : ℚ,(q=0 ∨ 0≤padicValRat 2 q)→algebraMap ℚ H q∈I)

include closed
theorem normalized (w : ℚ) (L : ℕ) (bound : w=0 ∨ -(L:ℤ)≤padicValRat 2 w) :
    (2:H)^L*algebraMap ℚ H w∈I := by
  have v2 : Prec 1 (2:ℚ) := Or.inr ((padicValRat.self (by decide : 1<2)).ge)
  have hw : Prec (-(L:ℤ)) w := bound
  have cap : Prec 0 ((2:ℚ)^L*w) := by simpa using (v2.pow L).mul hw
  simpa only [map_mul,map_pow,map_ofNat] using closed _ cap

theorem term (w : ℚ) (P L Q : ℕ) (guard : P+L≤Q) (bound : w=0 ∨ -(L:ℤ)≤padicValRat 2 w)
    (x y : I) (eq : (2:I)^Q ∣ x-y) :
    ∃ e : I,algebraMap ℚ H w*((x:H)-(y:H))=(2:H)^P*(e:H) := by
  obtain ⟨q,hq⟩ := eq
  let norm : I := ⟨_,normalized I closed w L bound⟩
  refine ⟨norm*(2:I)^(Q-(P+L))*q,?_⟩
  have eq' := congrArg I.subtype hq
  simp only [map_sub,map_mul,map_pow,map_ofNat,Subring.subtype_apply] at eq'
  rw [eq']
  have pow : (2:H)^Q=(2:H)^P*2^L*2^(Q-(P+L)) := by
    rw [←pow_add,←pow_add,Nat.add_sub_of_le guard]
  rw [pow]; change _=(2:H)^P*(((2:H)^L*algebraMap ℚ H w)*2^(Q-(P+L))*(q:H)); ring

theorem accumulate {α : Type} [Fintype α] (m L Q : α→ℕ) (P : ℕ) (w : α→ℕ→ℚ)
    (bound : ∀ t j,w t j=0 ∨ -(L t:ℤ)≤padicValRat 2 (w t j)) (guard : ∀ t,P+L t≤Q t)
    (x y : α→ℕ→I)
    (approx : ∀ t j,j< m t→(2:I)^Q t ∣ x t j-y t j) :
    ∃ E : I,(∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*(x t j:H))-
      (∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*(y t j:H))=(2:H)^P*(E:H) := by
  classical
  let A (t : α) := Fin (m t)
  have each (t : α) (j : A t) := term I closed (w t j.val) P (L t) (Q t) (guard t) (bound t j.val)
    (x t j.val) (y t j.val) (approx t j.val j.isLt)
  choose e he using each
  refine ⟨∑ t,∑ j : A t,e t j,?_⟩
  have sumE : ((∑ t,∑ j : A t,e t j : I):H)=∑ t,∑ j : A t,(e t j:H) := by
    change I.subtype (∑ t,∑ j : A t,e t j)=_; simp only [map_sum,Subring.subtype_apply]
  rw [sumE,←sum_sub_distrib]
  simp only [←sum_sub_distrib,←mul_sub,←Fin.sum_univ_eq_sum_range,mul_sum]
  apply sum_congr rfl; intro t _
  apply sum_congr rfl; intro j _; exact he t j
end DetDLP.GuardedRootSum
end

section
namespace DetDLP.GuardedPacketSamples
open Finset Polynomial DetDLP.OrientedPacketInstance

theorem full {a N : ℕ} (G : BipartiteMultigraph) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
    (P h u : ℕ) (hM : 0<G.nE) (lo : 3*G.nE≤h*u) (hi : h*u≤4*G.nE) :
    let Tm := univ.erase (0:ZMod (2^(a+1)))
    let v (t : ↥Tm) := padicValNat 2 t.val.val
    let m (t : ↥Tm) := h*(u-v t)
    let D (t : ↥Tm) := 2^(a-v t)
    let loss (t : ↥Tm) := 6*h*D t+4*G.nE*(a+1)
    let Q (t : ↥Tm) := P+8*h*D t+8*G.nE*(a+1)
    let n := G.nE*(2^(a+1)-1)+1
    ∃ w : ↥Tm→ℕ→ℚ, (∀ t j,w t j=0 ∨ -(loss t:ℤ)≤padicValRat 2 (w t j)) ∧
    ∀ (H : Type) [CommRing H] [Algebra ℚ H] (I : Subring H),
      (∀ q : ℚ,(q=0 ∨ 0≤padicValRat 2 q)→algebraMap ℚ H q∈I) →
    ∀ (R : ↥Tm→Type) [∀ t,CommRing (R t)] [∀ t,Algebra (ZMod (2^Q t)) (R t)]
      (π : (t : ↥Tm)→I→+*R t) (lift : (t : ↥Tm)→R t→I),
      (∀ t x,π t (lift t x)=x) → (∀ t x,π t x=0→(2:I)^Q t ∣ x) →
    ∀ (grid : (t : ↥Tm)→Fin n→R t), (∀ t i j,i≠j→IsUnit (grid t i-grid t j)) →
    ∃ V : (t : ↥Tm)→ℕ→Fin n→R t,∀ (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I)
      (U : (t : ↥Tm)→ZMod (2^(a+1))→(ZMod (2^Q t))[X]), (∀ t,Represents t.val (U t)) →
      let sample (t : ↥Tm) (j : Fin n) :=
        ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v z => π t (T v z)) x y *
            ∏ e,selector G active L (U t) (grid t j) x y e
      let jet (t : ↥Tm) (j : ℕ) := lift t (∑ k,V t j k*sample t k)
      ∃ E : I, (∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*(jet t j:H))-
        BTNContract G (fun v z => (T v z:H))=(2:H)^P*(E:H) := by
  classical
  intro Tm v m D loss Q n
  obtain ⟨w,bound,recov⟩ := tapered_hermite_recovery_weights a G.nE h u hM lo hi (fun z => z.valMinAbs) ZMod.coe_valMinAbs
  have bw (t : ↥Tm) (j : ℕ) : w t j=0 ∨ -(loss t:ℤ)≤padicValRat 2 (w t j) := by
    simpa only [loss,D,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using bound t j
  refine ⟨w,bw,?_⟩
  intro H _ _ I closed R _ _ π lift section' kernel grid units
  choose V hV using fun t => SampleJetLift.weights n (π t) (grid t) (units t)
  refine ⟨V,?_⟩
  intro T U rep sample jet
  let F := IntegralPacketSample.parent G active L I T
  let f (t : ↥Tm) := IntegralPacketSample.localPoly G active L I closed T t.val
  have origin := IntegralPacketSample.origin G active L I T
  have actual := recov H F (IntegralPacketSample.degree_bound G active L I T)
  have identity (t : ↥Tm) : (f t).map I.subtype=F.comp ((CauchyLocalForm.centre t.val).map (algebraMap ℚ H)) :=
    IntegralPacketSample.exact_local G active L I closed T t.val
  have centre (t : ↥Tm) : ((CauchyLocalForm.centre t.val).map (algebraMap ℚ H))=
      C (algebraMap ℚ H (t.val.valMinAbs:ℚ))+C (algebraMap ℚ H ((2:ℚ)^(a+1)))*X := by simp only [CauchyLocalForm.centre,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C]
  have hactual : BTNContract G (fun v z => (T v z:H))=
      ∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*((f t).coeff j:H) := by
    rw [←origin]; apply actual.trans
    apply sum_congr rfl; intro t _; apply sum_congr rfl; intro j _
    congr 1
    rw [← centre,← identity,coeff_map]; rfl
  have eval (t : ↥Tm) (k : Fin n) : (f t).eval₂ (π t) (grid t k)=sample t k :=
    IntegralPacketSample.finite_local G active L I closed T t.val (U t) (rep t) (R t) (π t) (grid t k)
  have exactJet (t : ↥Tm) (j : ℕ) : π t (jet t j)=π t ((f t).coeff j) := by
    have degree : (f t).natDegree<n := Nat.lt_succ_of_le (IntegralPacketSample.local_degree G active L I closed T t.val)
    change π t (lift t _)=_
    rw [section',hV t _ degree j]; simp only [eval]
  have remainder (t : ↥Tm) (j : ℕ) : (2:I)^Q t ∣ jet t j-(f t).coeff j := by
    apply kernel t; rw [map_sub,exactJet,sub_self]
  rw [hactual]
  exact GuardedRootSum.accumulate I closed m loss Q P w bw
    (fun t => by dsimp [Q,loss]; simp only [Nat.mul_assoc]; omega) jet (fun t j => (f t).coeff j) (fun t j _ => remainder t j)
end DetDLP.GuardedPacketSamples
end

open DetDLP Finset Polynomial DetDLP.OrientedPacketInstance

theorem solution {a N : ℕ} (G : BipartiteMultigraph) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
    (P h u : ℕ) (hM : 0<G.nE) (lo : 3*G.nE≤h*u) (hi : h*u≤4*G.nE) :
    let Tm := univ.erase (0:ZMod (2^(a+1)))
    let v (t : ↥Tm) := padicValNat 2 t.val.val
    let m (t : ↥Tm) := h*(u-v t)
    let D (t : ↥Tm) := 2^(a-v t)
    let loss (t : ↥Tm) := 6*h*D t+4*G.nE*(a+1)
    let Q (t : ↥Tm) := P+8*h*D t+8*G.nE*(a+1)
    let n := G.nE*(2^(a+1)-1)+1
    ∃ w : ↥Tm→ℕ→ℚ, (∀ t j,w t j=0 ∨ -(loss t:ℤ)≤padicValRat 2 (w t j)) ∧
    ∀ (H : Type) [CommRing H] [Algebra ℚ H] (I : Subring H),
      (∀ q : ℚ,(q=0 ∨ 0≤padicValRat 2 q)→algebraMap ℚ H q∈I) →
    ∀ (R : ↥Tm→Type) [∀ t,CommRing (R t)] [∀ t,Algebra (ZMod (2^Q t)) (R t)]
      (π : (t : ↥Tm)→I→+*R t) (lift : (t : ↥Tm)→R t→I),
      (∀ t x,π t (lift t x)=x) → (∀ t x,π t x=0→(2:I)^Q t ∣ x) →
    ∀ (grid : (t : ↥Tm)→Fin n→R t), (∀ t i j,i≠j→IsUnit (grid t i-grid t j)) →
    ∃ V : (t : ↥Tm)→ℕ→Fin n→R t,∀ (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I)
      (U : (t : ↥Tm)→ZMod (2^(a+1))→(ZMod (2^Q t))[X]), (∀ t,Represents t.val (U t)) →
      let sample (t : ↥Tm) (j : Fin n) :=
        ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v z => π t (T v z)) x y *
            ∏ e,selector G active L (U t) (grid t j) x y e
      let jet (t : ↥Tm) (j : ℕ) := lift t (∑ k,V t j k*sample t k)
      ∃ E : I, (∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*(jet t j:H))-
        BTNContract G (fun v z => (T v z:H))=(2:H)^P*(E:H) := by
  exact GuardedPacketSamples.full G active L P h u hM lo hi
