-- Prove2me | solution 1 for DetDLP.d4_unroll_guard_and_residual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:02:20.718513+00:00
-- url     : https://prove2.me/submissions/962db2aa-4899-477c-9bf7-749819468e04

import Definitions.Def_DetDLP_D4GuardWeight
import Definitions.Def_DetDLP_D4Plan
import Theorems.Thm_DetDLP_terminal_digit_query_size_and_count
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
set_option autoImplicit false
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

namespace DetDLP.IntegralJetTower
open Polynomial Finset

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

end DetDLP.IntegralJetTower
open DetDLP DetDLP.D4Plan DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4GuardTree DetDLP.D3Stopped Polynomial Finset
private theorem width_le (S t : ℕ) : width S t ≤ D3Stopped.level S := (Nat.div_le_self ..).trans (Nat.div_le_self ..)
private theorem shift_step (S t : ℕ) : shift S (t+1) = shift S t + 2 * width S (t+1) := by simp [shift,Finset.sum_range_succ,Nat.mul_add]
private theorem shift_init (S : ℕ) : shift S 0 = 2 * width S 0 := by simp [shift]
private theorem shift_mono (S : ℕ) : Monotone (shift S) := monotone_nat_of_le_succ fun t => by rw [shift_step]; omega
private theorem shift_small (S t : ℕ) : 32768 * shift S t ≤ D3Stopped.level S := by
  have h : shift S t + 2 * width S t ≤ 4*(D3Stopped.level S/131072) := by
    induction t with
    | zero => simp [shift_init,width]; omega
    | succ t ih =>
      rw [shift_step]; have h : width S (t+1) = width S t / 2 := by simp only [width,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_assoc]
      rw [h]; omega
  omega
private theorem reduce_repr {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (q : ℕ) (z : B f l p) : red f l q (repr hf z)=lift hf q z := by
  change MonicSpecialization.specialize _ (IntegralJetTower.Z_natural (Int.castRingHom (ZMod (2^q))) f l) (AdjoinRoot.mk _ _) = _
  rw [MonicSpecialization.spec_mk]
  unfold lift
  congr 1
  simp only [Polynomial.map_sum,Polynomial.map_monomial]
  apply sum_congr rfl; intro j _
  congr 1
  change MonicSpecialization.specialize _ (IntegralJetTower.F_natural (Int.castRingHom (ZMod (2^q))) f) (AdjoinRoot.mk _ _) = _
  rw [MonicSpecialization.spec_mk];simp only [Polynomial.map_sum, Polynomial.map_monomial, Int.coe_castRingHom, Int.cast_natCast]
private theorem self_lift {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (z : B f l p) : lift hf p z=z := by
  have cell (x : U f p) : AdjoinRoot.mk _ (∑ i : Fin f.natDegree, monomial i.val (((AdjoinRoot.modByMonicHom (hf.map _) x).coeff i.val).val : ZMod (2^p)))=x := by
    simp only [ZMod.natCast_zmod_val]
    have he := sum_modByMonic_coeff (hf.map (Int.castRingHom (ZMod (2^p)))) (p := AdjoinRoot.modByMonicHom (hf.map _) x) (degree_map_le.trans (degree_le_natDegree (p:=f)))
    rw [←AdjoinRoot.modByMonicHom_mk (hf.map _),AdjoinRoot.mk_leftInverse (hf.map _) x] at he
    rw [he,AdjoinRoot.mk_leftInverse] <;> exact hf.map _
  unfold lift word
  simp only [cell]
  have he := sum_modByMonic_coeff (monic_X_pow l : ((X:(U f p)[X])^l).Monic) (p:=AdjoinRoot.modByMonicHom (monic_X_pow l) z) (degree_X_pow_le _)
  rw [←AdjoinRoot.modByMonicHom_mk (monic_X_pow l),AdjoinRoot.mk_leftInverse (monic_X_pow l) z] at he
  rw [he,AdjoinRoot.mk_leftInverse] <;> exact monic_X_pow l
private theorem ker {f : ℤ[X]} {l : ℕ} (hf : f.Monic) (q : ℕ) (x : IntJet f l) (h : red f l q x=0) : (2:IntJet f l)^q ∣ x := by
  apply IntegralJetTower.divides (Int.castRingHom (ZMod (2^q))) f l hf q _ x h
  intro n hn;simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd n (2^q)).mp hn
private theorem vanish {f : ℤ[X]} {l : ℕ} (q : ℕ) : (2:B f l q)^q=0 := by
  have H : (2:ZMod (2^q))^q=0 := by exact_mod_cast (ZMod.natCast_self (2^q))
  simpa only [map_pow,map_ofNat,map_zero] using congrArg (algebraMap (ZMod (2^q)) (B f l q)) H
private theorem inc_allow {S M d i D : ℕ} (hd : d ≤ D) (hm : M ≤ S) (hu : 1 ≤ width S d) : increase M (shift S d) (width S d) i ≤ localAllowance S D := by
  let a := shift S d; let u := width S d; let L := shift S D
  change 1 ≤ u at hu
  have ha : a ≤ L := shift_mono S hd
  have hm' : mult M u ≤ 3*M+1 := by
    apply Nat.le_of_lt_succ; apply (Nat.div_lt_iff_lt_mul hu).2
    have hh := Nat.mul_le_mul_left (3*M+1) hu
    change 3*M+u-1 < (3*M+1+1)*u;rw [Nat.add_mul,one_mul];omega
  have ht : tileScale a i ≤ 2^L := Nat.pow_le_pow_right (by decide) ((Nat.sub_le ..).trans ha)
  change 8*mult M u*tileScale a i + 8*M*(a+1) ≤ 40*(S+1)*(L+1)*2^L
  have hp := Nat.pow_pos (n:=L) (by decide : 0<2)
  have h1 : 8*(3*M+1)*2^L ≤ 32*(S+1)*(L+1)*2^L := by apply Nat.mul_le_mul_right; exact (show 8*(3*M+1) ≤ 32*(S+1) by omega).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have h2 : 8*M*(a+1) ≤ 8*(S+1)*(L+1)*2^L := (Nat.mul_le_mul (Nat.mul_le_mul_left 8 (by omega : M ≤ S+1)) (by omega : a+1 ≤ L+1)).trans (Nat.le_mul_of_pos_right _ hp)
  nlinarith only [Nat.mul_le_mul (Nat.mul_le_mul_left 8 hm') ht,h1,h2]
private theorem loss_inc (M a u i : ℕ) : loss M a u i ≤ increase M a u i := by unfold loss increase;nlinarith
private theorem loss_mono (M a u i : ℕ) : loss M a u i ≤ loss M a u 0 := by unfold loss tileScale; simp only [Nat.sub_zero];gcongr <;> omega
private noncomputable def intLeaves {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l : ℕ} : {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → IntJet f l
  | _,_,_,_,.leaf z,_ => repr hf z
  | _,_,_,_,.step _ _ _ _ _ _ next,r => ∏ g, intLeaves (next r.1 g) (r.2 g)
private theorem leaf_red {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p} (e : Expansion S f hf l d k p z) (q : ℕ) (r : e.Ranks) : red f l q (intLeaves e r) = e.leaves q r := by
  induction e with
  | leaf => exact reduce_repr ..
  | step s ok T η hm hu next ih => simp only [intLeaves,Expansion.leaves,map_prod,ih]
private noncomputable def flat (A : ℕ) {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p} (e : Expansion S f hf l d k p z) := ∑ r, e.paddedWeight A r*intLeaves e r
private theorem flat_step (A : ℕ) {S d k b p l : ℕ} {f : ℤ[X]} {hf : f.Monic} {G : Graph} {host : Fin b → Fin G.nV}
    {lbl : Label (shift S d) G} {hu : width S d ≤ shift S d} (s : Step lbl hu f l p) (ok : s.sound hf) (T : OpenTensor host (B f l p)) (η : Fin b → Bool) (hm : G.nE ≤ S) (hw : 1≤width S d) (next : (ν : Branch s) → (g : Fin 64) → let c := s.child ν.1 ν.2.1 ν.2.2 g; Expansion S f hf l (d+1) k _ (BTNContract c.graph (c.tensor (lift hf _) (pin T η)))) :
    flat A (.step s ok T η hm hw next) = ∑ ν, 2^(A-loss G.nE (shift S d) (width S d) (AppendixD4.level ν.1.val)) * repr hf (AdjoinRoot.of _ (quotient s ν) : B f l _) * ∏ g, flat A (next ν g) := by
  classical
  unfold flat
  change ∑ r : (ν : Branch s) × ((g : Fin 64) → (next ν g).Ranks), _ = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl; intro ν _
  rw [Fintype.prod_sum,Finset.mul_sum];apply sum_congr rfl;intro v _
  simp only [Expansion.paddedWeight,intLeaves,Finset.prod_mul_distrib,mul_assoc]
private theorem nearProd {R : Type} [CommRing R] (p b : ℕ) (x y : Fin 64 → R) (h : ∀ g, (2:R)^(p+b) ∣ x g-2^b*y g) :
    (2:R)^(p+64*b) ∣ (∏ g,x g)-2^(64*b)*∏ g,y g := by
  classical
  choose e he using h
  have he' (g) : x g=2^b*(y g+2^p*e g) := by have := he g;rw [pow_add] at this;linear_combination this
  let I := Ideal.span ({(2:R)^p}:Set R)
  have hg (g) : Ideal.Quotient.mk I (y g+2^p*e g)=Ideal.Quotient.mk I (y g) := by
    rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)),zero_mul,add_zero]
  have hp : (2:R)^p ∣ (∏ g,(y g+2^p*e g))-∏ g,y g := by
    apply Ideal.mem_span_singleton.mp; apply (Ideal.Quotient.eq_zero_iff_mem (I:=I)).mp
    rw [map_sub,map_prod,map_prod];simp only [hg,sub_self]
  obtain ⟨v,hv⟩ := hp
  refine ⟨v,?_⟩;simp only [he',prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_fin,←pow_mul,b.mul_comm 64];rw [←mul_sub,hv,pow_add];ring
private theorem localize {S d p l b : ℕ} {f : ℤ[X]} {hf : f.Monic} {G : Graph} {host : Fin b → Fin G.nV}
    {lbl : Label (shift S d) G} {hu : width S d ≤ shift S d} (s : Step lbl hu f l p) (ok : s.sound hf) (T : OpenTensor host (B f l p)) (η : Fin b → Bool) :
    let a := shift S d; let u := width S d; let M := G.nE; let g := loss M a u 0
    let v (ν : Branch s) := loss M a u (AppendixD4.level ν.1.val)
    let w (ν : Branch s) := repr hf (AdjoinRoot.of _ (quotient s ν) : B f l _)
    let y (ν : Branch s) (j : Fin 64) := let c := s.child ν.1 ν.2.1 ν.2.2 j; repr hf (BTNContract c.graph (c.tensor (lift hf _) (pin T η)))
    (2:IntJet f l)^(p+g) ∣ (∑ ν, 2^(g-v ν)*w ν*∏ j,y ν j) - 2^g*repr hf (BTNContract G (pin T η)) := by
  intro a u M g v w y
  apply ker hf;rw [map_sub,map_mul,map_pow,map_ofNat,reduce_repr,map_sum]
  apply sub_eq_zero.mpr
  refine Eq.trans (sum_congr rfl (fun ν _ => ?_)) (ok _ host T η).2
  simp only [map_mul,map_pow,map_ofNat,map_prod,y,reduce_repr,w]
  have hh := (s.weight_guard ν.1 ν.2.1).choose_spec
  have eq := congrArg (AdjoinRoot.of ((X:(U f (p+g))[X])^l)) hh
  simp only [map_mul,map_pow,map_ofNat] at eq
  rw [self_lift];congr 1;exact eq.symm
private theorem distribute {R I : Type} [CommRing R] [Fintype I] (p g A b : ℕ) (hg : g≤A) (v : I → ℕ) (w : I → R) (y X : I → Fin 64 → R) (z : R)
    (hv : ∀ i,v i≤g) (hy : ∀ i j,(2:R)^(p+v i+b) ∣ X i j-2^b*y i j)
    (hl : (2:R)^(p+g) ∣ (∑ i,2^(g-v i)*w i*∏ j,y i j) - 2^g*z) :
    (2:R)^(p+(A+64*b)) ∣ (∑ i, 2^(A-v i)*w i*∏ j,X i j)-2^(A+64*b)*z := by
  let c := 64*b
  have hterm (i) : (2:R)^(p+(A+c)) ∣ 2^(A-v i)*w i*((∏ j,X i j)-2^c*∏ j,y i j) := by
    obtain ⟨e,he⟩ := nearProd (p+v i) b (X i) (y i) (hy i)
    refine ⟨w i*e,?_⟩;change (_ : R)*(_-2^(64*b)*_) = _
    rw [he,show p+(A+c)=(A-v i)+(p+v i+64*b) by have := hv i;dsimp [c];omega,pow_add];ring
  obtain ⟨e,he⟩ := hl
  have hmain : (2:R)^(p+(A+c)) ∣ 2^(A-g+c)*((∑ i,2^(g-v i)*w i*∏ j,y i j) - 2^g*z) := by
    rw [he]; refine ⟨e,?_⟩;rw [←mul_assoc,←pow_add];congr 2;omega
  have H := dvd_add (Finset.dvd_sum (s:=Finset.univ) (fun i _ => hterm i)) hmain
  convert H using 1
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  have eq (i) : (2:R)^(A-v i)*w i*(2^c*∏ j,y i j)=2^(A-g+c)*(2^(g-v i)*w i*∏ j,y i j) := by
    have h : (2:R)^(A-v i)*2^c=2^(A-g+c)*2^(g-v i) := by rw [←pow_add,←pow_add];congr 1;have := hv i;omega
    linear_combination w i*(∏ j,y i j)*h
  simp_rw [eq]; rw [←mul_assoc,←pow_add,show A-g+c+g=A+64*b by dsimp [c];omega];ring
private theorem inductiveGuard {D S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p} (e : Expansion S f hf l d k p z) (hd : d+k ≤ D) :
    (2:IntJet f l)^(p+localAllowance S D*slots k) ∣ flat (localAllowance S D) e-2^(localAllowance S D*slots k)*repr hf z := by
  classical
  induction e with
  | @leaf d k p z =>
    have card1 : Fintype.card (Expansion.leaf (S:=S) (d:=d) (k:=k) (hf:=hf) z).Ranks = 1 := Fintype.card_unique (α:=Unit)
    simp only [flat,Expansion.paddedWeight,intLeaves,Finset.sum_const,Finset.card_univ,card1,one_nsmul,sub_self,dvd_zero]
  | @step d k p b G host lbl hu s ok T η hm hw next ih =>
    rw [flat_step,slots, Nat.mul_add,Nat.mul_one,show localAllowance S D*(64*slots k)=64*(localAllowance S D*slots k) by ring]
    apply distribute (g:=loss G.nE (shift S d) (width S d) 0) (v:=fun ν : Branch s => loss G.nE (shift S d) (width S d) (AppendixD4.level ν.1.val)) (y:=fun ν j => let c := s.child ν.1 ν.2.1 ν.2.2 j;repr hf (BTNContract c.graph (c.tensor (lift hf _) (pin T η))))
    · exact (loss_inc ..).trans (inc_allow (by omega : d ≤ D) hm hw)
    · intro ν;apply loss_mono
    · intro ν j
      exact dvd_trans (pow_dvd_pow _ (Nat.add_le_add_right (Nat.add_le_add_left (loss_inc ..) _) _)) (ih ν j (by omega))
    · exact localize s ok T η
private theorem slot_bound (k : ℕ) : slots k ≤ 64^k := by
  suffices slots k < 64^k by omega
  induction k with | zero => decide | succ k ih => simp [slots,pow_succ];omega
private theorem cleared {S D p l : ℕ} {f : ℤ[X]} {hf : f.Monic} {z : B f l p} (e : Expansion S f hf l 0 D p z) :
    let g := totalGuard S D; let q := g+p
    (∑ r, 2^(g-localAllowance S D*slots D)*red f l q (e.paddedWeight (localAllowance S D) r)*e.leaves q r) = 2^g*lift hf q z := by
  intro g q
  have h := inductiveGuard (D:=D) e (by omega); obtain ⟨v,hv⟩ := h
  let b := localAllowance S D*slots D
  have hle : b ≤ g := Nat.mul_le_mul_left _ (slot_bound D)
  have eq : (2:IntJet f l)^(g-b)*flat (localAllowance S D) e-2^g*repr hf z=2^q*v := by
    have hh := congrArg ((2:IntJet f l)^(g-b)*·) hv
    simp only [mul_sub,←mul_assoc,←pow_add] at hh
    change _-2^(g-b+b)*_ = 2^(g-b+(p+b))*_ at hh
    rw [show g-b+b=g by omega,show g-b+(p+b)=q by dsimp [q];omega] at hh;exact hh
  have hh := congrArg (red f l q) eq
  simp only [map_sub,map_mul,map_pow,map_ofNat,vanish,zero_mul,sub_eq_zero,reduce_repr] at hh
  rw [←hh];unfold flat;rw [map_sum,Finset.mul_sum];apply sum_congr rfl;intro i _;rw [map_mul,leaf_red];ring
private theorem leaves_bounded {D S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p} (e : Expansion S f hf l d k p z) (r : e.Ranks) (hd : d+k ≤ D) : ∀ q ∈ e.leafPrec r,q ≤ p+localAllowance S D*k := by
  induction e with
  | leaf => simp [Expansion.leafPrec]
  | @step d k p b G host lbl hu s ok T η hm hw next ih =>
    intro q h; obtain ⟨v,hv,hq⟩ := List.mem_flatten.mp h;obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hv
    have hh := ih r.1 g (r.2 g) (by omega) q hq
    have hi := inc_allow (i:=AppendixD4.level r.1.1.val) (by omega : d ≤ D) hm hw
    change q ≤ (p+increase G.nE (shift S d) (width S d) _)+localAllowance S D*k at hh
    rw [Nat.mul_succ];omega

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

private theorem guard_log (S m p : ℕ) (L : ℕ) (hl : 2≤L) (hs : S≤2^L) (hm : 4*m ≤ 2*S) (hp : p≤S) :
    let D := Nat.clog 32 (4*m)
    let g := 64*(S+1)*(L+1)*2^L*64^D
    p+g+1 ≤ 2^(16*L) := by
  intro D g
  have inc : 2*2^L ≤ 32^L := by
    calc
      _ = 2^(L+1) := by rw [pow_succ]; ring
      _ ≤ 2^(5*L) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have dd : D≤L := Nat.clog_le_of_le_pow (hm.trans ((Nat.mul_le_mul_left 2 hs).trans inc))
  have d64 : 64^D ≤ 2^(6*L) := calc
    _ ≤ 64^L := Nat.pow_le_pow_right (by decide) dd
    _ = _ := by rw [show (64:ℕ)=2^6 by decide,←pow_mul]
  have lsize : L+1≤2^L := Nat.lt_two_pow_self
  have sp : S+1≤2^(L+1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n:=L); omega
  have gg := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 64 sp) lsize) (Nat.le_refl (2^L))) d64
  have ge : g ≤ 2^(9*L+7) := by
    apply gg.trans_eq
    rw [show (64:ℕ)=2^6 by decide,←pow_add,←pow_add,←pow_add,←pow_add]
    congr 1; omega
  have main : S+1 ≤ 2^(9*L+7) := sp.trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ 2^(9*L+7)+2^(9*L+7) := by omega
    _ = 2^(9*L+7+1) := by rw [pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
open ResidualScalarOracle
set_option maxHeartbeats 1000000 in
theorem solution (C : ℕ) (hC : 0<C) : ∃ L₀ K : ℕ, ∀ {c : ℕ} (x : Input C c),
    let L := D3Stopped.level x.S; let D := Nat.clog 32 (4*x.m); let β := 4*x.m*x.k
    let g := totalGuard x.S D; let q := g+x.p
    L₀ ≤ L → (g:ℝ) ≤ polyBound K (D4Plan.size x) ∧
    (∀ n ≤ 4*x.m+64^D, ((digits q (digitWidth β n)^n:ℕ):ℝ) ≤ Real.exp (K*(L:ℝ)^(13/10:ℝ))) ∧
    (∀ (f : ℤ[X]) (R : Graph), f.natDegree=4*L → R.nV ≤ 4*x.m+64^D →
      precision f x.l R (digitWidth β R.nV) β ≤ K*x.b ∧ spacing f R*x.l ≤ K*x.b) ∧
    (∀ δ : ℕ, δ ≤ β/32^D+32*(L+2) ∨ (∃ M ≤ threshold x.S, δ ≤ 2*M) → δ*x.m ≤ 1217*(C+1)^3*x.b) ∧
    ∀ {f : ℤ[X]} {hf : f.Monic} {z : B f x.l x.p} (e : Expansion x.S f hf x.l 0 D x.p z),
      (∀ r, ∀ p ∈ e.leafPrec r, p ≤ q) ∧
      (∑ r, 2^(g-localAllowance x.S D*slots D)*red f x.l q (e.paddedWeight (localAllowance x.S D) r)*e.leaves q r) = 2^g*lift hf q z := by
  obtain ⟨k,e,c,hc,H⟩ := terminal_digit_query_size_and_count C
  let K := max 32 (max k ⌈c⌉₊)
  refine ⟨1024+2*C,K,?_⟩
  intro c' x L D β g q big
  have hL : 1024 ≤ L := by omega
  have hs : 2 ≤ x.S := by
    by_contra! h; have h' : x.S ≤ 2^0 := by simpa using h
    have := Nat.clog_le_of_le_pow h';change 1024 ≤ Nat.clog 2 x.S at hL;omega
  have hedge := (m14a_separator_edge_budget x.spec).1
  have hm : 4*x.m ≤ 2*x.S := (Nat.le_mul_of_pos_right _ x.hk).trans hedge
  have hmass : x.b ≤ 2*C*x.S := x.lower.trans ((Nat.mul_le_mul_left C hedge).trans_eq (by ring))
  have ha : shift x.S D ≤ L := by have := shift_small x.S D;omega
  have hg : g ≤ 64*(x.S+1)*(L+1)*2^L*64^D := by
    change 40*(x.S+1)*(shift x.S D+1)*2^(shift x.S D)*64^D ≤ _
    gcongr <;> omega
  have hK : k ≤ K := (le_max_left ..).trans (le_max_right ..)
  have hKc : c ≤ (K:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈c⌉₊ ≤ K from (le_max_right ..).trans (le_max_right ..)))
  have hh (n : ℕ) (hn : n ≤ 4*x.m+64^D) := H x.S x.m x.b x.p x.l β n (by change 24+2*C ≤ L;omega) x.hb x.hm x.hl hs hm hmass x.mb x.hS x.upper x.lm x.pS hn
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hglog := guard_log x.S x.m x.p L (by omega) (Nat.le_pow_clog (by decide) _) hm x.pS
    change x.p+64*(x.S+1)*(L+1)*2^L*64^D+1 ≤ 2^(16*L) at hglog
    have hh' : g ≤ 2^(16*L) := by omega
    have hs' : 2^(L-1) ≤ x.S := (Nat.pow_lt_of_lt_clog (by change L-1 < L;omega)).le
    have htwo : 2^L ≤ (x.S+1)^2 := by rw [show L=L-1+1 by omega,pow_succ];nlinarith only [hs',Nat.zero_le (x.S^2)]
    have hp : g ≤ (D4Plan.size x+1)^K := calc
      _ ≤ (2^L)^16 := hh'.trans_eq (by rw [←pow_mul,Nat.mul_comm])
      _ ≤ ((x.S+1)^2)^16 := Nat.pow_le_pow_left htwo _
      _ = (x.S+1)^32 := by rw [←pow_mul]
      _ ≤ _ := (Nat.pow_le_pow_left (by change x.S+1 ≤ x.S+x.desc.length+1;omega) 32).trans (Nat.pow_le_pow_right (by omega) (le_max_left ..))
    unfold polyBound
    have hKr : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K from (by decide : 1≤32).trans (le_max_left ..))
    exact (show (g:ℝ) ≤ ((D4Plan.size x:ℝ)+1)^K by exact_mod_cast hp).trans (le_mul_of_one_le_left (by positivity) hKr)
  · intro n hn
    have hd := (hh n hn).2.2.2.2.2
    have hds : digits q (digitWidth β n) ≤ (x.p+64*(x.S+1)*(L+1)*2^L*64^D)/(digitWidth β n)+1 := Nat.add_le_add_right (Nat.div_le_div_right (by dsimp [q];omega)) _
    exact (show ((digits q (digitWidth β n)^n:ℕ):ℝ) ≤ _ by exact_mod_cast Nat.pow_le_pow_left hds n).trans (hd.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKc (by positivity))))
  · intro f R hf hn
    have z := hh R.nV hn
    simp only [precision,spacing,hf,digitWidth]
    exact ⟨z.2.1.trans (Nat.mul_le_mul_right _ hK),z.2.2.2.1.trans (Nat.mul_le_mul_right _ hK)⟩
  · intro δ h
    have hdeg := ResidualDegreeRate.full _ _ _ _ _ hs (by change 16+2*C ≤ L;omega) hmass x.mb x.hS x.upper
    apply le_trans _ hdeg
    apply Nat.mul_le_mul_right
    rcases h with hh | ⟨M,hM,hh⟩
    · apply le_trans hh;apply le_trans _ (le_max_left ..);apply Nat.add_le_add_right
      exact (Nat.div_le_div_left (Nat.le_pow_clog (by decide : 1<32) (4*x.m)) (by nlinarith only [x.hm])).trans_eq (Nat.mul_div_cancel_left _ (by nlinarith only [x.hm]))
    · apply le_trans hh;apply le_trans _ (le_max_right ..);apply Nat.mul_le_mul_left;apply hM.trans
      let t := (L/32).sqrt+1; let r := L.sqrt
      have ht : 1 ≤ t := Nat.succ_pos _
      have htr : t+1 ≤ r := by
        apply Nat.le_sqrt'.mpr; have h := Nat.sqrt_le (L/32)
        have hs0 : 1 ≤ (L/32).sqrt := Nat.le_sqrt'.mpr (by omega)
        have hr' : 32*((L/32).sqrt*(L/32).sqrt) ≤ L := (Nat.mul_le_mul_left _ h).trans (by omega)
        dsimp [t];nlinarith
      have hsR : r*r ≤ x.S := (Nat.sqrt_le _).trans (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le))
      have hpos : 1 ≤ r := by omega
      change (x.S+r-1)/max 1 r ≤ x.S/t
      rw [max_eq_right hpos];apply (Nat.le_div_iff_mul_le ht).mpr
      have h1 := Nat.div_mul_le_self (x.S+r-1) r
      have h2 := Nat.mul_le_mul_right ((x.S+r-1)/r) htr
      by_contra! h
      have hdiv : r ≤ (x.S+r-1)/r := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      nlinarith only [h,h1,h2,hdiv,Nat.sub_le (x.S+r) 1]
  · intro f hf z t
    refine ⟨?_,cleared t⟩
    intro r P hP
    have hv := leaves_bounded (D:=D) t r (by omega) P hP
    have hd : D ≤ 64^D := (Nat.lt_two_pow_self (n:=D)).le.trans (Nat.pow_le_pow_left (by decide) _)
    change P ≤ g+x.p
    change localAllowance x.S D*64^D+x.p ≥ P
    have := Nat.mul_le_mul_left (localAllowance x.S D) hd;omega

end
