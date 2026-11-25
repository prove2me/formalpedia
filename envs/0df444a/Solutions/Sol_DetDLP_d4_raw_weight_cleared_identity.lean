-- Prove2me | solution 1 for DetDLP.d4_raw_weight_cleared_identity
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T10:46:32.326525+00:00
-- url     : https://prove2.me/submissions/17c75bb1-9932-4eb5-a4ba-a7ff00516d3a

import Definitions.Def_DetDLP_D4RawGuard
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

theorem divides (hf : f.Monic) (k : ℕ) (base : ∀ x,φ x=0→(2:A)^k∣x)
    (x : Z A f e) (hz : zMap φ f e x=0) : (2:Z A f e)^k∣x := by
  have first (y : U A f) (hy : uMap φ f y=0) : (2:U A f)^k∣y := by
    simpa only [map_ofNat] using MonicSpecialization.kernel φ (F_natural φ f) (hf.map _) 2 k base y hy
  simpa only [map_ofNat] using MonicSpecialization.kernel (uMap φ f) (Z_natural φ f e) (monic_X_pow e) 2 k first x hz

end DetDLP.IntegralJetTower

open DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4GuardTree DetDLP.D3Stopped Polynomial Finset
private theorem shift_step (S t : ℕ) : shift S (t+1) = shift S t + 2 * width S (t+1) := by simp [shift,Finset.sum_range_succ,Nat.mul_add]

private theorem shift_mono (S : ℕ) : Monotone (shift S) := monotone_nat_of_le_succ fun t => by rw [shift_step]; omega

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
    rw [he,AdjoinRoot.mk_leftInverse]
  unfold lift word
  simp only [cell]
  have he := sum_modByMonic_coeff (monic_X_pow l : ((X:(U f p)[X])^l).Monic) (p:=AdjoinRoot.modByMonicHom (monic_X_pow l) z) (degree_X_pow_le _)
  rw [←AdjoinRoot.modByMonicHom_mk (monic_X_pow l),AdjoinRoot.mk_leftInverse (monic_X_pow l) z] at he
  rw [he,AdjoinRoot.mk_leftInverse]
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

private noncomputable def coordAdd {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (j : Fin l) (i : Fin f.natDegree) : B f l p →+ ZMod (2^p) :=
  ((Polynomial.lcoeff (R:=ZMod (2^p)) i.val).toAddMonoidHom.comp (AdjoinRoot.modByMonicHom (hf.map _)).toAddMonoidHom).comp
    ((Polynomial.lcoeff (R:=U f p) j.val).toAddMonoidHom.comp (AdjoinRoot.modByMonicHom (monic_X_pow l)).toAddMonoidHom)

private theorem word_dvd {f : ℤ[X]} {l p t : ℕ} (hf : f.Monic) (ht : t ≤ p)
    (x : B f l p) (hx : (2 : B f l p)^t ∣ x) (j : Fin l) (i : Fin f.natDegree) :
    2^t ∣ word f l p hf x j i := by
  obtain ⟨y, hy⟩ := hx
  let c := coordAdd (p:=p) hf j i
  have h : x = (2^t : ℕ) • y := by simpa only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using hy
  have hc := congrArg c h
  rw [map_nsmul, nsmul_eq_mul] at hc
  change 2^t ∣ (c x).val
  have hh : ((c x).val : ZMod (2^p)) = ((2^t * (c y).val : ℕ) : ZMod (2^p)) := by
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hc
  apply ((ZMod.natCast_eq_natCast_iff ..).mp hh |>.dvd_iff (pow_dvd_pow 2 ht)).mpr
  exact dvd_mul_right ..

private noncomputable def packWords {f : ℤ[X]} {l : ℕ} (c : Fin l → Fin f.natDegree → ℕ) : IntJet f l :=
  AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.mk _ (∑ i : Fin f.natDegree, monomial i.val (c j i : ℤ))))

private theorem pack_scale {f : ℤ[X]} {l : ℕ} (n : ℕ) (c : Fin l → Fin f.natDegree → ℕ) :
    (n : IntJet f l) * packWords c = packWords (fun j i => n*c j i) := by
  rw [← nsmul_eq_mul]
  simp only [packWords, ← map_nsmul, Finset.smul_sum, Nat.cast_mul, ← nsmul_eq_mul]

private noncomputable def canonQuotient {G : Graph} {a u p l : ℕ} {lbl : Label a G} {hu : u≤a} {f : ℤ[X]}
    (hf : f.Monic) (s : Step lbl hu f l p) (ν : Branch s) : IntJet f l :=
  let g := loss G.nE a u 0
  let t := g - loss G.nE a u (AppendixD4.level ν.1.val)
  let W : B f l (p+g) := AdjoinRoot.of _ (s.weight ν.1 ν.2.1)
  packWords (fun j i => word f l (p+g) hf W j i / 2^t)

private theorem canon_spec {G : Graph} {a u p l : ℕ} {lbl : Label a G} {hu : u≤a} {f : ℤ[X]}
    (hf : f.Monic) (s : Step lbl hu f l p) (ν : Branch s) :
    let g := loss G.nE a u 0
    let t := g - loss G.nE a u (AppendixD4.level ν.1.val)
    (2:IntJet f l)^t * canonQuotient hf s ν = repr hf (AdjoinRoot.of _ (s.weight ν.1 ν.2.1) : B f l (p+g)) := by
  intro g t
  let W : B f l (p+g) := AdjoinRoot.of _ (s.weight ν.1 ν.2.1)
  have hW : (2:B f l (p+g))^t ∣ W := by
    obtain ⟨y, hy⟩ := s.weight_guard ν.1 ν.2.1
    refine ⟨AdjoinRoot.of _ y, ?_⟩
    simpa only [map_pow, map_ofNat, map_mul] using congrArg (AdjoinRoot.of ((X : (U f (p+g))[X])^l)) hy
  change (2:IntJet f l)^t * packWords (fun j i => word f l (p+g) hf W j i / 2^t) = packWords (fun j i => word f l (p+g) hf W j i)
  rw [←Nat.cast_ofNat (R:=IntJet f l) (n:=2), ←Nat.cast_pow, pack_scale]
  congr 1; funext j i
  exact Nat.mul_div_cancel' (word_dvd hf (by dsimp [t]; omega) W hW j i)

private noncomputable def rawPaddedWeight (A : ℕ) {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l : ℕ} :
    {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → IntJet f l
  | _, _, _, _, .leaf (k:=k) _, _ => 2^(A*slots k)
  | _, _, _, _, .step (G:=G) (d:=d) s _ _ _ _ _ next, r =>
    2^(A-loss G.nE (shift S d) (width S d) (AppendixD4.level r.1.1.val)) * canonQuotient hf s r.1 *
      ∏ j, rawPaddedWeight A (next r.1 j) (r.2 j)

private noncomputable def intLeaves {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l : ℕ} : {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → IntJet f l
  | _,_,_,_,.leaf z,_ => repr hf z
  | _,_,_,_,.step _ _ _ _ _ _ next,r => ∏ g, intLeaves (next r.1 g) (r.2 g)
private theorem leaf_red {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p} (e : Expansion S f hf l d k p z) (q : ℕ) (r : e.Ranks) : red f l q (intLeaves e r) = e.leaves q r := by
  induction e with
  | leaf => exact reduce_repr ..
  | step s ok T η hm hu next ih => simp only [intLeaves,Expansion.leaves,map_prod,ih]
private noncomputable def flat (A : ℕ) {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p} (e : Expansion S f hf l d k p z) := ∑ r, rawPaddedWeight A e r*intLeaves e r
private theorem flat_step (A : ℕ) {S d k b p l : ℕ} {f : ℤ[X]} {hf : f.Monic} {G : Graph} {host : Fin b → Fin G.nV}
    {lbl : Label (shift S d) G} {hu : width S d ≤ shift S d} (s : Step lbl hu f l p) (ok : s.sound hf) (T : OpenTensor host (B f l p)) (η : Fin b → Bool) (hm : G.nE ≤ S) (hw : 1≤width S d) (next : (ν : Branch s) → (g : Fin 64) → let c := s.child ν.1 ν.2.1 ν.2.2 g; Expansion S f hf l (d+1) k _ (BTNContract c.graph (c.tensor (lift hf _) (pin T η)))) :
    flat A (.step s ok T η hm hw next) = ∑ ν, 2^(A-loss G.nE (shift S d) (width S d) (AppendixD4.level ν.1.val)) * canonQuotient hf s ν * ∏ g, flat A (next ν g) := by
  classical
  unfold flat
  change ∑ r : (ν : Branch s) × ((g : Fin 64) → (next ν g).Ranks), _ = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl; intro ν _
  rw [Fintype.prod_sum,Finset.mul_sum];apply sum_congr rfl;intro v _
  simp only [rawPaddedWeight,intLeaves,Finset.prod_mul_distrib,mul_assoc]
private theorem nearProd {R : Type} [CommRing R] (p b : ℕ) (x y : Fin 64 → R) (h : ∀ g, (2:R)^(p+b) ∣ x g-2^b*y g) :
    (2:R)^(p+64*b) ∣ (∏ g,x g)-2^(64*b)*∏ g,y g := by
  have aux (s : Finset (Fin 64)) : (2:R)^(p+s.card*b) ∣ (∏ g ∈ s,x g)-2^(s.card*b)*∏ g ∈ s,y g := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      obtain ⟨u,hu⟩ := h i
      obtain ⟨v,hv⟩ := ih
      have ei : x i = 2^b*(y i+2^p*u) := by rw [pow_add] at hu; linear_combination hu
      have es : (∏ g ∈ s,x g) = 2^(s.card*b)*((∏ g ∈ s,y g)+2^p*v) := by rw [pow_add] at hv; linear_combination hv
      refine ⟨y i*v + u*(∏ g ∈ s,y g) + 2^p*u*v, ?_⟩
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul, Finset.prod_insert hi, Finset.prod_insert hi, ei, es]
      simp only [pow_add]; ring
  simpa only [Finset.card_univ,Fintype.card_fin] using aux Finset.univ
private theorem localize {S d p l b : ℕ} {f : ℤ[X]} {hf : f.Monic} {G : Graph} {host : Fin b → Fin G.nV}
    {lbl : Label (shift S d) G} {hu : width S d ≤ shift S d} (s : Step lbl hu f l p) (ok : s.sound hf) (T : OpenTensor host (B f l p)) (η : Fin b → Bool) :
    let a := shift S d; let u := width S d; let M := G.nE; let g := loss M a u 0
    let v (ν : Branch s) := loss M a u (AppendixD4.level ν.1.val)
    let w (ν : Branch s) := canonQuotient hf s ν
    let y (ν : Branch s) (j : Fin 64) := let c := s.child ν.1 ν.2.1 ν.2.2 j; repr hf (BTNContract c.graph (c.tensor (lift hf _) (pin T η)))
    (2:IntJet f l)^(p+g) ∣ (∑ ν, 2^(g-v ν)*w ν*∏ j,y ν j) - 2^g*repr hf (BTNContract G (pin T η)) := by
  intro a u M g v w y
  apply ker hf;rw [map_sub,map_mul,map_pow,map_ofNat,reduce_repr,map_sum]
  apply sub_eq_zero.mpr
  refine Eq.trans (sum_congr rfl (fun ν _ => ?_)) (ok _ host T η).2
  change red f l (p+g) (((2:IntJet f l)^(g-v ν)*canonQuotient hf s ν)*∏ j,y ν j) = _
  rw [canon_spec hf s ν,map_mul,reduce_repr,self_lift,map_prod]
  simp only [y,reduce_repr,g,M,a,u]
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
    simp only [flat,rawPaddedWeight,intLeaves,Finset.sum_const,Finset.card_univ,card1,one_nsmul,sub_self,dvd_zero]
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
    (∑ r, 2^(g-localAllowance S D*slots D)*red f l q (rawPaddedWeight (localAllowance S D) e r)*e.leaves q r) = 2^g*lift hf q z := by
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

open DetDLP.D4GuardTree.Expansion

private theorem exponent_budget {A g P x y : ℕ} (hg : g ≤ A) (h : x+y=P) : A-g+x = A+P-(g+y) := by omega

private theorem raw_factor {D S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p}
    (e : Expansion S f hf l d k p z) (r : e.Ranks) (hd : d+k ≤ D) :
    let b := localAllowance S D*slots k
    rawLossSum e r ≤ b ∧ rawPaddedWeight (localAllowance S D) e r = 2^(b-rawLossSum e r)*rawCoeff e r := by
  induction e with
  | leaf => simp [rawLossSum,rawCoeff,rawPaddedWeight]
  | @step d k p b G host lbl hu s ok T η hm hw next ih =>
    let A := localAllowance S D
    let B₀ := A*slots k
    let g := loss G.nE (shift S d) (width S d) 0
    let v := loss G.nE (shift S d) (width S d) (AppendixD4.level r.1.1.val)
    let c (j : Fin 64) := rawLossSum (next r.1 j) (r.2 j)
    let W := repr hf (AdjoinRoot.of _ (s.weight r.1.1 r.1.2.1) : B f l _)
    have hg : g ≤ A := (loss_inc ..).trans (inc_allow (by omega : d ≤ D) hm hw)
    have hv : v ≤ g := loss_mono ..
    have hc (j) : c j ≤ B₀ := (ih r.1 j (r.2 j) (by omega)).1
    have hs : (∑ j, c j) ≤ 64*B₀ := by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hc j)
    have he : (∑ j, (B₀-c j)) + ∑ j,c j = 64*B₀ := by
      rw [← Finset.sum_add_distrib]; simp [Nat.sub_add_cancel (hc _)]
    have hb : A*slots (k+1) = A+64*B₀ := by dsimp [slots,B₀]; ring
    change g + ∑ j,c j ≤ A*slots (k+1) ∧
      (2:IntJet f l)^(A-v)*canonQuotient hf s r.1*(∏ j,rawPaddedWeight A (next r.1 j) (r.2 j)) =
      2^(A*slots (k+1)-(g+∑ j,c j))*(W * ∏ j, rawCoeff (next r.1 j) (r.2 j))
    rw [hb]; refine ⟨by omega,?_⟩
    have hnode : (2:IntJet f l)^(A-v)*canonQuotient hf s r.1 = 2^(A-g)*W := by
      rw [show A-v = (A-g)+(g-v) by omega,pow_add,mul_assoc,canon_spec hf s r.1]
    have hi (j) : rawPaddedWeight A (next r.1 j) (r.2 j) = (2:IntJet f l)^(B₀-c j)*rawCoeff (next r.1 j) (r.2 j) :=
      (ih r.1 j (r.2 j) (by omega)).2
    simp only [hnode,hi,prod_mul_distrib]
    have hpow : (2:IntJet f l)^(A-g) * (∏ j, (2:IntJet f l)^(B₀-c j)) = 2^(A+64*B₀-(g+∑ j,c j)) := by
      rw [Finset.prod_pow_eq_pow_sum,←pow_add,exponent_budget hg he]
    linear_combination W*(∏ j, rawCoeff (next r.1 j) (r.2 j))*hpow

theorem solution {S D p l : ℕ} {f : ℤ[X]} {hf : f.Monic} {z : B f l p}
    (e : Expansion S f hf l 0 D p z) :
    let g := totalGuard S D; let q := g+p
    (∀ r, rawLossSum e r ≤ g) ∧
    (∑ r : e.Ranks, (2 : B f l q) ^ (g - rawLossSum e r) * red f l q (rawCoeff e r) * e.leaves q r) =
      2 ^ g * lift hf q z := by
  intro g q
  let b := localAllowance S D * slots D
  have hb : b ≤ g := Nat.mul_le_mul_left _ (slot_bound D)
  have h (r) := raw_factor (D:=D) e r (by omega)
  refine ⟨fun r => (h r).1.trans hb, ?_⟩
  refine Eq.trans (Finset.sum_congr rfl (fun r _ => ?_)) (cleared e)
  rw [(h r).2,map_mul,map_pow,map_ofNat,←mul_assoc,←pow_add]
  have hr : rawLossSum e r ≤ b := (h r).1
  change (2:B f l q)^(g-rawLossSum e r)*_*_ = 2^(g-b+(b-rawLossSum e r))*_*_
  rw [show g-b+(b-rawLossSum e r)=g-rawLossSum e r by omega]
