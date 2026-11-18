-- Prove2me | solution 1 for BddExp3SUM.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T17:31:21.255496+00:00
-- url     : https://prove2.me/submissions/34a78fc5-8f08-4c9c-a6be-295b3c33b768

import Definitions.Def_BddExp3SUM_Profiles
import Definitions.Def_BddExp3SUM_Hash


set_option autoImplicit false
namespace BddExp3SUM

def Instance.embed {M : ℕ} (x : Instance M) (a : Fin x.r → ℕ) : Grp M x.r :=
  fun j => ((M / x.m j * a j : ℕ) : ZMod M)

namespace EmbeddingProof

def intScale (M m : ℕ) : ℤ →+ ZMod M where
  toFun z := ((M/m : ℕ) : ZMod M)*(z : ZMod M)
  map_zero' := by simp
  map_add' a b := by simp [mul_add]

lemma intScale_period {M m : ℕ} (hm : m∣M) : intScale M m (m:ℤ)=0 := by
  simp only [intScale,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_natCast]
  rw [←Nat.cast_mul,Nat.div_mul_cancel hm,ZMod.natCast_self]

def scaledHom {M m : ℕ} (hm : m∣M) : ZMod m →+ ZMod M :=
  ZMod.lift m ⟨intScale M m,intScale_period hm⟩

lemma scaledHom_nat {M m : ℕ} (hm : m∣M) (a : ℕ) :
    scaledHom hm (a:ZMod m)=((M/m*a:ℕ):ZMod M) := by
  have h := ZMod.lift_coe m (⟨intScale M m,intScale_period hm⟩) (a:ℤ)
  simpa only [scaledHom,intScale,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Int.cast_natCast,Nat.cast_mul] using h

lemma scaledHom_val {M m : ℕ} (hM : 0 < M) (hm : m∣M) (a : ZMod m) :
    scaledHom hm a=((M/m*a.val:ℕ):ZMod M) := by
  letI : NeZero m := ⟨ne_of_gt (Nat.pos_of_dvd_of_pos hm hM)⟩
  simpa only [ZMod.natCast_zmod_val] using scaledHom_nat hm a.val

theorem scaledHom_injective {M m : ℕ} (hM : 0 < M) (hm : m∣M) :
    Function.Injective (scaledHom hm) := by
  letI : NeZero M := ⟨hM.ne'⟩
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hM
  letI : NeZero m := ⟨hm0.ne'⟩
  have hs : 0 < M/m := Nat.div_pos (Nat.le_of_dvd hM hm) hm0
  have he : M/m*m=M := Nat.div_mul_cancel hm
  intro a b hab
  rw [scaledHom_val hM hm,scaledHom_val hM hm] at hab
  have ha : M/m*a.val<M := by nlinarith [a.val_lt]
  have hb : M/m*b.val<M := by nlinarith [b.val_lt]
  have hv := congrArg ZMod.val hab
  rw [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] at hv
  apply ZMod.val_injective m
  exact Nat.eq_of_mul_eq_mul_left hs hv

theorem scale_zero_iff {M m a : ℕ} (hM : 0 < M) (hm : m∣M) :
    ((M/m*a:ℕ):ZMod M)=0 ↔ a%m=0 := by
  rw [ZMod.natCast_eq_zero_iff]
  have hs : 0 < M/m := Nat.div_pos (Nat.le_of_dvd hM hm) (Nat.pos_of_dvd_of_pos hm hM)
  conv_lhs => lhs; rw [← Nat.div_mul_cancel hm]
  rw [Nat.mul_dvd_mul_iff_left hs,Nat.dvd_iff_mod_eq_zero]

theorem section_2_embedding (M : ℕ) (hM : 2≤M) :
    (∀ m : ℕ, m∣M → ∃ f : ZMod m →+ ZMod M, Function.Injective f ∧
      ∀ y : ZMod m,f y=((M/m*y.val:ℕ):ZMod M)) ∧
    ∀ x : Instance M,
      (∀ a a' : Fin x.r → ℕ,(∀ j,a j < x.m j) → (∀ j,a' j < x.m j) →
        x.embed a=x.embed a' → a=a') ∧
      ∀ a₁ a₂ a₃ : Fin x.r → ℕ,
        x.ZeroSum a₁ a₂ a₃ ↔ x.embed a₁+x.embed a₂+x.embed a₃=0 := by
  have hM0 : 0 < M := by omega
  constructor
  · intro m hm
    exact ⟨scaledHom hm,scaledHom_injective hM0 hm,scaledHom_val hM0 hm⟩
  · intro x
    constructor
    · intro a b ha hb hab
      funext j
      have hj := congrFun hab j
      change ((M/x.m j*a j:ℕ):ZMod M)=((M/x.m j*b j:ℕ):ZMod M) at hj
      rw [←scaledHom_nat (x.m_dvd j),←scaledHom_nat (x.m_dvd j)] at hj
      have he := scaledHom_injective hM0 (x.m_dvd j) hj
      have hv := congrArg ZMod.val he
      simpa only [ZMod.val_natCast_of_lt (ha j),ZMod.val_natCast_of_lt (hb j)] using hv
    · intro a b c
      change (∀ j,(a j+b j+c j)%x.m j=0) ↔ _
      constructor
      · intro hz
        funext j
        have hj := (scale_zero_iff hM0 (x.m_dvd j)).mpr (hz j)
        simpa only [Instance.embed,Pi.add_apply,Pi.zero_apply,Nat.mul_add,Nat.cast_add] using hj
      · intro hz j
        apply (scale_zero_iff hM0 (x.m_dvd j)).mp
        have hj := congrFun hz j
        simpa only [Instance.embed,Pi.add_apply,Pi.zero_apply,Nat.mul_add,Nat.cast_add] using hj

end EmbeddingProof

end BddExp3SUM


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace BddExp3SUM
namespace MiddleProof
open EmbeddingProof
noncomputable section

lemma reduce_zero_multiple {M p : ℕ} [NeZero M] (hpM : p∣M) (a : ZMod M)
    (ha : reduceHom hpM a=0) : ∃ b : ZMod M,a=((M/p:ℕ):ZMod M)*b := by
  have he : reduceHom hpM a=(a.val:ZMod (M/p)) := by
    rw [←ZMod.natCast_zmod_val a]
    simp [reduceHom]
  have hd : M/p∣a.val := (ZMod.natCast_eq_zero_iff _ _).mp (he.symm.trans ha)
  refine ⟨(a.val/(M/p):ℕ),?_⟩
  rw [←Nat.cast_mul,Nat.mul_div_cancel' hd,ZMod.natCast_zmod_val]

theorem kernel_mem_B {M r e k q p : ℕ} [NeZero M] (hpM : p∣M)
    (u : Fin (k+q) → Grp M r) (x : Grp M r) (hx : piHash hpM e u x=0) :
    KHash e u x∈B M r e k q p := by
  have h0 := congrArg Prod.fst hx
  have h1 := congrArg (fun y : PiTarget M r e k q p => y.2.1) hx
  have h2 := congrArg (fun y : PiTarget M r e k q p => y.2.2) hx
  refine ⟨h0,fun j => congrFun h1 j,fun j => ?_⟩
  exact reduce_zero_multiple hpM _ (congrFun h2 j)

def bLift {M r e k q p : ℕ} (hpM : p∣M) :
    (Fin q → ZMod p) →+ KTarget M r e k q where
  toFun v := (0,Fin.append (fun _ : Fin k => 0) (fun j => scaledHom hpM (v j)))
  map_zero' := by
    apply Prod.ext (by rfl)
    change Fin.append (fun _ : Fin k => 0) (fun _ : Fin q => scaledHom hpM 0)=(0 : Fin (k+q) → ZMod M)
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_add' v w := by
    apply Prod.ext (by simp)
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

@[simp] lemma bLift_left {M r e k q p : ℕ} (hpM : p∣M) (v : Fin q → ZMod p) (i : Fin k) :
    (bLift (r:=r) (e:=e) (k:=k) hpM v).2 (Fin.castAdd q i)=0 := by simp [bLift]

@[simp] lemma bLift_right {M r e k q p : ℕ} (hpM : p∣M) (v : Fin q → ZMod p) (i : Fin q) :
    (bLift (r:=r) (e:=e) (k:=k) hpM v).2 (Fin.natAdd k i)=scaledHom hpM (v i) := by simp [bLift]

theorem bLift_mem {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) (v : Fin q → ZMod p) :
    bLift (r:=r) (e:=e) (k:=k) hpM v∈B M r e k q p := by
  refine ⟨rfl,fun j => bLift_left hpM v j,fun j => ?_⟩
  refine ⟨((v j).val:ℕ),?_⟩
  rw [bLift_right,scaledHom_val (Nat.pos_of_ne_zero (NeZero.ne M)) hpM,Nat.cast_mul]

theorem bLift_injective {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) :
    Function.Injective (bLift (r:=r) (e:=e) (k:=k) (q:=q) hpM) := by
  intro v w h
  funext j
  apply scaledHom_injective (Nat.pos_of_ne_zero (NeZero.ne M)) hpM
  have hj := congrArg (fun y : KTarget M r e k q => y.2 (Fin.natAdd k j)) h
  simpa only [bLift_right] using hj

theorem bLift_surjective {M r e k q p : ℕ} [NeZero M] (hpM : p∣M)
    (w : KTarget M r e k q) (hw : w∈B M r e k q p) :
    ∃ v : Fin q → ZMod p,bLift hpM v=w := by
  choose a ha using hw.2.2
  let v : Fin q → ZMod p := fun j => (a j).val
  refine ⟨v,?_⟩
  apply Prod.ext hw.1.symm
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [bLift_left,hw.2.1]
  · rw [bLift_right,ha i]
    change scaledHom hpM ((a i).val:ZMod p)=_
    rw [scaledHom_nat,Nat.cast_mul,ZMod.natCast_zmod_val]

def bMap {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) :
    (Fin q → ZMod p) →+ B M r e k q p where
  toFun v := ⟨bLift hpM v,bLift_mem hpM v⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' v w := Subtype.ext (map_add _ v w)

def bEquiv {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) :
    (Fin q → ZMod p) ≃+ B M r e k q p :=
  AddEquiv.ofBijective (bMap hpM) ⟨
    fun v w h => bLift_injective hpM (congrArg Subtype.val h),
    fun w => by
      obtain ⟨v,hv⟩ := bLift_surjective hpM w.val w.property
      exact ⟨v,Subtype.ext hv⟩⟩

theorem card_B {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p∣M) :
    Nat.card (B M r e k q p)=p^q := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr (bEquiv (r:=r) (e:=e) (k:=k) (q:=q) hpM).symm.toEquiv]
  simp [Nat.card_eq_fintype_card]

def supportB (M r e k q p : ℕ) (s : Finset (Fin q)) : AddSubgroup (KTarget M r e k q) :=
  B M r e k q p ⊓
    { carrier := {w | ∀ j : Fin q,j∉s → w.2 (Fin.natAdd k j)=0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun ha hb j hj => by simp [ha j hj,hb j hj]
      neg_mem' := fun ha j hj => by simp [ha j hj] }

def extendHom {q p : ℕ} (s : Finset (Fin q)) : (s → ZMod p) →+ (Fin q → ZMod p) where
  toFun v j := if h : j∈s then v ⟨j,h⟩ else 0
  map_zero' := by funext j;split_ifs <;> rfl
  map_add' v w := by funext j;split_ifs with h <;> simp [h]

theorem extendHom_injective {q p : ℕ} (s : Finset (Fin q)) : Function.Injective (extendHom (p:=p) s) := by
  intro v w he
  funext j
  have hj := congrFun he j.val
  simpa only [extendHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,dif_pos j.property] using hj

def supportMap {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) (s : Finset (Fin q)) :
    (s → ZMod p) →+ supportB M r e k q p s where
  toFun v := ⟨bLift hpM (extendHom s v),bLift_mem hpM _,fun j hj => by
    rw [bLift_right]
    simp only [extendHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,dif_neg hj,map_zero]⟩
  map_zero' := by apply Subtype.ext;change bLift hpM (extendHom s 0)=0;rw [map_zero,map_zero]
  map_add' v w := by
    apply Subtype.ext
    change bLift hpM (extendHom s (v+w))=bLift hpM (extendHom s v)+bLift hpM (extendHom s w)
    rw [map_add,map_add]

theorem supportMap_bijective {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) (s : Finset (Fin q)) :
    Function.Bijective (supportMap (r:=r) (e:=e) (k:=k) hpM s) := by
  constructor
  · intro v w he
    exact extendHom_injective s (bLift_injective hpM (congrArg Subtype.val he))
  · intro w
    obtain ⟨v,hv⟩ := bLift_surjective hpM w.val w.property.1
    let t : s → ZMod p := fun j => v j.val
    have he : extendHom s t=v := by
      funext j
      by_cases hj : j∈s
      · simp only [extendHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,dif_pos hj,t]
      · have hz : scaledHom hpM (v j)=0 := by
          rw [←bLift_right (r:=r) (e:=e) (k:=k),hv]
          exact w.property.2 j hj
        have hv0 : v j=0 := scaledHom_injective (Nat.pos_of_ne_zero (NeZero.ne M)) hpM
          (hz.trans (map_zero _).symm)
        simp only [extendHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,dif_neg hj,hv0]
    refine ⟨t,Subtype.ext ?_⟩
    change bLift hpM (extendHom s t)=w.val
    rw [he,hv]

def supportEquiv {M r e k q p : ℕ} [NeZero M] (hpM : p∣M) (s : Finset (Fin q)) :
    (s → ZMod p) ≃+ supportB M r e k q p s :=
  AddEquiv.ofBijective (supportMap hpM s) (supportMap_bijective hpM s)

theorem card_supportB {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p∣M)
    (s : Finset (Fin q)) : Nat.card (supportB M r e k q p s)=p^s.card := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr (supportEquiv (r:=r) (e:=e) (k:=k) hpM s).symm.toEquiv]
  simp [Nat.card_eq_fintype_card]

def firstHalf (q : ℕ) : Finset (Fin q) := Finset.univ.filter fun j => j.val<(q+1)/2

lemma firstHalf_card (q : ℕ) : (firstHalf q).card=(q+1)/2 := by
  rw [firstHalf,Fin.card_filter_val_lt,min_eq_right (by omega)]

lemma secondHalf_card (q : ℕ) : ((firstHalf q)ᶜ).card=q/2 := by
  rw [Finset.card_compl,Fintype.card_fin,firstHalf_card]
  omega

lemma B₁_eq_supportB (M r e k q p : ℕ) : B₁ M r e k q p=supportB M r e k q p (firstHalf q) := by
  ext w
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [firstHalf,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]

lemma B₂_eq_supportB (M r e k q p : ℕ) : B₂ M r e k q p=supportB M r e k q p (firstHalf q)ᶜ := by
  ext w
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [firstHalf,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and,not_not]

theorem card_B₁ {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p∣M) :
    Nat.card (B₁ M r e k q p)=p^((q+1)/2) := by
  rw [B₁_eq_supportB,card_supportB hp hpM,firstHalf_card]

theorem card_B₂ {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p∣M) :
    Nat.card (B₂ M r e k q p)=p^(q/2) := by
  rw [B₂_eq_supportB,card_supportB hp hpM,secondHalf_card]

theorem split_unique {M r e k q p : ℕ} [NeZero M] (hpM : p∣M)
    (w : KTarget M r e k q) (hw : w∈B M r e k q p) :
    ∃! v : (B₁ M r e k q p)×(B₂ M r e k q p),(v.1 : KTarget M r e k q)+v.2=w := by
  classical
  obtain ⟨v,hv⟩ := bLift_surjective hpM w hw
  let v1 : Fin q → ZMod p := fun j => if j∈firstHalf q then v j else 0
  let v2 : Fin q → ZMod p := fun j => if j∈firstHalf q then 0 else v j
  have h1 : bLift (r:=r) (e:=e) (k:=k) hpM v1∈B₁ M r e k q p := by
    refine ⟨bLift_mem hpM v1,fun j hj => ?_⟩
    rw [bLift_right]
    simp [v1,firstHalf,show ¬j.val<(q+1)/2 by omega]
  have h2 : bLift (r:=r) (e:=e) (k:=k) hpM v2∈B₂ M r e k q p := by
    refine ⟨bLift_mem hpM v2,fun j hj => ?_⟩
    rw [bLift_right]
    simp [v2,firstHalf,hj]
  have he : bLift (r:=r) (e:=e) (k:=k) hpM v1+bLift hpM v2=w := by
    rw [←map_add,hv.symm]
    congr 1
    funext j
    dsimp [v1,v2]
    split_ifs <;> simp
  refine ⟨(⟨bLift hpM v1,h1⟩,⟨bLift hpM v2,h2⟩),he,?_⟩
  intro z hz
  have hz1 : (z.1:KTarget M r e k q)=bLift hpM v1 := by
    apply Prod.ext
    · exact z.1.property.1.1
    · funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · exact (z.1.property.1.2.1 i).trans (bLift_left hpM v1 i).symm
      · by_cases hi : i.val<(q+1)/2
        · have hh := congrArg (fun y : KTarget M r e k q => y.2 (Fin.natAdd k i)) hz
          have hh' := congrArg (fun y : KTarget M r e k q => y.2 (Fin.natAdd k i)) he
          have hz2 := z.2.property.2 i hi
          have hv2 : (bLift (r:=r) (e:=e) (k:=k) hpM v2).2 (Fin.natAdd k i)=0 := by
            rw [bLift_right];simp [v2,firstHalf,hi]
          change (z.1:KTarget M r e k q).2 (Fin.natAdd k i)+(z.2:KTarget M r e k q).2 (Fin.natAdd k i)=_ at hh
          change (bLift hpM v1).2 (Fin.natAdd k i)+(bLift hpM v2).2 (Fin.natAdd k i)=_ at hh'
          simpa only [hz2,hv2,add_zero] using hh.trans hh'.symm
        · have hz0 := z.1.property.2 i (by omega)
          have hv0 : (bLift (r:=r) (e:=e) (k:=k) hpM v1).2 (Fin.natAdd k i)=0 := by
            rw [bLift_right];simp [v1,firstHalf,hi]
          exact hz0.trans hv0.symm
  have hz2 : (z.2:KTarget M r e k q)=bLift hpM v2 := by
    apply add_left_cancel (a:=bLift (r:=r) (e:=e) (k:=k) hpM v1)
    calc
      bLift hpM v1+(z.2:KTarget M r e k q)=(z.1:KTarget M r e k q)+(z.2:KTarget M r e k q) := by rw [hz1]
      _=w := hz
      _=bLift hpM v1+bLift hpM v2 := he.symm
  exact Prod.ext (Subtype.ext hz1) (Subtype.ext hz2)

theorem eq_6 {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p∣M)
    (u : Fin (k+q) → Grp M r) :
    (∀ x : Grp M r,piHash hpM e u x=0 → KHash e u x∈B M r e k q p) ∧
    Nonempty (B M r e k q p ≃+ (Fin q → ZMod p)) ∧
    Nat.card (B M r e k q p)=p^q ∧
    Nat.card (B₁ M r e k q p)=p^((q+1)/2) ∧
    Nat.card (B₂ M r e k q p)=p^(q/2) ∧
    ∀ w∈B M r e k q p,∃! v : (B₁ M r e k q p)×(B₂ M r e k q p),
      (v.1:KTarget M r e k q)+v.2=w := by
  exact ⟨kernel_mem_B hpM u,⟨(bEquiv hpM).symm⟩,card_B hp hpM,
    card_B₁ hp hpM,card_B₂ hp hpM,split_unique hpM⟩

end
end MiddleProof
end BddExp3SUM

open BddExp3SUM

theorem solution {M r e k q p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    (u : Fin (k + q) → Grp M r) :
    (∀ x : Grp M r, piHash hpM e u x = 0 → KHash e u x ∈ B M r e k q p) ∧
    Nonempty (B M r e k q p ≃+ (Fin q → ZMod p)) ∧
    Nat.card (B M r e k q p) = p ^ q ∧
    Nat.card (B₁ M r e k q p) = p ^ ((q + 1) / 2) ∧
    Nat.card (B₂ M r e k q p) = p ^ (q / 2) ∧
    ∀ w ∈ B M r e k q p, ∃! v : (B₁ M r e k q p) × (B₂ M r e k q p), (v.1 : KTarget M r e k q) + v.2 = w  := BddExp3SUM.MiddleProof.eq_6 hp hpM u
