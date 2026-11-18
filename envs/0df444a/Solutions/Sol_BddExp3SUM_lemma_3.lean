-- Prove2me | solution 1 for BddExp3SUM.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T17:40:29.714148+00:00
-- url     : https://prove2.me/submissions/933099c2-165c-4ece-b5e2-1e67f22393c4

import Definitions.Def_BddExp3SUM_Profiles
import Definitions.Def_BddExp3SUM_Hash
import Definitions.Def_BddExp3SUM_Blocks


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BddExp3SUM
namespace ProfileProof

theorem cosetCount_le {M r : ℕ} (S : Finset (Grp M r)) (d : ℕ) (x : Grp M r) :
    cosetCount S d x ≤ S.card := by
  classical
  exact Finset.card_filter_le _ _

theorem profile_bound {M r n : ℕ} (S : Finset (Grp M r)) (hS : S.card ≤ n) :
    profileCount S ≤ (1+Nat.log 2 n)^Lcard M := by
  classical
  let tag : Grp M r → (Dvs M → Fin (Nat.log 2 n+1)) := fun x d =>
    ⟨Nat.log 2 (cosetCount S d.val x),by
      have h := Nat.log_mono_right (b:=2) (le_trans (cosetCount_le S d.val x) hS)
      omega⟩
  let repr : (Dvs M → Fin (Nat.log 2 n+1)) → (Dvs M → ℕ) :=
    fun t d => 2^(t d).val
  have he : S.image (profile S)=(S.image tag).image repr := by
    rw [Finset.image_image]
    rfl
  calc
    profileCount S=(S.image tag |>.image repr).card := congrArg Finset.card he
    _ ≤ (S.image tag).card := Finset.card_image_le
    _ ≤ Fintype.card (Dvs M → Fin (Nat.log 2 n+1)) := Finset.card_le_univ _
    _ = (1+Nat.log 2 n)^Lcard M := by simp [Lcard,Nat.add_comm]

theorem profile_partition {M r : ℕ} (S : Fin 3 → Finset (Grp M r))
    (x : Fin 3 → Grp M r) (hx : ∀ i,x i∈S i) :
    ∃! U : Fin 3 → Finset (Grp M r),IsProfileTriple S U ∧ ∀ i,x i∈U i := by
  classical
  let U : Fin 3 → Finset (Grp M r) :=
    fun i => (S i).filter fun y => profile (S i) y=profile (S i) (x i)
  refine ⟨U,⟨?_,?_⟩,?_⟩
  · intro i
    exact ⟨x i,hx i,rfl⟩
  · intro i
    exact Finset.mem_filter.mpr ⟨hx i,rfl⟩
  · rintro V ⟨hV,hxV⟩
    funext i
    obtain ⟨y,hy,he⟩ := hV i
    have hp : profile (S i) (x i)=profile (S i) y := by
      have hh := hxV i
      rw [he] at hh
      exact (Finset.mem_filter.mp hh).2
    rw [he]
    change (S i).filter (fun z => profile (S i) z=profile (S i) y)=
      (S i).filter (fun z => profile (S i) z=profile (S i) (x i))
    rw [hp]

theorem profile_count {M r n : ℕ} (S : Fin 3 → Finset (Grp M r)) (hS : ∀ i,(S i).card ≤ n) :
    (∀ i,profileCount (S i) ≤ (1+Nat.log 2 n)^Lcard M) ∧
    ∀ x : Fin 3 → Grp M r,(∀ i,x i∈S i) →
      ∃! U : Fin 3 → Finset (Grp M r),IsProfileTriple S U ∧ ∀ i,x i∈U i :=
  ⟨fun i => profile_bound (S i) (hS i),profile_partition S⟩

end ProfileProof
end BddExp3SUM


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BddExp3SUM
namespace CosetProof

theorem count_nonzero {M r : ℕ} (S : Finset (Grp M r)) (d : ℕ) (x : Grp M r) (hx : x∈S) :
    cosetCount S d x≠0 := by
  classical
  apply ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨x,Finset.mem_filter.mpr ⟨hx,by simp [H]⟩⟩

theorem dyadic_count_le {M r : ℕ} (S : Finset (Grp M r)) (d : ℕ) (x : Grp M r) (hx : x∈S) :
    sCount S d x ≤ cosetCount S d x := Nat.pow_log_le_self 2 (count_nonzero S d x hx)

theorem subinst_subset {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (i : Fin 3) : U i⊆S i := by
  classical
  obtain ⟨x,hx,he⟩ := h.isProfile i
  rw [he]
  exact Finset.filter_subset _ _

theorem sMin_le_count {M r n e : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (he : e∈Dvs M) (i : Fin 3) (x : Grp M r) (hx : x∈U i) :
    sMin S U e ≤ cosetCount (S i) e x := by
  classical
  obtain ⟨a,ha,hU⟩ := h.isProfile i
  have hxP : profile (S i) x=profile (S i) a := by
    have hx' := hx
    rw [hU] at hx'
    exact (Finset.mem_filter.mp hx').2
  have hbound : sVal S U i e ≤ cosetCount (S i) e x := by
    apply Finset.sup_le
    intro y hy
    have hyP : profile (S i) y=profile (S i) a := by
      rw [hU] at hy
      exact (Finset.mem_filter.mp hy).2
    have heq : sCount (S i) e y=sCount (S i) e x := congrFun (hyP.trans hxP.symm) ⟨e,he⟩
    rw [heq]
    exact dyadic_count_le (S i) e x (subinst_subset h i hx)
  apply le_trans _ hbound
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem fiber_image_lower_bound {α β : Type*} [DecidableEq β] (S U : Finset α) (f : α → β) (a : ℕ)
    (h : ∀ x∈U,a ≤ (S.filter fun y => f y=f x).card) :
    (U.image f).card*a ≤ S.card := by
  classical
  calc
    _ = ∑ y∈U.image f,a := by simp
    _ ≤ ∑ y∈U.image f,(S.filter fun x => f x=y).card := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact h x hx
    _ = (S.filter fun x => f x∈U.image f).card := Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ S.card := Finset.card_filter_le _ _

theorem represented_cosets_bound {M r n e : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (he : e∈Dvs M) (i : Fin 3) :
    cosetsRepresented (U i) e*sMin S U e ≤ n := by
  classical
  have hh := fiber_image_lower_bound (S i) (U i)
    (fun x => (QuotientAddGroup.mk x : Grp M r⧸H M r e)) (sMin S U e) (by
      intro x hx
      have hc := sMin_le_count h he i x hx
      convert hc using 1
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro y hy
      exact QuotientAddGroup.eq_iff_sub_mem)
  exact hh.trans (h.card_le i)

end CosetProof
end BddExp3SUM


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BddExp3SUM
namespace BlockProof
noncomputable section

def blockLabel {M r : ℕ} {T : Type*} (φ : Grp M r → T) (b : Finset (Grp M r)) : T :=
  if h : b.Nonempty then φ h.choose else φ 0

theorem block_count_bound {M r : ℕ} {T : Type*} (φ : Grp M r → T)
    (U : Finset (Grp M r)) (s : ℕ) (hs : 0<s) (parts : Finset (Finset (Grp M r)))
    (h : IsBlockCut φ U s parts) :
    (parts.card:ℝ) ≤ classCount U φ+(U.card:ℝ)/s := by
  classical
  have hl (b : Finset (Grp M r)) (hb : b∈parts) : blockLabel φ b∈U.image φ := by
    rw [blockLabel,dif_pos (h.nonempty b hb)]
    exact Finset.mem_image.mpr ⟨(h.nonempty b hb).choose,
      h.subset b hb (h.nonempty b hb).choose_spec,rfl⟩
  have hf (y : T) : parts.filter (fun b => blockLabel φ b=y)=
      parts.filter (fun b => ∀ x∈b,φ x=y) := by
    apply Finset.filter_congr
    intro b hb
    rw [blockLabel,dif_pos (h.nonempty b hb)]
    constructor
    · intro he x hx
      exact (h.same_label b hb x hx _ (h.nonempty b hb).choose_spec).trans he
    · intro he
      exact he _ (h.nonempty b hb).choose_spec
  have hb := Finset.card_eq_sum_card_fiberwise (s:=parts) (t:=U.image φ)
    (f:=blockLabel φ) hl
  simp_rw [hf,h.count] at hb
  have hu := Finset.card_eq_sum_card_fiberwise (s:=U) (t:=U.image φ)
    (f:=φ) (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  have hbR : (parts.card:ℝ)=∑ y∈U.image φ,
      (⌈((U.filter fun x => φ x=y).card:ℝ)/s⌉₊:ℝ) := by exact_mod_cast hb
  have huR : (U.card:ℝ)=∑ y∈U.image φ,((U.filter fun x => φ x=y).card:ℝ) := by
    exact_mod_cast hu
  rw [hbR]
  calc
    _ ≤ ∑ y∈U.image φ,(((U.filter fun x => φ x=y).card:ℝ)/s+1) := by
      apply Finset.sum_le_sum
      intro y hy
      exact (Nat.ceil_lt_add_one (by positivity)).le
    _=(U.card:ℝ)/s+(U.image φ).card := by
      rw [Finset.sum_add_distrib,←Finset.sum_div,←huR]
      simp
    _=classCount U φ+(U.card:ℝ)/s := by unfold classCount;ring

end
end BlockProof
end BddExp3SUM


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BddExp3SUM
namespace CertificateProof

theorem sigma_pos {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) : 0 < σ M n := by
  apply Nat.succ_le_iff.mp
  apply (Nat.one_le_floor_iff _).mpr
  apply Real.one_le_rpow
  · exact_mod_cast (show 1≤R M n by have := h.two_le;have := h.R_ge;omega)
  · norm_num [α,γ]

theorem subinst_nonempty {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (i : Fin 3) : (U i).Nonempty := by
  classical
  obtain ⟨x,hx,he⟩ := h.isProfile i
  rw [he]
  exact ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩

theorem class_bound_of_image_bound {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k+q) → Grp M r) (i : Fin 3)
    (hc : classCount (U i) (piHash h.p_dvd e u)*p^q ≤ cosetsRepresented (U i) e*e^(k+q)) :
    (classCount (U i) (piHash h.p_dvd e u):ℝ) < (M:ℝ)^2*n/σ M n := by
  classical
  let a := cosetsRepresented (U i) e
  let c := classCount (U i) (piHash h.p_dvd e u)
  have ha : 0<a := by
    obtain ⟨x,hx⟩ := subinst_nonempty h.toSubinst i
    exact Finset.card_pos.mpr (Finset.mem_image.mpr ⟨x,hx,rfl⟩ |> fun hh => ⟨_,hh⟩)
  have hσ : (0:ℝ)<σ M n := by exact_mod_cast sigma_pos h
  have heM : e≤M := Nat.le_of_dvd (by have := h.two_le;omega)
    (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp h.e_mem).1)
  have hpM : p≤M := Nat.le_of_dvd (by have := h.two_le;omega) h.p_dvd
  have he0 : 0<e := lt_of_lt_of_le (by decide : 0<2) (Finset.mem_filter.mp h.e_mem).2
  have hD : (0:ℝ)<(p:ℝ)^q := pow_pos (by exact_mod_cast h.p_prime.pos) _
  have hcR : (c:ℝ)*(p:ℝ)^q ≤ (a:ℝ)*(e:ℝ)^(k+q) := by exact_mod_cast hc
  have hcos : (a:ℝ)*(sMin S U e:ℝ) ≤ n := by
    exact_mod_cast CosetProof.represented_cosets_bound h.toSubinst h.e_mem i
  have hcert := (lt_div_iff₀ hσ).mp h.certificate
  have hlog : (R M n:ℝ) ≤ (p:ℝ)*(p:ℝ)^q := by
    have hh := (Nat.lt_pow_succ_log_self h.p_prime.one_lt (R M n)).le
    rw [←h.q_eq,pow_succ] at hh
    exact_mod_cast (by simpa only [Nat.mul_comm] using hh : R M n ≤ p*p^q)
  have hA : (c:ℝ)*(p:ℝ)^q*σ M n < (n:ℝ)*e*R M n := by
    calc
      _ ≤ (a:ℝ)*(e:ℝ)^(k+q)*σ M n := mul_le_mul_of_nonneg_right hcR hσ.le
      _ < (a:ℝ)*e*sMin S U e*R M n := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hcert (show (0:ℝ)<a by exact_mod_cast ha)
      _ = ((a:ℝ)*sMin S U e)*((e:ℝ)*R M n) := by ring
      _ ≤ (n:ℝ)*((e:ℝ)*R M n) := mul_le_mul_of_nonneg_right hcos (by positivity)
      _ = (n:ℝ)*e*R M n := by ring
  have hB : (n:ℝ)*e*R M n ≤ (M:ℝ)^2*n*(p:ℝ)^q := by
    calc
      _ ≤ (n:ℝ)*e*((p:ℝ)*(p:ℝ)^q) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = ((n:ℝ)*(p:ℝ)^q)*((e:ℝ)*p) := by ring
      _ ≤ ((n:ℝ)*(p:ℝ)^q)*((M:ℝ)*M) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast Nat.mul_le_mul heM hpM
      _ = (M:ℝ)^2*n*(p:ℝ)^q := by ring
  apply (lt_div_iff₀ hσ).mpr
  apply (mul_lt_mul_iff_right₀ hD).mp
  simpa only [c,mul_assoc,mul_left_comm,mul_comm] using hA.trans_le hB

theorem lemma_3_of_image_bound {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k+q) → Grp M r) (i : Fin 3)
    (hc : classCount (U i) (piHash h.p_dvd e u)*p^q ≤ cosetsRepresented (U i) e*e^(k+q)) :
    (classCount (U i) (piHash h.p_dvd e u):ℝ) < (M:ℝ)^2*n/σ M n ∧
    ∀ parts : Finset (Finset (Grp M r)),IsBlockCut (piHash h.p_dvd e u) (U i) (σ M n) parts →
      (parts.card:ℝ) ≤ ((M:ℝ)^2+1)*n/σ M n := by
  have hclass := class_bound_of_image_bound h u i hc
  refine ⟨hclass,fun parts hparts => ?_⟩
  have hb := BlockProof.block_count_bound _ _ _ (sigma_pos h) parts hparts
  have hcard : (U i).card≤n := (Finset.card_le_card (CosetProof.subinst_subset h.toSubinst i)).trans (h.card_le i)
  have hcardR : (U i).card/(σ M n:ℝ) ≤ (n:ℝ)/σ M n :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
  apply hb.trans
  calc
    _ ≤ (M:ℝ)^2*n/σ M n+(n:ℝ)/σ M n := add_le_add hclass.le hcardR
    _ = ((M:ℝ)^2+1)*n/σ M n := by ring

end CertificateProof
end BddExp3SUM


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
set_option maxHeartbeats 1500000
noncomputable section
namespace BddExp3SUM
namespace ClassProof
open EmbeddingProof

lemma quotient_divisors {M e p : ℕ} (hM:0<M) (he:e∣M) (hp:p∣e) (hp0:0<p) :
    e/p∣M/p ∧ (M/p)/(e/p)=M/e := by
  have he0:0<e := Nat.pos_of_dvd_of_pos he hM
  have hep:0<e/p := Nat.div_pos (Nat.le_of_dvd he0 hp) hp0
  have hh:(M/e)*(e/p)*p=M := by
    rw [Nat.mul_assoc,Nat.div_mul_cancel hp,Nat.div_mul_cancel he]
  have hratio:(M/e)*(e/p)=M/p := by
    calc
      _ = ((M/e)*(e/p)*p)/p := (Nat.mul_div_cancel _ hp0).symm
      _ = M/p := congrArg (fun z:ℕ=>z/p) hh
  refine ⟨⟨M/e,by rw [← hratio,Nat.mul_comm]⟩,?_⟩
  rw [← hratio,Nat.mul_div_cancel _ hep]

lemma killed_mem_scaled_range {M e : ℕ} (hM:0<M) (he:e∣M) (a : ZMod M) (ha:e • a=0) :
    ∃b:ZMod e,scaledHom he b=a := by
  letI : NeZero M:=⟨ne_of_gt hM⟩
  have he0:0<e := Nat.pos_of_dvd_of_pos he hM
  have hn:((e*a.val:ℕ):ZMod M)=0 := by
    rw [Nat.cast_mul,ZMod.natCast_zmod_val]
    simpa only [nsmul_eq_mul] using ha
  have hd:M∣e*a.val := (ZMod.natCast_eq_zero_iff _ _).mp hn
  have hdm:M/e∣a.val := by
    have hd':e*(M/e)∣e*a.val := by simpa only [Nat.mul_div_cancel' he] using hd
    exact (Nat.mul_dvd_mul_iff_left he0).mp hd'
  refine ⟨(a.val/(M/e):ℕ),?_⟩
  rw [scaledHom_nat, Nat.mul_div_cancel' hdm,ZMod.natCast_zmod_val]

lemma reduced_killed_mem_scaled_range {M e p : ℕ} (hM:0<M) (he:e∣M) (hp:p∣e) (hp0:0<p)
    (a : ZMod M) (ha:e • a=0) :
    ∃b:ZMod (e/p),scaledHom (quotient_divisors hM he hp hp0).1 b=
      reduceHom (hp.trans he) a := by
  obtain ⟨b,rfl⟩:=killed_mem_scaled_range hM he a ha
  refine ⟨(b.val:ℕ),?_⟩
  rw [scaledHom_nat,(quotient_divisors hM he hp hp0).2,scaledHom_val hM he]
  change ((M/e*b.val:ℕ):ZMod (M/p))=
    (ZMod.castHom (Nat.div_dvd_of_dvd (hp.trans he)) (ZMod (M/p))) ((M/e*b.val:ℕ):ZMod M)
  exact (map_natCast _ _).symm

lemma row_killed_of_mem_H {M r e : ℕ} (a x : Grp M r) (hx:x∈H M r e) :
    e • rowHom a x=0 := by
  rw [← map_nsmul]
  simpa only [map_zero] using congrArg (rowHom a) hx

/-- On a fixed original H_e-coset the full/reduced row values have at most
 e^k (e/p)^q possibilities. This holds for every choice of rows. -/
theorem classCount_bound {M r e p k q : ℕ} (hM:0<M) (he:e∣M) (hp:p∣e) (hp0:0<p)
    (U : Finset (Grp M r)) (u : Fin (k+q)→Grp M r) :
    classCount U (piHash (hp.trans he) e u) ≤ cosetsRepresented U e*e^k*(e/p)^q := by
  classical
  letI : DecidableEq (PiTarget M r e k q p):=fun a b=>Classical.propDecidable (a=b)
  have he0:0<e := Nat.pos_of_dvd_of_pos he hM
  have hep:0<e/p := Nat.div_pos (Nat.le_of_dvd he0 hp) hp0
  letI : NeZero e:=⟨ne_of_gt he0⟩
  letI : NeZero (e/p):=⟨ne_of_gt hep⟩
  let C:=U.image (fun x=>(QuotientAddGroup.mk x:Grp M r⧸H M r e))
  let rep: C→Grp M r := fun c=>(Finset.mem_image.mp c.property).choose
  have hrep:∀c:C,rep c∈U ∧ (QuotientAddGroup.mk (rep c):Grp M r⧸H M r e)=c := by
    intro c
    exact (Finset.mem_image.mp c.property).choose_spec
  let lab:C×(Fin k→ZMod e)×(Fin q→ZMod (e/p))→PiTarget M r e k q p := fun z=>
    (z.1.val,(fun j=>rowHom (u (Fin.castAdd q j)) (rep z.1)+scaledHom he (z.2.1 j)),
      fun j=>reduceHom (hp.trans he) (rowHom (u (Fin.natAdd k j)) (rep z.1))+
        scaledHom (quotient_divisors hM he hp hp0).1 (z.2.2 j))
  have hsub:U.image (piHash (hp.trans he) e u)⊆Finset.univ.image lab := by
    intro y hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    let c:C:=⟨QuotientAddGroup.mk x,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
    have hcos:(QuotientAddGroup.mk x:Grp M r⧸H M r e)=QuotientAddGroup.mk (rep c) :=
      (hrep c).2.symm
    have hxH:x-rep c∈H M r e := QuotientAddGroup.eq_iff_sub_mem.mp hcos
    have hfull:∀j:Fin k,∃b:ZMod e,scaledHom he b=rowHom (u (Fin.castAdd q j)) (x-rep c) :=
      fun j=>killed_mem_scaled_range hM he _ (row_killed_of_mem_H _ _ hxH)
    have hred:∀j:Fin q,∃b:ZMod (e/p),scaledHom (quotient_divisors hM he hp hp0).1 b=
        reduceHom (hp.trans he) (rowHom (u (Fin.natAdd k j)) (x-rep c)) :=
      fun j=>reduced_killed_mem_scaled_range hM he hp hp0 _ (row_killed_of_mem_H _ _ hxH)
    choose a ha using hfull
    choose b hb using hred
    apply Finset.mem_image.mpr
    refine ⟨(c,a,b),Finset.mem_univ _,?_⟩
    refine Prod.ext ?_ ?_
    · rfl
    refine Prod.ext ?_ ?_
    · funext j
      change rowHom (u (Fin.castAdd q j)) (rep c)+scaledHom he (a j)=_
      rw [ha,map_sub]
      abel
    · funext j
      change reduceHom (hp.trans he) (rowHom (u (Fin.natAdd k j)) (rep c))+
        scaledHom (quotient_divisors hM he hp hp0).1 (b j)=_
      rw [hb,map_sub,map_sub]
      abel
  have hh:(U.image (piHash (hp.trans he) e u)).card ≤
      Fintype.card (C×(Fin k→ZMod e)×(Fin q→ZMod (e/p))) :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_image_le (s:=Finset.univ) (f:=lab)).trans_eq Finset.card_univ)
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card,
    Fintype.card_coe,cosetsRepresented,classCount,C,Nat.mul_assoc] using hh

theorem classCount_mul_prime_pow_le {M r n k q e p : ℕ} {S U : Fin 3→Finset (Grp M r)}
    (h:Cert M r n S U k q e p) (u : Fin (k+q)→Grp M r) (i : Fin 3) :
    classCount (U i) (piHash h.p_dvd e u)*p^q ≤ cosetsRepresented (U i) e*e^(k+q) := by
  have he:e∣M := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp h.e_mem).1
  have hM:0<M := lt_of_lt_of_le (by decide:0<2) h.two_le
  have hc:=classCount_bound hM he h.p_dvd_e h.p_prime.pos (U i) u
  have hh:=Nat.mul_le_mul_right (p^q) hc
  have hp:(e/p)*p=e := Nat.div_mul_cancel h.p_dvd_e
  calc
    _ ≤ (cosetsRepresented (U i) e*e^k*(e/p)^q)*p^q := hh
    _ = cosetsRepresented (U i) e*e^(k+q) := by rw [Nat.mul_assoc _ ((e/p)^q),← mul_pow,hp,pow_add];ring

end ClassProof
end BddExp3SUM


set_option autoImplicit false

namespace BddExp3SUM
namespace BlockProof

theorem lemma_3 {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k+q) → Grp M r) (i : Fin 3) :
    (classCount (U i) (piHash h.p_dvd e u):ℝ) < (M:ℝ)^2*n/σ M n ∧
    ∀ parts : Finset (Finset (Grp M r)),IsBlockCut (piHash h.p_dvd e u) (U i) (σ M n) parts →
      (parts.card:ℝ) ≤ ((M:ℝ)^2+1)*n/σ M n :=
  CertificateProof.lemma_3_of_image_bound h u i (ClassProof.classCount_mul_prime_pow_le h u i)

end BlockProof
end BddExp3SUM

open BddExp3SUM

theorem solution {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k + q) → Grp M r) (i : Fin 3) :
    (classCount (U i) (piHash h.p_dvd e u) : ℝ) < (M : ℝ) ^ 2 * n / σ M n ∧
    ∀ parts : Finset (Finset (Grp M r)), IsBlockCut (piHash h.p_dvd e u) (U i) (σ M n) parts →
      (parts.card : ℝ) ≤ ((M : ℝ) ^ 2 + 1) * n / σ M n  := BddExp3SUM.BlockProof.lemma_3 h u i
