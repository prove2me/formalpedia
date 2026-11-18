-- Prove2me | solution 1 for BirthdayEntropy.Soundness.fixed_flattening_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:29:15.558721+00:00
-- url     : https://prove2.me/submissions/7d44037a-7825-4beb-9908-4e03468faf01

import Definitions.Def_BirthdayEntropy_Soundness_Biclique
import Theorems.Thm_BirthdayEntropy_Soundness_pair_avoidance
import Theorems.Thm_BirthdayEntropy_Soundness_binomial_product_deficit
import Theorems.Thm_BirthdayEntropy_Soundness_support_deficit_cell_bound

noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness
namespace BirthdayEntropy.Soundness.Fixed

lemma card_signed {n ℓ : ℕ} (v : Vertex n ℓ) : (signed v).card = ℓ := by
  have hi : Function.Injective (fun i : v.1.val => (i.val,v.2 i)) := by
    intro a b h
    exact Subtype.ext (congrArg Prod.fst h)
  simp [signed,Finset.card_image_of_injective _ hi,v.1.property]

lemma support_signed {n ℓ : ℕ} (v : Vertex n ℓ) : support (signed v) = v.1.val := by
  ext i
  simp [support,signed]

lemma signed_inj {n ℓ : ℕ} : Function.Injective (@signed n ℓ) := by
  intro v w h
  have hS : v.1 = w.1 := Subtype.ext (by simpa only [support_signed] using congrArg support h)
  cases v with
  | mk S a =>
    cases w with
    | mk T b =>
      dsimp only at hS
      subst T
      congr 1
      funext i
      have hm : (i.val,a i) ∈ signed (⟨S,a⟩ : Vertex n ℓ) := by
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rw [h] at hm
      obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hm
      have hji : j = i := Subtype.ext (congrArg Prod.fst heq)
      subst j
      exact (congrArg Prod.snd heq).symm

def allowed {n ℓ : ℕ} (A : Finset (Signed n)) : Finset (Vertex n ℓ) :=
  Finset.univ.filter (fun v => signed v ⊆ A)

lemma allowed_card {n ℓ : ℕ} (A : Finset (Signed n)) :
    (allowed (ℓ := ℓ) A).card ≤ Nat.choose A.card ℓ := by
  have hmap : (allowed (ℓ := ℓ) A).image signed ⊆ A.powersetCard ℓ := by
    intro S hS
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp hv).2,card_signed v⟩
  have h := Finset.card_le_card hmap
  simpa [Finset.card_image_of_injective _ signed_inj] using h

lemma flatten_contains_left {n ℓ r : ℕ} (X : Tuple n ℓ r) (i : Fin r) :
    signed (X.1 i) ⊆ (flatten X).1 := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩

lemma flatten_contains_right {n ℓ r : ℕ} (X : Tuple n ℓ r) (j : Fin r) :
    signed (X.2 j) ⊆ (flatten X).2 := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hp⟩

lemma accepted_cell_count {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (r : ℕ) (F : Flattening n) :
    (acceptedCell φ H r F).card ≤ ((allowed (ℓ := ℓ) F.1).card)^r * ((allowed (ℓ := ℓ) F.2).card)^r := by
  have hsub : acceptedCell φ H r F ⊆
      (Fintype.piFinset (fun _ : Fin r => allowed F.1)) ×ˢ (Fintype.piFinset (fun _ : Fin r => allowed F.2)) := by
    intro X hX
    have hh : X ∈ accepted φ H r ∧ flatten X = F := by simpa only [acceptedCell,cell,Finset.mem_filter] using hX
    have hF := hh.2
    apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      simp only [allowed,Finset.mem_filter,Finset.mem_univ,true_and]
      simpa only [hF] using flatten_contains_left X i
    · apply Fintype.mem_piFinset.mpr
      intro j
      simp only [allowed,Finset.mem_filter,Finset.mem_univ,true_and]
      simpa only [hF] using flatten_contains_right X j
  simpa using Finset.card_le_card hsub

private lemma signed_card_sum {n : ℕ} (A : Finset (Signed n)) :
    (A.card : ℝ) = ∑ i : Fin n, ((if (i,false) ∈ A then (1:ℝ) else 0) + (if (i,true) ∈ A then (1:ℝ) else 0)) := by
  calc
    _ = ∑ p : Signed n, if p ∈ A then (1:ℝ) else 0 := by simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma support_deficit {n : ℕ} (F : Flattening n) (h : CrossConsistent F) :
    (F.1.card : ℝ) + F.2.card + (terrible F).card ≤ 2*n := by
  rw [signed_card_sum,signed_card_sum]
  have ht : ((terrible F).card : ℝ) = ∑ i : Fin n, if i ∈ terrible F then (1:ℝ) else 0 := by simp
  rw [ht,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : Fin n, (2:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h0 := h i false
      have h1 := h i true
      simp only [Bool.not_false,Bool.not_true] at h0 h1
      by_cases a0 : (i,false) ∈ F.1 <;> by_cases a1 : (i,true) ∈ F.1 <;>
        by_cases b0 : (i,false) ∈ F.2 <;> by_cases b1 : (i,true) ∈ F.2 <;>
        simp_all [terrible,badLeft,badRight,good,Bool.exists_bool] <;> norm_num
    _ = _ := by simp [mul_comm]
end BirthdayEntropy.Soundness.Fixed
end


noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.decEq
namespace BirthdayEntropy.Soundness.Fixed

lemma subtype_card_of_subset {U : Type*} [Fintype U] (A S : Finset U) (hS : S ⊆ A) :
    (S.subtype (· ∈ A)).card = S.card := by
  rw [Finset.card_subtype,Finset.filter_eq_self.mpr hS]

lemma subtype_injOn {U : Type*} [Fintype U] (A : Finset U) :
    Set.InjOn (Finset.subtype (· ∈ A)) {S : Finset U | S ⊆ A} := by
  intro S hS T hT heq
  have hh := congrArg (fun Z : Finset A => Z.map (Function.Embedding.subtype _)) heq
  simpa only [Finset.subtype_map_of_mem hS,Finset.subtype_map_of_mem hT] using hh

lemma subtype_subset_iff {U : Type*} [Fintype U] (A S T : Finset U) (hS : S ⊆ A) :
    S.subtype (· ∈ A) ⊆ T.subtype (· ∈ A) ↔ S ⊆ T := by
  constructor
  · intro h u hu
    have hu' : (⟨u,hS hu⟩ : A) ∈ S.subtype (· ∈ A) := by simpa using hu
    have ht' := h hu'
    simpa using ht' 
  · intro h u hu
    exact Finset.mem_subtype.mpr (h (Finset.mem_subtype.mp hu))

lemma avoidance_restrict {U : Type*} [Fintype U] (A : Finset U) (P : Finset (Finset U))
    (hP : P.Nonempty) (hPA : ∀ e ∈ P, e ⊆ A) (hpairs : ∀ e ∈ P, e.card = 2)
    (q : ℝ) (hq : ∀ u, ((P.filter (fun e => u ∈ e)).card : ℝ) ≤ q)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓA : ℓ ≤ A.card) :
    (((A.powersetCard ℓ).filter (fun S => ∀ e ∈ P, ¬e ⊆ S)).card : ℝ) ≤
      (Nat.choose A.card ℓ : ℝ) * Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(4*q*(A.card : ℝ)^2))) := by
  classical
  let lift : Finset U → Finset A := Finset.subtype (· ∈ A)
  let P' := P.image lift
  have hinj : Set.InjOn lift P := by
    intro e he f hf h
    exact subtype_injOn A (hPA e he) (hPA f hf) h
  have hP' : P'.Nonempty := hP.image lift
  have hcardP : P'.card = P.card := Finset.card_image_of_injOn hinj
  have hpair' : ∀ e ∈ P', e.card = 2 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    rw [subtype_card_of_subset A f (hPA f hf),hpairs f hf]
  have hq' : ∀ u : A, ((P'.filter (fun e => u ∈ e)).card : ℝ) ≤ q := by
    intro u
    have heq : P'.filter (fun e => u ∈ e) = (P.filter (fun e => u.val ∈ e)).image lift := by
      ext e
      simp only [P',Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨f,hf,rfl⟩,hu⟩
        exact ⟨f,⟨hf,Finset.mem_subtype.mp hu⟩,rfl⟩
      · rintro ⟨f,⟨hf,hu⟩,rfl⟩
        exact ⟨⟨f,hf,rfl⟩,Finset.mem_subtype.mpr hu⟩
    rw [heq]
    apply le_trans _ (hq u.val)
    exact_mod_cast Finset.card_image_le
  have hcount : ((A.powersetCard ℓ).filter (fun S => ∀ e ∈ P, ¬e ⊆ S)).card =
      ((Finset.univ.powersetCard ℓ : Finset (Finset A)).filter (fun S => ∀ e ∈ P', ¬e ⊆ S)).card := by
    apply Finset.card_bij (fun S _ => lift S)
    · intro S hS
      have hSC := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,?_⟩
      · exact (subtype_card_of_subset A S hSC.1).trans hSC.2
      · intro e he hes
        obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
        apply (Finset.mem_filter.mp hS).2 f hf
        exact (subtype_subset_iff A f S (hPA f hf)).mp hes
    · intro S hS T hT heq
      exact subtype_injOn A (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 heq
    · intro S hS
      let T : Finset U := S.map (Function.Embedding.subtype _)
      have hTA : T ⊆ A := by intro u hu; obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hu; exact v.property
      have hlift : lift T = S := by ext u; simp [T,lift]
      refine ⟨T,?_,hlift⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨hTA,?_⟩,?_⟩
      · simpa [T] using (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
      · intro e he hes
        apply (Finset.mem_filter.mp hS).2 (lift e) (Finset.mem_image_of_mem _ he)
        rw [←hlift]
        exact (subtype_subset_iff A e T (hPA e he)).mpr hes
  have h := pair_avoidance P' hP' hpair' q (by
    intro u
    calc
      _ = ((P'.filter (fun e => u ∈ e)).card : ℝ) := by
        apply congrArg (fun Z : Finset (Finset A) => (Z.card : ℝ))
        ext e
        simp only [Finset.mem_filter]
      _ ≤ q := hq' u) ℓ hℓ (by simpa using hℓA)
  rw [avoidanceProbability] at h
  simp only [Fintype.card_coe,hcardP] at h
  have hh := (div_le_iff₀ (show (0:ℝ)<Nat.choose A.card ℓ by exact_mod_cast Nat.choose_pos hℓA)).mp h
  apply le_trans _ (by simpa only [mul_comm] using hh)
  apply le_of_eq
  calc
    _ = (((Finset.univ.powersetCard ℓ : Finset (Finset A)).filter (fun S => ∀ e ∈ P', ¬e ⊆ S)).card : ℝ) := by exact_mod_cast hcount
    _ = _ := by
      apply congrArg (fun Z : Finset (Finset A) => (Z.card : ℝ))
      ext S
      simp

lemma family_avoidance_bound {U V : Type*} [Fintype U] (Z : Finset V)
    (f : V → Finset U) (hinj : Function.Injective f) (A : Finset U) (ℓ : ℕ)
    (hsize : ∀ v ∈ Z, (f v).card = ℓ)
    (P : Finset (Finset U)) (hP : P.Nonempty) (hPA : ∀ e ∈ P, e ⊆ A)
    (hpairs : ∀ e ∈ P, e.card = 2) (q : ℝ)
    (hq : ∀ u : U, ((P.filter (fun e => u ∈ e)).card : ℝ) ≤ q)
    (hℓ : 2 ≤ ℓ) (hℓA : ℓ ≤ A.card)
    (hZ : ∀ v ∈ Z, f v ⊆ A ∧ ∀ e ∈ P, ¬e ⊆ f v) :
    (Z.card : ℝ) ≤ (Nat.choose A.card ℓ : ℝ)*Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(4*q*(A.card : ℝ)^2))) := by
  classical
  have hsub : Z.image f ⊆ (A.powersetCard ℓ).filter (fun S => ∀ e ∈ P, ¬e ⊆ S) := by
    intro S hS
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨(hZ v hv).1,hsize v hv⟩,(hZ v hv).2⟩
  have hh : (Z.card : ℝ) ≤ (((A.powersetCard ℓ).filter (fun S => ∀ e ∈ P, ¬e ⊆ S)).card : ℝ) := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hc
    exact_mod_cast hc
  apply hh.trans
  exact avoidance_restrict A P hP hPA hpairs q hq ℓ hℓ hℓA

lemma vertex_avoidance_bound {n ℓ : ℕ} (Z : Finset (Vertex n ℓ)) (A : Finset (Signed n))
    (P : Finset (Finset (Signed n))) (hP : P.Nonempty) (hPA : ∀ e ∈ P, e ⊆ A)
    (hpairs : ∀ e ∈ P, e.card = 2) (q : ℝ)
    (hq : ∀ u : Signed n, ((P.filter (fun e => u ∈ e)).card : ℝ) ≤ q)
    (hℓ : 2 ≤ ℓ) (hℓA : ℓ ≤ A.card)
    (hZ : ∀ v ∈ Z, signed v ⊆ A ∧ ∀ e ∈ P, ¬e ⊆ signed v) :
    (Z.card : ℝ) ≤ (Nat.choose A.card ℓ : ℝ)*Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(4*q*(A.card : ℝ)^2))) := by
  apply family_avoidance_bound Z signed signed_inj A ℓ (fun v hv => card_signed v) P hP hPA hpairs q _ hℓ hℓA hZ
  intro u
  calc
    _ = ((P.filter (fun e => u ∈ e)).card : ℝ) := by
      apply congrArg (fun Z : Finset (Finset (Signed n)) => (Z.card : ℝ))
      ext e
      simp only [Finset.mem_filter]
    _ ≤ q := hq u
end BirthdayEntropy.Soundness.Fixed
end


noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness
namespace BirthdayEntropy.Soundness.Fixed

lemma forbidden_cell_bound {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (r : ℕ) (F : Flattening n) (hF : CrossConsistent F) (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ n)
    (P : Finset (Finset (Signed n))) (hP : P.Nonempty) (hPA : ∀ e ∈ P, e ⊆ F.1)
    (hpairs : ∀ e ∈ P, e.card = 2) (q : ℝ)
    (hq : ∀ u, ((P.filter (fun e => u ∈ e)).card : ℝ) ≤ q)
    (havoid : ∀ X ∈ acceptedCell φ H r F, ∀ i, ∀ e ∈ P, ¬e ⊆ signed (X.1 i)) :
    ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
      Real.exp (-(r : ℝ)*(P.card : ℝ)*(ℓ : ℝ)^2/(16*q*(n : ℝ)^2)) := by
  classical
  let Z := (allowed (ℓ := ℓ) F.1).filter (fun v => ∀ e ∈ P, ¬e ⊆ signed v)
  have hcount : ((acceptedCell φ H r F).card : ℝ) ≤
      (Z.card : ℝ)^r * ((allowed (ℓ := ℓ) F.2).card : ℝ)^r := by
    have hsub : acceptedCell φ H r F ⊆ (Fintype.piFinset (fun _ : Fin r => Z)) ×ˢ
      (Fintype.piFinset (fun _ : Fin r => allowed F.2)) := by
      intro X hX
      have hh : X ∈ accepted φ H r ∧ flatten X = F := by simpa only [acceptedCell,cell,Finset.mem_filter] using hX
      apply Finset.mem_product.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,havoid X hX i⟩
        simpa only [hh.2] using flatten_contains_left X i
      · apply Fintype.mem_piFinset.mpr
        intro j
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        simpa only [hh.2] using flatten_contains_right X j
    have hc : (acceptedCell φ H r F).card ≤ Z.card^r * (allowed (ℓ := ℓ) F.2).card^r := by
      simpa using Finset.card_le_card hsub
    exact_mod_cast hc
  by_cases hr : r = 0
  · subst r
    simpa using hcount
  have hZcard : (Z.card : ℝ) ≤ Nat.choose F.1.card ℓ := by
    have hle : Z.card ≤ (allowed (ℓ := ℓ) F.1).card := Finset.card_filter_le _ _
    exact_mod_cast hle.trans (allowed_card F.1)
  have hBcard : ((allowed (ℓ := ℓ) F.2).card : ℝ) ≤ Nat.choose F.2.card ℓ := by exact_mod_cast allowed_card F.2
  by_cases hla : ℓ ≤ F.1.card
  swap
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hla),Nat.cast_zero] at hZcard
    have hz : (Z.card : ℝ) = 0 := le_antisymm hZcard (by positivity)
    rw [hz,zero_pow hr,zero_mul] at hcount
    exact hcount.trans (by positivity)
  by_cases hlb : ℓ ≤ F.2.card
  swap
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hlb),Nat.cast_zero] at hBcard
    have hz : ((allowed (ℓ := ℓ) F.2).card : ℝ) = 0 := le_antisymm hBcard (by positivity)
    rw [hz,zero_pow hr,mul_zero] at hcount
    exact hcount.trans (by positivity)
  have hqpos : 0 < q := by
    obtain ⟨e,he⟩ := hP
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by rw [hpairs e he]; decide : 0 < e.card)
    have hc : (0 : ℝ) < (P.filter (fun e => u ∈ e)).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hu⟩⟩
    exact hc.trans_le (hq u)
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by omega : 0<ℓ) hℓn
  have hA : (0 : ℝ) < F.1.card := by exact_mod_cast lt_of_lt_of_le (by omega : 0<ℓ) hla
  have hAsize : (F.1.card : ℝ) ≤ 2*n := by
    have h := support_deficit F hF
    have ht : (0:ℝ) ≤ (terrible F).card := by positivity
    have hb : (0:ℝ) ≤ F.2.card := by positivity
    linarith
  have hsmall : (P.card : ℝ)*(ℓ : ℝ)^2/(16*q*(n : ℝ)^2) ≤
      (P.card : ℝ)*(ℓ : ℝ)^2/(4*q*(F.1.card : ℝ)^2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hsq : (F.1.card : ℝ)^2 ≤ (2*(n : ℝ))^2 := (sq_le_sq₀ hA.le (by positivity)).mpr hAsize
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*q by positivity)]
  have hZ := vertex_avoidance_bound Z F.1 P hP hPA hpairs q hq hℓ hla (by
    intro v hv
    have hh := Finset.mem_filter.mp hv
    exact ⟨(Finset.mem_filter.mp hh.1).2,hh.2⟩)
  have hZw : (Z.card : ℝ) ≤ (Nat.choose F.1.card ℓ : ℝ)*
      Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(16*q*(n : ℝ)^2))) := by
    apply hZ.trans
    gcongr
  have hbase : (Nat.choose F.1.card ℓ : ℝ)*(Nat.choose F.2.card ℓ : ℝ) ≤ (Nat.choose n ℓ : ℝ)^2 := by
    have hd := support_deficit F hF
    have hh := binomial_product_deficit F.1.card F.2.card n ℓ 0 (by norm_num) hla hlb hℓn (by
      have ht : (0:ℝ) ≤ (terrible F).card := by positivity
      linarith)
    simpa using hh
  have hprod : (Z.card : ℝ)*((allowed (ℓ := ℓ) F.2).card : ℝ) ≤
      (Nat.choose n ℓ : ℝ)^2*Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(16*q*(n : ℝ)^2))) := by
    calc
      _ ≤ ((Nat.choose F.1.card ℓ : ℝ)*Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(16*q*(n : ℝ)^2)))) *
          (Nat.choose F.2.card ℓ : ℝ) := by gcongr
      _ = ((Nat.choose F.1.card ℓ : ℝ)*(Nat.choose F.2.card ℓ : ℝ))*Real.exp (-((P.card : ℝ)*(ℓ : ℝ)^2/(16*q*(n : ℝ)^2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
  rw [←mul_pow] at hcount
  apply hcount.trans
  apply (pow_le_pow_left₀ (by positivity) hprod r).trans_eq
  rw [mul_pow,←pow_mul,←Real.exp_nat_mul]
  congr 2
  ring
end BirthdayEntropy.Soundness.Fixed
end


noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness
namespace BirthdayEntropy.Soundness.Fixed

lemma scope_card {n m : ℕ} (φ : CSP n m) (j : Fin m) : (φ.H.verts j).card = 3 := by
  simp [RandOrderCSP.Hypergraph.verts,Finset.card_image_of_injective _ (φ.H.row_inj j)]

lemma source_size {n m : ℕ} (φ : CSP n m) (d : ℝ) (hS : Source φ d) : (n : ℝ) ≤ 3*m := by
  have hdeg (v : Fin n) : (φ.H.deg v : ℝ) = ∑ j : Fin m, if v ∈ φ.H.verts j then (1:ℝ) else 0 := by
    simp [RandOrderCSP.Hypergraph.deg,RandOrderCSP.Hypergraph.edgesAt]
  have heq : (∑ v : Fin n, (φ.H.deg v : ℝ)) = 3*m := by
    simp_rw [hdeg]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin m, (3:ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa using congrArg (fun k : ℕ => (k:ℝ)) (scope_card φ j)
      _ = _ := by simp [mul_comm]
  calc
    (n : ℝ) = ∑ _v : Fin n, (1:ℝ) := by simp
    _ ≤ ∑ v : Fin n, (φ.H.deg v : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact_mod_cast (hS v).1
    _ = _ := heq

lemma nongood_card {n : ℕ} (F : Flattening n) :
    ((Finset.univ \ good F).card : ℝ) ≤ (terrible F).card + (badCount F : ℝ) := by
  have hsub : (Finset.univ \ good F) ⊆ (terrible F ∪ badLeft F) ∪ badRight F := by
    intro i hi
    by_cases hl : i ∈ badLeft F
    · simp [hl]
    by_cases hr : i ∈ badRight F
    · simp [hr]
    have ht : i ∈ terrible F := by simp [terrible,hl,hr,(Finset.mem_sdiff.mp hi).2]
    simp [ht]
  have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc' : (Finset.univ \ good F).card ≤ (terrible F).card + ((badLeft F).card + (badRight F).card) := by omega
  dsimp [badCount]
  exact_mod_cast hc' 

def goodViolations {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (F : Flattening n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => φ.f j (g ∘ φ.H.M j) = false ∧ φ.H.verts j ⊆ good F)

lemma good_violations_lower {n m : ℕ} (φ : CSP n m) (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε)
    (hS : Source φ d) (hG : Gap φ ε) (F : Flattening n)
    (ht : ((terrible F).card : ℝ) < beta d ε*n) (hb : (badCount F : ℝ) < beta d ε*n)
    (g : Fin n → Bool) : ε*(n : ℝ)/6 ≤ (goodViolations φ g F).card := by
  classical
  let NG := Finset.univ \ good F
  let Touch := NG.biUnion (fun v => φ.H.edgesAt v)
  let Vio := Finset.univ.filter (fun j => φ.f j (g ∘ φ.H.M j) = false)
  have htouch : (Touch.card : ℝ) ≤ d*((terrible F).card + (badCount F : ℝ)) := by
    have hc : Touch.card ≤ ∑ v ∈ NG, (φ.H.edgesAt v).card := Finset.card_biUnion_le
    calc
      (Touch.card : ℝ) ≤ ∑ v ∈ NG, ((φ.H.edgesAt v).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _v ∈ NG, d := by
        apply Finset.sum_le_sum
        intro v hv
        exact (hS v).2
      _ = (NG.card : ℝ)*d := by simp
      _ ≤ (((terrible F).card : ℝ)+(badCount F : ℝ))*d := mul_le_mul_of_nonneg_right (nongood_card F) (by linarith)
      _ = _ := by ring
  have hsub : Vio ⊆ goodViolations φ g F ∪ Touch := by
    intro j hj
    by_cases hscope : φ.H.verts j ⊆ good F
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2,hscope⟩)
    · apply Finset.mem_union_right
      obtain ⟨v,hv,hng⟩ := Finset.not_subset.mp hscope
      exact Finset.mem_biUnion.mpr ⟨v,by simp [NG,hng],by simp [RandOrderCSP.Hypergraph.edgesAt,hv]⟩
  have hvc : (Vio.card : ℝ) ≤ (goodViolations φ g F).card + (Touch.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hgap : ε*(m : ℝ) ≤ Vio.card := hG g
  have hn := source_size φ d hS
  have hβeps : 48*d*beta d ε ≤ ε := by
    have hh := min_le_right (1/4:ℝ) (ε/(48*d))
    have hpos : 0 < 48*d := by linarith
    have hx := (le_div_iff₀ hpos).mp hh
    simpa [beta,mul_comm] using hx
  have htouchsmall : (Touch.card : ℝ) ≤ ε*(n : ℝ)/24 := by
    have hcount : ((terrible F).card : ℝ)+(badCount F : ℝ) ≤ 2*beta d ε*n := by linarith
    have hd0 : 0 ≤ d := by linarith
    have hh := mul_le_mul_of_nonneg_left hcount hd0
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hβeps hn0]
  nlinarith [mul_le_mul_of_nonneg_left hn hε.le]


lemma good_value {n : ℕ} (F : Flattening n) (hF : CrossConsistent F) (i : Fin n) (hi : i ∈ good F) :
    (i,assignment F.1 i) ∈ F.1 ∧ (i,assignment F.1 i) ∈ F.2 := by
  obtain ⟨b,hbA,hbB⟩ := (Finset.mem_filter.mp hi).2
  cases b with
  | false =>
    have hn : (i,true) ∉ F.1 := by intro h; exact hF i true h hbB
    simpa [assignment,hn] using And.intro hbA hbB
  | true => simpa [assignment,hbA] using And.intro hbA hbB

def chosenPair {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (j : Fin m) : Finset (Signed n) :=
  {(φ.H.M j 0,g (φ.H.M j 0)),(φ.H.M j 1,g (φ.H.M j 1))}

lemma chosenPair_card {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (j : Fin m) :
    (chosenPair φ g j).card = 2 := by
  apply Finset.card_pair
  intro h
  have hh := φ.H.row_inj j (congrArg Prod.fst h)
  norm_num at hh

lemma chosenPair_scope {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (j : Fin m)
    (u : Signed n) (hu : u ∈ chosenPair φ g j) : u.1 ∈ φ.H.verts j := by
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  · have heq := Finset.mem_singleton.mp hu
    rw [heq]
    exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩

def chosenPairs {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (F : Flattening n) : Finset (Finset (Signed n)) :=
  (goodViolations φ g F).image (chosenPair φ g)

lemma chosenPairs_card {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (F : Flattening n)
    (d : ℝ) (hS : Source φ d) :
    ((goodViolations φ g F).card : ℝ) ≤ (chosenPairs φ g F).card*d := by
  classical
  have hfiber : ∀ e ∈ chosenPairs φ g F,
      (((goodViolations φ g F).filter (fun j => chosenPair φ g j = e)).card : ℝ) ≤ d := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    let u := φ.H.M j 0
    have hsub : (goodViolations φ g F).filter (fun k => chosenPair φ g k = chosenPair φ g j) ⊆ φ.H.edgesAt u := by
      intro k hk
      have heq := (Finset.mem_filter.mp hk).2
      have hum : (u,g u) ∈ chosenPair φ g k := by rw [heq]; simp [chosenPair,u]
      have hu := chosenPair_scope φ g k (u,g u) hum
      simpa [RandOrderCSP.Hypergraph.edgesAt] using hu
    have hcard : (((goodViolations φ g F).filter (fun k => chosenPair φ g k = chosenPair φ g j)).card : ℝ) ≤ φ.H.deg u := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans (hS u).2
  have heq := Finset.card_eq_sum_card_image (chosenPair φ g) (goodViolations φ g F)
  have heqR : ((goodViolations φ g F).card : ℝ) =
      ∑ e ∈ chosenPairs φ g F, (((goodViolations φ g F).filter (fun j => chosenPair φ g j = e)).card : ℝ) := by
    exact_mod_cast heq
  rw [heqR]
  calc
    _ ≤ ∑ _e ∈ chosenPairs φ g F, d := Finset.sum_le_sum hfiber
    _ = _ := by simp

lemma chosenPairs_incidence {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool) (F : Flattening n)
    (d : ℝ) (hS : Source φ d) (u : Signed n) :
    (((chosenPairs φ g F).filter (fun e => u ∈ e)).card : ℝ) ≤ d := by
  classical
  have hsub : (chosenPairs φ g F).filter (fun e => u ∈ e) ⊆
      (φ.H.edgesAt u.1).image (chosenPair φ g) := by
    intro e he
    have hh := Finset.mem_filter.mp he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hh.1
    have hu := chosenPair_scope φ g j u hh.2
    exact Finset.mem_image.mpr ⟨j,by simp [RandOrderCSP.Hypergraph.edgesAt,hu],rfl⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hcR : (((chosenPairs φ g F).filter (fun e => u ∈ e)).card : ℝ) ≤ φ.H.deg u.1 := by exact_mod_cast hc
  exact hcR.trans (hS u.1).2

lemma chosenPairs_left {n m : ℕ} (φ : CSP n m) (F : Flattening n) (hF : CrossConsistent F) :
    ∀ e ∈ chosenPairs φ (assignment F.1) F, e ⊆ F.1 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
  have hscope := (Finset.mem_filter.mp hj).2.2
  apply Finset.insert_subset_iff.mpr
  constructor
  · exact (good_value F hF _ (hscope (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩))).1
  · apply Finset.singleton_subset_iff.mpr
    exact (good_value F hF _ (hscope (Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩))).1

lemma assignment_of_mem {n : ℕ} (A : Finset (Signed n)) (hA : consistent A)
    (i : Fin n) (b : Bool) (hb : (i,b) ∈ A) : assignment A i = b := by
  cases b with
  | false =>
    have hn : (i,true) ∉ A := by intro h; exact hA i ⟨hb,h⟩
    simp [assignment,hn]
  | true => simp [assignment,hb]

lemma chosenPairs_avoided {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (r : ℕ) (F : Flattening n) (hF : CrossConsistent F) :
    ∀ X ∈ acceptedCell φ H r F, ∀ i, ∀ e ∈ chosenPairs φ (assignment F.1) F,
      ¬e ⊆ signed (X.1 i) := by
  classical
  intro X hX i e he hes
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
  have hj' := (Finset.mem_filter.mp hj).2
  have hscope := hj'.2
  have hvalue : ∀ k : Fin 3, (φ.H.M j k,assignment F.1 (φ.H.M j k)) ∈ F.2 := by
    intro k
    exact (good_value F hF _ (hscope (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩))).2
  have hX' : X ∈ accepted φ H r ∧ flatten X = F := by simpa only [acceptedCell,cell,Finset.mem_filter] using hX
  have hthird := hvalue 2
  have hthird' : (φ.H.M j 2,assignment F.1 (φ.H.M j 2)) ∈ (flatten X).2 := by simpa only [hX'.2] using hthird
  obtain ⟨k,hk,hthird⟩ := Finset.mem_biUnion.mp hthird'
  have hadj := (Finset.mem_filter.mp hX'.1).2.2.2 i k
  let A := signed (X.1 i) ∪ signed (X.2 k)
  have hbits : ∀ l : Fin 3, (φ.H.M j l,assignment F.1 (φ.H.M j l)) ∈ A := by
    intro l
    fin_cases l
    · exact Finset.mem_union_left _ (hes (by simp [chosenPair]))
    · exact Finset.mem_union_left _ (hes (by simp [chosenPair]))
    · exact Finset.mem_union_right _ hthird
  have hexpose : φ.H.verts j ⊆ support A := by
    intro u hu
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image.mpr ⟨_,hbits l,rfl⟩
  have hsatisfied := hadj.2.2 j hexpose
  have heq : assignment A ∘ φ.H.M j = assignment F.1 ∘ φ.H.M j := by
    funext l
    exact assignment_of_mem A hadj.2.1 _ _ (hbits l)
  rw [heq,hj'.1] at hsatisfied
  contradiction
end BirthdayEntropy.Soundness.Fixed
end


noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness

theorem BirthdayEntropy.Soundness.Fixed.source_loss (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε)
    {n m ℓ : ℕ} (φ : CSP n m) (hS : Source φ d) (hG : Gap φ ε)
    (H : Finset (Vertex n ℓ)) (r : ℕ) (F : Flattening n) (hF : CrossConsistent F)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ n)
    (ht : ((terrible F).card : ℝ) < beta d ε*n) (hb : (badCount F : ℝ) < beta d ε*n) :
    ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
      Real.exp (-(ε/(96*d^2)) * r * (n : ℝ)*(ratio n ℓ)^2) := by
  classical
  let g := assignment F.1
  let P := Fixed.chosenPairs φ g F
  have hn : (0:ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by omega : 0<ℓ) hℓn
  have hlow := Fixed.good_violations_lower φ d ε hd hε hS hG F ht hb g
  have hcount := Fixed.chosenPairs_card φ g F d hS
  have hdpos : 0 < d := by linarith
  have hPlow : ε*(n : ℝ)/(6*d) ≤ P.card := by
    apply (div_le_iff₀ (by positivity : 0 < 6*d)).mpr
    change ε*(n : ℝ) ≤ (Fixed.chosenPairs φ g F).card*(6*d)
    nlinarith
  have hP : P.Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have hz : P.card = 0 := by omega
    have hzR : (P.card : ℝ) = 0 := by exact_mod_cast hz
    rw [hzR] at hPlow
    have hh : 0 < ε*(n : ℝ)/(6*d) := by positivity
    linarith
  have hpair : ∀ e ∈ P, e.card = 2 := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    exact Fixed.chosenPair_card φ g j
  have hcell := Fixed.forbidden_cell_bound φ H r F hF hℓ hℓn P hP
    (Fixed.chosenPairs_left φ F hF) hpair d
    (by intro u; exact Fixed.chosenPairs_incidence φ g F d hS u)
    (Fixed.chosenPairs_avoided φ H r F hF)
  have hcoef : (ε/(96*d^2))*(n : ℝ)*(ratio n ℓ)^2 ≤
      (P.card : ℝ)*(ℓ : ℝ)^2/(16*d*(n : ℝ)^2) := by
    have hmul := mul_le_mul_of_nonneg_right hPlow (show 0 ≤ (ℓ : ℝ)^2/(16*d*(n : ℝ)^2) by positivity)
    calc
      _ = (ε*(n : ℝ)/(6*d))*((ℓ : ℝ)^2/(16*d*(n : ℝ)^2)) := by
        unfold ratio
        field_simp
        <;> ring
      _ ≤ (P.card : ℝ)*((ℓ : ℝ)^2/(16*d*(n : ℝ)^2)) := hmul
      _ = _ := by ring
  apply hcell.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hcoef (show 0 ≤ (r : ℝ) by positivity)
  calc
    _ = -((r : ℝ)*((P.card : ℝ)*(ℓ : ℝ)^2/(16*d*(n : ℝ)^2))) := by ring
    _ ≤ -((r : ℝ)*((ε/(96*d^2))*(n : ℝ)*(ratio n ℓ)^2)) := neg_le_neg hm
    _ = _ := by ring
end


noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness
namespace BirthdayEntropy.Soundness.Fixed

def oppositePair {n : ℕ} (i : Fin n) : Finset (Signed n) := {(i,false),(i,true)}

lemma oppositePair_inj {n : ℕ} : Function.Injective (@oppositePair n) := by
  intro i j h
  have hh : (i,false) ∈ oppositePair j := by rw [←h]; simp [oppositePair]
  simpa [oppositePair] using hh

lemma signed_consistent {n ℓ : ℕ} (v : Vertex n ℓ) : consistent (signed v) := by
  intro i hi
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hi.1
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hi.2
  have hab : a = b := Subtype.ext ((congrArg Prod.fst hea).trans (congrArg Prod.fst heb).symm)
  have hf := congrArg Prod.snd hea
  have ht := congrArg Prod.snd heb
  subst b
  simp_all

lemma bad_left_loss {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) (r : ℕ)
    (F : Flattening n) (hF : CrossConsistent F) (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ n)
    (hBL : (badLeft F).Nonempty) :
    ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r)*
      Real.exp (-(r : ℝ)*(badLeft F).card*(ratio n ℓ)^2/16) := by
  let P := (badLeft F).image oppositePair
  have hP : P.Nonempty := hBL.image oppositePair
  have hPA : ∀ e ∈ P, e ⊆ F.1 := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    have hh := (Finset.mem_filter.mp hi).2
    simpa [oppositePair,Finset.insert_subset_iff] using hh
  have hpairs : ∀ e ∈ P, e.card = 2 := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    simp [oppositePair]
  have hq : ∀ u : Signed n, ((P.filter (fun e => u ∈ e)).card : ℝ) ≤ 1 := by
    intro u
    have hsub : P.filter (fun e => u ∈ e) ⊆ {oppositePair u.1} := by
      intro e he
      have hh := Finset.mem_filter.mp he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh.1
      have heq : u.1 = i := by
        rcases Finset.mem_insert.mp hh.2 with hu | hu
        · exact congrArg Prod.fst hu
        · exact congrArg Prod.fst (Finset.mem_singleton.mp hu)
      simp [heq]
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_singleton _)
  have havoid : ∀ X ∈ acceptedCell φ H r F, ∀ i, ∀ e ∈ P, ¬e ⊆ signed (X.1 i) := by
    intro X hX i e he hes
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    apply signed_consistent (X.1 i) v
    exact ⟨hes (by simp [oppositePair]),hes (by simp [oppositePair])⟩
  have hh := forbidden_cell_bound φ H r F hF hℓ hℓn P hP hPA hpairs 1 hq havoid
  have hcard : P.card = (badLeft F).card := Finset.card_image_of_injective _ oppositePair_inj
  rw [hcard] at hh
  convert hh using 1
  congr 2
  unfold ratio
  ring

lemma cell_swap {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) (r : ℕ) (F : Flattening n) :
    (acceptedCell φ H r F).card = (acceptedCell φ H r (F.2,F.1)).card := by
  classical
  have hmem (X : Tuple n ℓ r) (F : Flattening n) : X ∈ acceptedCell φ H r F →
      X.swap ∈ acceptedCell φ H r (F.2,F.1) := by
    intro hX
    have hh : ((∀ i, X.1 i ∈ H) ∧ (∀ j, X.2 j ∈ H) ∧ ∀ i j, (graph φ).Adj (X.1 i) (X.2 j)) ∧ flatten X = F := by
      simpa only [acceptedCell,cell,accepted,Finset.mem_filter,Finset.mem_univ,true_and] using hX
    simp only [acceptedCell,cell,accepted,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨⟨hh.1.2.1,hh.1.1,fun i j => (graph φ).adj_symm (hh.1.2.2 j i)⟩,?_⟩
    change ((flatten X).2,(flatten X).1) = (F.2,F.1)
    rw [hh.2]
  apply Finset.card_bij (fun X _ => X.swap)
  · intro X hX
    exact hmem X F hX
  · intro X hX Y hY heq
    exact Prod.swap_injective heq
  · intro Y hY
    refine ⟨Y.swap,?_,by simp⟩
    simpa using hmem Y (F.2,F.1) hY

lemma cross_swap {n : ℕ} (F : Flattening n) (hF : CrossConsistent F) : CrossConsistent (F.2,F.1) := by
  intro i b hi hj
  have hh := hF i (!b) hj
  apply hh
  simpa using hi

lemma bad_loss {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) (r : ℕ)
    (F : Flattening n) (hF : CrossConsistent F) (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ n) :
    ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r)*
      Real.exp (-(1/32:ℝ)*r*(ratio n ℓ)^2*(badCount F)) := by
  have hx : 0 ≤ ratio n ℓ := by unfold ratio; positivity
  by_cases hzero : badCount F = 0
  · have hh := support_deficit_cell_bound φ H r F hF hℓn
    rw [hzero,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]
    apply hh.trans
    have he : Real.exp (-(r : ℝ)*ratio n ℓ*(terrible F).card) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) hx])
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ (Nat.choose n ℓ : ℝ)^(2*r) by positivity)]
  have hpos : 0 < badCount F := Nat.pos_of_ne_zero hzero
  by_cases hleft : (badRight F).card ≤ (badLeft F).card
  · have hBL : (badLeft F).Nonempty := Finset.card_pos.mp (by dsimp [badCount] at hpos; omega)
    have hh := bad_left_loss φ H r F hF hℓ hℓn hBL
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hhalf : (badCount F : ℝ) ≤ 2*(badLeft F).card := by dsimp [badCount]; exact_mod_cast (by omega : (badLeft F).card+(badRight F).card ≤ 2*(badLeft F).card)
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (r : ℝ)*(ratio n ℓ)^2 by positivity)]
  · have hBR : (badRight F).Nonempty := Finset.card_pos.mp (by omega)
    have hh := bad_left_loss φ H r (F.2,F.1) (cross_swap F hF) hℓ hℓn hBR
    rw [←cell_swap φ H r F] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hhalf : (badCount F : ℝ) ≤ 2*(badRight F).card := by dsimp [badCount]; exact_mod_cast (by omega : (badLeft F).card+(badRight F).card ≤ 2*(badRight F).card)
    change -(r : ℝ)*(badRight F).card*(ratio n ℓ)^2/16 ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (r : ℝ)*(ratio n ℓ)^2 by positivity)]
end BirthdayEntropy.Soundness.Fixed
end


noncomputable section
open scoped Classical
open Finset BirthdayEntropy.Soundness

theorem solution (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), 2 ≤ ℓ → (ℓ : ℝ) < min (beta d ε) (1/2) * n →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
      ∀ (r : ℕ) (F : Flattening n), CrossConsistent F →
        ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
          Real.exp (-c₀ * r * ratio n ℓ * energy ℓ (beta d ε) F) := by
  classical
  let c₀ : ℝ := min 1 (min (1/32) (ε/(96*d^2)))
  have hdpos : 0 < d := by linarith
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc1 : c₀ ≤ 1 := min_le_left _ _
  have hcb : c₀ ≤ 1/32 := (min_le_right _ _).trans (min_le_left _ _)
  have hcs : c₀ ≤ ε/(96*d^2) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c₀,hc₀,?_⟩
  intro n m φ hS hG ℓ hℓ hscale H hH r F hF
  have hn : 0 < (n : ℝ) := by
    by_contra h
    have hn0 : (n : ℝ)=0 := le_antisymm (le_of_not_gt h) (by positivity)
    rw [hn0,mul_zero] at hscale
    have : (2:ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hℓn : ℓ ≤ n := by
    have hmin := min_le_right (beta d ε) (1/2)
    have hh : (ℓ : ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hx : 0 ≤ ratio n ℓ := by unfold ratio; positivity
  have hterr := support_deficit_cell_bound φ H r F hF hℓn
  have htprod : 0 ≤ (r : ℝ)*ratio n ℓ*((terrible F).card : ℝ) := by positivity
  have hbase : ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) := by
    have he : Real.exp (-(r : ℝ)*ratio n ℓ*(terrible F).card) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ (Nat.choose n ℓ : ℝ)^(2*r) by positivity)
    simp only [mul_one] at hh
    exact hterr.trans hh
  have hterr' : ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
      Real.exp (-c₀*r*ratio n ℓ*(terrible F).card) := by
    apply hterr.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc1 htprod]
  have hbad := Fixed.bad_loss φ H r F hF hℓ hℓn
  have hbprod : 0 ≤ (r : ℝ)*(ratio n ℓ)^2*(badCount F : ℝ) := by positivity
  have hbad' : ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r)*
      Real.exp (-c₀*r*ratio n ℓ*(ratio n ℓ*badCount F)) := by
    apply hbad.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb hbprod]
  have hsource' (ht : ((terrible F).card : ℝ) < beta d ε*n) (hb : (badCount F : ℝ) < beta d ε*n) :
      ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r)*
        Real.exp (-c₀*r*ratio n ℓ*((n : ℝ)*ratio n ℓ)) := by
    have hh := Fixed.source_loss d ε hd hε φ hS hG H r F hF hℓ hℓn ht hb
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ (r : ℝ)*(n : ℝ)*(ratio n ℓ)^2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcs hp]
  have hcases : energy ℓ (beta d ε) F = ((terrible F).card : ℝ) ∨
      energy ℓ (beta d ε) F = ratio n ℓ*badCount F ∨
      energy ℓ (beta d ε) F = (if ((terrible F).card : ℝ) < beta d ε*n ∧ (badCount F : ℝ) < beta d ε*n
        then (n : ℝ)*ratio n ℓ else 0) := by
    unfold energy
    rcases max_choice ((terrible F).card : ℝ) (max (ratio n ℓ*badCount F)
      (if ((terrible F).card : ℝ) < beta d ε*n ∧ (badCount F : ℝ) < beta d ε*n then (n : ℝ)*ratio n ℓ else 0)) with h | h
    · exact Or.inl h
    · rcases max_choice (ratio n ℓ*badCount F)
        (if ((terrible F).card : ℝ) < beta d ε*n ∧ (badCount F : ℝ) < beta d ε*n then (n : ℝ)*ratio n ℓ else 0) with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (h.trans h'))
  rcases hcases with ht | hb | hi
  · simpa only [ht] using hterr'
  · simpa only [hb] using hbad'
  · by_cases hc : ((terrible F).card : ℝ) < beta d ε*n ∧ (badCount F : ℝ) < beta d ε*n
    · simpa only [hi,if_pos hc] using hsource' hc.1 hc.2
    · rw [hi,if_neg hc,mul_zero,Real.exp_zero,mul_one]
      exact hbase
end
