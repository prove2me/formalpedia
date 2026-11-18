-- Prove2me | solution 1 for BddExp3SUM.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T18:49:35.684786+00:00
-- url     : https://prove2.me/submissions/22e17ebd-0789-4dff-a00c-f2c4578679ad

import Definitions.Def_BddExp3SUM_Profiles
import Definitions.Def_BddExp3SUM_Hash


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


open scoped BigOperators

namespace BddExp3SUM.TripleProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma subinst_nonempty {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (i : Fin 3) : (U i).Nonempty := by
  classical
  obtain ⟨x, hx, he⟩ := h.isProfile i
  rw [he]
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

lemma sVal_eq {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) (i : Fin 3)
    (x : Grp M r) (hx : x ∈ U i) : sVal S U i d = sCount (S i) d x := by
  classical
  obtain ⟨a, ha, hU⟩ := h.isProfile i
  have hxP : profile (S i) x = profile (S i) a := by
    rw [hU] at hx
    exact (Finset.mem_filter.mp hx).2
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    rw [hU] at hy
    have he := congrFun ((Finset.mem_filter.mp hy).2.trans hxP.symm) ⟨d, hd⟩
    exact he.le
  · exact Finset.le_sup hx

lemma sVal_pos {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) (i : Fin 3) : 0 < sVal S U i d := by
  obtain ⟨x, hx⟩ := subinst_nonempty h i
  rw [sVal_eq h hd i x hx]
  exact pow_pos (by norm_num) _

lemma count_lt_two_sVal {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) (i : Fin 3)
    (x : Grp M r) (hx : x ∈ U i) : cosetCount (S i) d x < 2 * sVal S U i d := by
  rw [sVal_eq h hd i x hx]
  simpa only [sCount, dyadic, pow_succ, mul_comm] using
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (cosetCount (S i) d x)

noncomputable def triples {α : Type*} [AddCommGroup α] (A B C : Finset α) (H : AddSubgroup α) :
    Finset (α × α × α) := by
  classical
  exact (A ×ˢ B ×ˢ C).filter (fun q => q.1 + q.2.1 + q.2.2 ∈ H)

lemma triples_cyclic {α : Type*} [AddCommGroup α] (A B C : Finset α) (H : AddSubgroup α) :
    (triples A B C H).card = (triples B C A H).card := by
  classical
  apply Finset.card_bij (fun q _ => (q.2.1, q.2.2, q.1))
  · intro q hq
    rcases q with ⟨a, b, c⟩
    simp only [triples, Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2.1, hq.1.2.2, hq.1.1⟩, by convert hq.2 using 1 <;> abel⟩
  · intro a ha b hb he
    exact Prod.ext (congrArg (fun p => p.2.2) he)
      (Prod.ext (congrArg (fun p => p.1) he) (congrArg (fun p => p.2.1) he))
  · intro q hq
    rcases q with ⟨b, c, a⟩
    refine ⟨(a, b, c), ?_, rfl⟩
    simp only [triples, Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2.2, hq.1.1, hq.1.2.1⟩, by convert hq.2 using 1 <;> abel⟩

lemma triples_card_sum {α : Type*} [AddCommGroup α] (A B C : Finset α) (H : AddSubgroup α) :
    (triples A B C H).card = ∑ bc ∈ B ×ˢ C, (A.filter fun a => a + bc.1 + bc.2 ∈ H).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := B ×ˢ C) (by
    intro q hq
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)]
  apply Finset.sum_congr rfl
  intro bc hbc
  have hfilter : (triples A B C H).filter (fun q => q.2 = bc) =
      (A.filter fun a => a + bc.1 + bc.2 ∈ H) ×ˢ {bc} := by
    ext q
    rcases q with ⟨a, b, c⟩
    simp only [triples, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨ha, hb, hc⟩, hsum⟩, he⟩
      subst bc
      exact ⟨⟨ha, hsum⟩, rfl⟩
    · rintro ⟨⟨ha, hsum⟩, he⟩
      subst bc
      exact ⟨⟨⟨ha, (Finset.mem_product.mp hbc).1, (Finset.mem_product.mp hbc).2⟩, hsum⟩, rfl⟩
  rw [hfilter, Finset.card_product, Finset.card_singleton, mul_one]

lemma fiber_bound {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) (i : Fin 3) (b c : Grp M r) :
    ((U i).filter fun a => a + b + c ∈ H M r d).card < 2 * sVal S U i d := by
  classical
  let T := (U i).filter (fun a => a + b + c ∈ H M r d)
  by_cases hT : T.Nonempty
  · obtain ⟨a, ha⟩ := hT
    have haU := (Finset.mem_filter.mp ha).1
    have hsub : T ⊆ (S i).filter (fun y => y - a ∈ H M r d) := by
      intro y hy
      have hyU := (Finset.mem_filter.mp hy).1
      refine Finset.mem_filter.mpr ⟨CosetProof.subinst_subset h i hyU, ?_⟩
      have hh := (H M r d).sub_mem (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp ha).2
      convert hh using 1 <;> abel
    exact (Finset.card_le_card hsub).trans_lt (count_lt_two_sVal h hd i a haU)
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card < _
    rw [he, Finset.card_empty]
    have hp := sVal_pos h hd i
    omega

lemma triple_bound_first {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) (i j k : Fin 3) :
    (triples (U i) (U j) (U k) (H M r d)).card < 2 * sVal S U i d * n ^ 2 := by
  classical
  rw [triples_card_sum]
  have hsum : (∑ bc ∈ U j ×ˢ U k, ((U i).filter fun a => a + bc.1 + bc.2 ∈ H M r d).card) <
      ∑ _bc ∈ U j ×ˢ U k, 2 * sVal S U i d := by
    apply Finset.sum_lt_sum_of_nonempty
      ((subinst_nonempty h j).product (subinst_nonempty h k))
    intro bc _
    exact fiber_bound h hd i bc.1 bc.2
  apply hsum.trans_le
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_product]
  have hj : (U j).card ≤ n := (Finset.card_le_card (CosetProof.subinst_subset h j)).trans (h.card_le j)
  have hk : (U k).card ≤ n := (Finset.card_le_card (CosetProof.subinst_subset h k)).trans (h.card_le k)
  calc
    _ = (2 * sVal S U i d) * ((U j).card * (U k).card) := by ring
    _ ≤ (2 * sVal S U i d) * (n * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hj hk)
    _ = _ := by ring

end BddExp3SUM.TripleProof


open scoped BigOperators

namespace BddExp3SUM.TripleProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma represented_cosets_sVal {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) (i : Fin 3) :
    cosetsRepresented (U i) d * sVal S U i d ≤ n := by
  have hh := CosetProof.fiber_image_lower_bound (S i) (U i)
    (fun x => (QuotientAddGroup.mk x : Grp M r ⧸ H M r d)) (sVal S U i d) (by
      intro x hx
      have hc : sVal S U i d ≤ cosetCount (S i) d x := by
        rw [sVal_eq h hd i x hx]
        exact CosetProof.dyadic_count_le (S i) d x (CosetProof.subinst_subset h i hx)
      convert hc using 1
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro y hy
      exact QuotientAddGroup.eq_iff_sub_mem)
  exact hh.trans (h.card_le i)

lemma countIn_bound {M r n d : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) (hd : d ∈ Dvs M) :
    countIn U d < 2 * sMin S U d * n ^ 2 := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : Fin 3 => sVal S U i d)
  change (Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => sVal S U i d)) = _ at he
  rw [show sMin S U d = sVal S U i d from he]
  fin_cases i
  · exact triple_bound_first h hd 0 1 2
  · change (triples (U 0) (U 1) (U 2) (H M r d)).card < _
    rw [triples_cyclic]
    exact triple_bound_first h hd 1 2 0
  · change (triples (U 0) (U 1) (U 2) (H M r d)).card < _
    rw [triples_cyclic, triples_cyclic]
    exact triple_bound_first h hd 2 0 1

lemma full_coset {M r : ℕ} (S : Finset (Grp M r)) (x : Grp M r) :
    cosetCount S M x = S.card := by
  unfold cosetCount
  congr 1
  apply Finset.filter_true_of_mem
  intro y hy
  change M • (y - x) = 0
  ext i
  simp [nsmul_eq_mul]

lemma sMin_sqrt_lower {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Subinst M r n S U) : Real.sqrt (n : ℝ) / 2 < sMin S U M := by
  have hM : M ∈ Dvs M := by
    have hpos : M ≠ 0 := by have := h.two_le; omega
    simp [Dvs, Nat.mem_divisors, hpos, h.two_le]
  have hpoint (i : Fin 3) : Real.sqrt (n : ℝ) / 2 < sVal S U i M := by
    obtain ⟨x, hx⟩ := subinst_nonempty h i
    have hl := count_lt_two_sVal h hM i x hx
    rw [full_coset] at hl
    have hr : ((S i).card : ℝ) < 2 * (sVal S U i M : ℝ) := by exact_mod_cast hl
    linarith [h.sqrt_lt i]
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : Fin 3 => sVal S U i M)
  change sMin S U M = sVal S U i M at he
  rw [he]
  exact hpoint i

lemma quarter_power_le_half_sqrt {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt (n : ℝ) / 2 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hs4 : 4 ≤ Real.sqrt (n : ℝ) := by
    calc
      (4 : ℝ) = Real.sqrt 16 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hn16
  have hss2 : 2 ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
    calc
      (2 : ℝ) = Real.sqrt 4 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hs4
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))
  have hid : (n : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0]
    norm_num
  rw [hid]
  nlinarith

theorem lemma_2 {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)} (h : Subinst M r n S U) :
    (∀ d ∈ Dvs M,
      ((countIn U d : ℝ) < 2 * sMin S U d * (n : ℝ) ^ 2) ∧
      ∀ i, (cosetsRepresented (U i) d : ℝ) ≤ (n : ℝ) / sVal S U i d ∧
        (n : ℝ) / sVal S U i d ≤ (n : ℝ) / sMin S U d) ∧
    √(n : ℝ) / 2 < sMin S U M ∧ (n : ℝ) ^ ((1 : ℝ) / 4) ≤ √(n : ℝ) / 2 := by
  constructor
  · intro d hd
    constructor
    · exact_mod_cast countIn_bound h hd
    · intro i
      have hpos : (0 : ℝ) < sVal S U i d := by exact_mod_cast sVal_pos h hd i
      have hmin : sMin S U d ≤ sVal S U i d := Finset.inf'_le _ (Finset.mem_univ i)
      have hminpos : (0 : ℝ) < sMin S U d := by
        obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
          (fun j : Fin 3 => sVal S U j d)
        change sMin S U d = sVal S U j d at he
        rw [he]
        exact_mod_cast sVal_pos h hd j
      constructor
      · apply (le_div_iff₀ hpos).mpr
        exact_mod_cast represented_cosets_sVal h hd i
      · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hminpos (by exact_mod_cast hmin)
  · exact ⟨sMin_sqrt_lower h, quarter_power_le_half_sqrt h.n_ge⟩

end BddExp3SUM.TripleProof

open BddExp3SUM

theorem solution {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)} (h : Subinst M r n S U) :
    (∀ d ∈ Dvs M,
      ((countIn U d : ℝ) < 2 * sMin S U d * (n : ℝ) ^ 2) ∧
      ∀ i, (cosetsRepresented (U i) d : ℝ) ≤ (n : ℝ) / sVal S U i d ∧
        (n : ℝ) / sVal S U i d ≤ (n : ℝ) / sMin S U d) ∧
    √(n : ℝ) / 2 < sMin S U M ∧ (n : ℝ) ^ ((1 : ℝ) / 4) ≤ √(n : ℝ) / 2  := BddExp3SUM.TripleProof.lemma_2 h
