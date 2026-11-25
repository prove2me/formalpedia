-- Prove2me | solution 1 for DetDLP.w3_stage2_abstract_coset_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T20:41:45.8049+00:00
-- url     : https://prove2.me/submissions/b5a35c7b-f95c-4d04-8fc9-56072f46337b

import Definitions.Def_DetDLP_W3_CosetTrace
import Theorems.Thm_DetDLP_proposition_4_1_fixed_shift_soundness
import Theorems.Thm_DetDLP_lemma_4_2_newton_binomial_filter
import Theorems.Thm_DetDLP_lemma_4_4_coset_update_halving

set_option autoImplicit false
open DetDLP

private theorem w3_rep_mem {M N : ℕ} [NeZero M] (s : w3_Rep M N) : s.1 ∈ w3_coset s := by
  exact ⟨0, by simp⟩

private theorem w3_basis_full {M N : ℕ} : IsModularLatticeBasis M (w3_full M N).2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hij; simp [w3_full, Matrix.one_apply, ne_of_lt hij]
  · intro i; simp [w3_full]
  · intro i j hji; simp [w3_full, Matrix.one_apply, ne_of_gt hji]
  · intro v; exact ⟨_, (Matrix.one_mulVec _).symm⟩
  · simp [w3_full]

private theorem w3_in_full {M N : ℕ} [NeZero M] (x : w3_Label M N) : x ∈ w3_coset (w3_full M N) := by
  refine ⟨fun i => ((x i).val : ℤ), ?_⟩
  intro i; simp [w3_full, ZMod.natCast_zmod_val]

private theorem w3_update_exists {M N : ℕ} [NeZero M] (hM : 2 ≤ M) (hN : 1 ≤ N)
    (s : w3_Rep M N) (r : w3_Row M N) (hs : IsModularLatticeBasis M s.2)
    (h : ∃ x ∈ w3_coset s, w3_holds r x) : ∃ t, w3_update r s t ∧
      (¬ w3_holds r s.1 → 2 * Nat.card (w3_coset t) ≤ Nat.card (w3_coset s)) := by
  obtain ⟨_, _, _, H⟩ := lemma_4_4_coset_update_halving
  obtain ⟨x, B, hb, he, _, _, hh⟩ := H M N hM hN s.1 s.2 r.1 r.2 hs h
  refine ⟨(x,B), ⟨hb,he⟩, fun hv => ?_⟩
  change 2 * Nat.card (affineCoset M x B) ≤ _
  rw [he]; exact (hh hv).2

private theorem w3_init_exists {M N : ℕ} [NeZero M] (hM : 2 ≤ M) (hN : 1 ≤ N)
    (rs : List (w3_Row M N)) (s : w3_Rep M N) (lam : w3_Label M N)
    (hs : IsModularLatticeBasis M s.2) (hl : lam ∈ w3_coset s) (hr : ∀ r ∈ rs, w3_holds r lam) :
    ∃ t, w3_InitTrace rs s t ∧ IsModularLatticeBasis M t.2 ∧ lam ∈ w3_coset t := by
  induction rs generalizing s with
  | nil => exact ⟨s,.nil s,hs,hl⟩
  | cons r rs ih =>
    obtain ⟨t, hu, _⟩ := w3_update_exists hM hN s r hs ⟨lam,hl,hr r (by simp)⟩
    have ht : lam ∈ w3_coset t := hu.2.symm ▸ ⟨hl,hr r (by simp)⟩
    obtain ⟨u,hu',hb,hl'⟩ := ih t hu.1 ht (fun r' hr' => hr _ (by simp [hr']))
    exact ⟨u,.cons hu hu',hb,hl'⟩

private theorem w3_init_exact {M N : ℕ} [NeZero M] {rs : List (w3_Row M N)} {s t : w3_Rep M N}
    (h : w3_InitTrace rs s t) (x : w3_Label M N) : x ∈ w3_coset t ↔ x ∈ w3_coset s ∧ ∀ r ∈ rs, w3_holds r x := by
  induction h with
  | nil => simp
  | cons hu _ ih => rw [ih,hu.2]; simp [and_assoc]

private theorem w3_cuts_subset {G : Type*} [AddCommGroup G] {m M : ℕ} [NeZero M]
    {FB : IndexedFactorBase G m} {P : G} {n : ℕ} {s t : w3_Rep M FB.totalCoords}
    (h : w3_Cuts FB M P n s t) : w3_coset t ⊆ w3_coset s := by
  induction h with
  | nil => exact Set.Subset.rfl
  | cons h _ ih =>
    obtain ⟨_,_,_,_,_,hu,_⟩ := h
    exact ih.trans (hu.2.symm ▸ Set.sep_subset _ _)

section Labels
variable {G : Type*} {m : ℕ} (FB : IndexedFactorBase G m) (M : ℕ) [NeZero M]

private theorem w3_sum_slots (X : FB.BlockTuple) (v : Fin FB.totalCoords → ℤ) :
    (∑ j, (FB.tupleCnt X j : ℤ) * v j) = ∑ i, ∑ k, v (FB.coordOf i (X i k)) := by
  classical
  simp only [IndexedFactorBase.tupleCnt, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _
  simp [ite_mul]

private theorem w3_label_cast (y : w3_Label M FB.totalCoords) (X : FB.BlockTuple) :
    ((FB.tupleLabelSum M y X : ℤ) : ZMod M) = ∑ i, (FB.tupleCnt X i : ZMod M) * y i := by
  simp [IndexedFactorBase.tupleLabelSum, ZMod.natCast_zmod_val]

private theorem w3_row_eq (y : w3_Label M FB.totalCoords) (X Y : FB.BlockTuple) :
    w3_holds (w3_shiftRow FB M X Y) y ↔ ((w3_delta FB M y X Y : ℤ) : ZMod M) = 1 := by
  simp only [w3_holds,w3_shiftRow,sub_mul,Finset.sum_sub_distrib,w3_delta,Int.cast_sub,w3_label_cast]

private theorem w3_init_iff (U : Fin FB.totalCoords → FB.BlockTuple) (y : w3_Label M FB.totalCoords) :
    (∀ r ∈ w3_initRows FB M U, w3_holds r y) ↔ FB.SatisfiesInitialCongruences M U y := by
  classical
  simp [w3_initRows,w3_holds,w3_unitRow,IndexedFactorBase.SatisfiesInitialCongruences,
    w3_label_cast,sub_mul,Finset.sum_sub_distrib,ite_mul,sub_eq_zero]

private theorem w3_delta_range (y : w3_Label M FB.totalCoords) (X Y : FB.BlockTuple) :
    -((2*m : ℕ) : ℤ) * ((M : ℤ)-1) ≤ w3_delta FB M y X Y ∧
    w3_delta FB M y X Y ≤ ((2*m : ℕ) : ℤ) * ((M : ℤ)-1) := by
  have bounds (T : FB.BlockTuple) : 0 ≤ FB.tupleLabelSum M y T ∧
      FB.tupleLabelSum M y T ≤ ((2*m : ℕ) : ℤ) * ((M : ℤ)-1) := by
    unfold IndexedFactorBase.tupleLabelSum; rw [w3_sum_slots]
    refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity, ?_⟩
    calc _ ≤ ∑ _i : Fin m, ∑ _k : Fin 2, ((M : ℤ)-1) := by
                gcongr with i _ k; have := (y (FB.coordOf i (T i k))).val_lt; omega
         _ = _ := by simp; ring
  obtain ⟨hx,hx'⟩ := bounds X; obtain ⟨hy,hy'⟩ := bounds Y
  unfold w3_delta; constructor <;> linarith

private theorem w3_flat_slot {n : ℕ} (F : Fin n → List G) (i : Fin n) (r : Fin (F i).length) :
    ((List.finRange n).flatMap F)[(∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), (F j).length) + r.val]? = some ((F i).get r) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i r
    · intro s; simp [List.finRange_succ,List.flatMap_cons,List.getElem?_append,s.isLt]
    · intro s
      have hsum : (∑ t ∈ Finset.univ.filter (fun t : Fin (n+1) => t < j.succ), (F t).length) =
          (F 0).length + ∑ t ∈ Finset.univ.filter (fun t : Fin n => t < j), (F t.succ).length := by
        simp only [Finset.sum_filter,Fin.sum_univ_succ,Fin.succ_pos,if_true,Fin.succ_lt_succ_iff]
      simpa [List.finRange_succ,List.flatMap_cons,List.flatMap_map,hsum,Nat.add_assoc,
        List.getElem?_append,Function.comp_def] using ih (fun t => F t.succ) j s

private theorem w3_elem_slot (P Q : G) (i : Fin m) (r : Fin (FB.blocks i).length) :
    FB.elem P Q (FB.coordOf i r) = (FB.blocks i).get r := by
  have h := FB.blockOffset_add_lt i r
  have hlen : FB.blockOffset i + r.val < ((List.finRange m).flatMap FB.blocks).length := by
    rw [List.length_flatMap, ← Fin.sum_univ_def]; exact h
  have he := w3_flat_slot FB.blocks i r
  change ((List.finRange m).flatMap FB.blocks)[FB.blockOffset i + r.val]? = some _ at he
  rw [List.getElem?_eq_getElem hlen] at he
  unfold IndexedFactorBase.elem
  rw [dif_pos (show (FB.coordOf i r).val < FB.totalBaseSize from h)]
  exact Option.some.inj he

end Labels

private theorem w3_card_bound {M N : ℕ} [NeZero M] (s : w3_Rep M N) : Nat.card (w3_coset s) ≤ M ^ N := by
  classical
  have h := Nat.card_le_card_of_injective (Subtype.val : w3_coset s → w3_Label M N) Subtype.val_injective
  simpa [w3_Label,Nat.card_eq_fintype_card,Fintype.card_pi_const,ZMod.card] using h

private theorem w3_fuel {G : Type*} [AddCommGroup G] {m M : ℕ} [NeZero M] (FB : IndexedFactorBase G m) (P : G)
    (lam : w3_Label M FB.totalCoords) (hlp : w3_pass FB M P lam)
    (step : ∀ s : w3_Rep M FB.totalCoords, IsModularLatticeBasis M s.2 → lam ∈ w3_coset s →
      ¬ w3_pass FB M P s.1 → ∃ t, w3_cut FB M P s t ∧ lam ∈ w3_coset t)
    (k : ℕ) (s : w3_Rep M FB.totalCoords) (hs : IsModularLatticeBasis M s.2)
    (hl : lam ∈ w3_coset s) (hc : Nat.card (w3_coset s) ≤ 2^k) :
    ∃ n ≤ k, ∃ t, w3_Cuts FB M P n s t ∧ w3_pass FB M P t.1 := by
  classical
  induction k generalizing s with
  | zero =>
    letI : Nonempty (w3_coset s) := ⟨⟨lam,hl⟩⟩
    have pos := Nat.card_pos (α := w3_coset s)
    have eq1 : Nat.card (w3_coset s) = 1 := by rw [pow_zero] at hc; omega
    letI := (Nat.card_eq_one_iff_unique.mp eq1).1
    have he : s.1 = lam := congrArg Subtype.val (Subsingleton.elim (⟨s.1,w3_rep_mem s⟩ : w3_coset s) ⟨lam,hl⟩)
    exact ⟨0,le_rfl,s,.nil s,he.symm ▸ hlp⟩
  | succ k ih =>
    by_cases hp : w3_pass FB M P s.1
    · exact ⟨0,Nat.zero_le _,s,.nil s,hp⟩
    obtain ⟨t,ht,hlt⟩ := step s hs hl hp
    obtain ⟨_,_,_,_,_,hu,hh⟩ := id ht
    have hct : Nat.card (w3_coset t) ≤ 2^k := by rw [pow_succ] at hc; omega
    obtain ⟨n,hn,u,hw,hpu⟩ := ih t hu.1 hlt hct
    exact ⟨n+1,Nat.succ_le_succ hn,u,.cons ht hw,hpu⟩

theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (M : ℕ) [NeZero M] (hM : 2 ≤ M) (P Q : G) (e : G ≃+ ZMod M) (hP : e P = 1)
    {m : ℕ} (hm : 2 ≤ m) (FB : IndexedFactorBase G m)
    (cover : ∀ g : G, ∃ X : FB.BlockTuple, FB.tupleVal X = g)
    (U : Fin FB.totalCoords → FB.BlockTuple) (hU : ∀ j, FB.tupleVal (U j) = FB.elem P Q j) :
    (∃ y, w3_Outcome FB M P U y) ∧
    ∀ y, w3_Outcome FB M P U y → (∀ j, y j = e (FB.elem P Q j)) ∧
      (y FB.targetCoord).val < M ∧ (y FB.targetCoord).val • P = Q := by
  classical
  let lam : w3_Label M FB.totalCoords := fun j => e (FB.elem P Q j)
  have hlam (j) : (lam j).val • P = FB.elem P Q j := by
    apply e.injective; simp [hP,nsmul_eq_mul, ZMod.natCast_zmod_val,lam]
  have htarget : FB.elem P Q FB.targetCoord = Q := by simp [IndexedFactorBase.elem,IndexedFactorBase.targetCoord]
  have hgen : FB.elem P Q FB.genCoord = P := by simp [IndexedFactorBase.elem,IndexedFactorBase.genCoord]
  have hsum (T : FB.BlockTuple) : ((FB.tupleLabelSum M lam T : ℤ) : ZMod M) = e (FB.tupleVal T) := by
    unfold IndexedFactorBase.tupleLabelSum; rw [w3_sum_slots]; push_cast
    simp [IndexedFactorBase.tupleVal,Fin.sum_univ_two,lam,w3_elem_slot,ZMod.natCast_zmod_val]
  have hli : FB.SatisfiesInitialCongruences M U lam := ⟨by simp [lam,hgen,hP],fun j => by rw [hsum,hU]⟩
  have hlp : w3_pass FB M P lam := by
    intro X Y h; rw [w3_row_eq]; simp [w3_delta,hsum,h,map_add,hP]
  have hN : 1 ≤ FB.totalCoords := by unfold IndexedFactorBase.totalCoords; omega
  constructor
  · obtain ⟨s,hi,hs,hl⟩ := w3_init_exists hM hN (w3_initRows FB M U) (w3_full M _) lam w3_basis_full (w3_in_full lam) ((w3_init_iff FB M U lam).2 hli)
    have step (v : w3_Rep M FB.totalCoords) (hb : IsModularLatticeBasis M v.2) (hlv : lam ∈ w3_coset v) (hp : ¬ w3_pass FB M P v.1) : ∃ t, w3_cut FB M P v t ∧ lam ∈ w3_coset t := by
      unfold w3_pass at hp; push Not at hp; obtain ⟨X,Y,hy,hbad⟩ := hp
      let r := w3_shiftRow FB M X Y
      have hgood : w3_holds r lam := hlp X Y hy
      obtain ⟨t,hu,hh⟩ := w3_update_exists hM hN v r hb ⟨lam,hlv,hgood⟩
      obtain ⟨h0,hz,_,_⟩ := lemma_4_2_newton_binomial_filter (2*m) M (by omega) hM
      let d := w3_delta FB M v.1 X Y
      obtain ⟨hd1,hd2⟩ := w3_delta_range FB M v.1 X Y
      have hn : (filterPoly (2*m) M).eval d ≠ 0 := by
        intro h; apply hbad; apply (w3_row_eq FB M _ _ _).2
        have he := (ZMod.intCast_eq_intCast_iff d 1 M).2 ((hz d (by simpa only [neg_mul] using hd1) hd2).1 h)
        simpa only [Int.cast_one] using he
      exact ⟨t,⟨X,Y,hy,lt_of_le_of_ne (h0 d) (Ne.symm hn),hbad,hu,hh hbad⟩,hu.2.symm ▸ ⟨hlv,hgood⟩⟩
    obtain ⟨n,hn,t,hc,hpass⟩ := w3_fuel FB P lam hlp step (Nat.clog 2 (M ^ FB.totalCoords)) s hs hl
      ((w3_card_bound s).trans (Nat.le_pow_clog (by decide) _))
    exact ⟨t.1,s,t,n,hi,hc,hn,rfl,hpass⟩
  · rintro y ⟨s,t,n,hi,hc,_,rfl,hpass⟩
    have hyn := ((w3_init_exact hi t.1).1 ((w3_cuts_subset hc) (w3_rep_mem t))).2
    have hcard : Fintype.card G = M := (Fintype.card_congr e.toEquiv).trans (ZMod.card M)
    have hord : addOrderOf P = M := by rw [← e.addOrderOf_eq P,hP,ZMod.addOrderOf_one]
    have heq := proposition_4_1_fixed_shift_soundness M hM hcard P Q hord FB cover U hU lam hlam t.1
      ((w3_init_iff FB M U t.1).1 hyn) (fun X Y h => (w3_row_eq FB M _ _ _).1 (hpass X Y h))
    exact ⟨heq,(t.1 FB.targetCoord).val_lt,by rw [heq]; exact (hlam _).trans htarget⟩
