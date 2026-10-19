-- Prove2me | solution 1 for BBCode.new360_support_right_companion322
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:27:20.320457+00:00
-- url     : https://prove2.me/submissions/3bdc4aa5-71f9-42f3-8804-77a5cc70e022

import Definitions.Def_BBCode_Setting
open Matrix
namespace BBNew360Split_right_companion322
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BBNew360Cert

def entry {r : ℕ} (v : BitVec r) (i : Fin r) : ZMod 2 :=
  if v.getLsbD i.val then 1 else 0

lemma entry_xor {r : ℕ} (v w : BitVec r) (i : Fin r) :
    entry (v ^^^ w) i = entry v i + entry w i := by
  simp only [entry, BitVec.getLsbD_xor]
  cases v.getLsbD i.val <;> cases w.getLsbD i.val <;> decide

lemma entry_injective {r : ℕ} : Function.Injective (entry (r := r)) := by
  intro v w h
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi := congrFun h (⟨k,hk⟩ : Fin r)
  unfold entry at hi
  cases hv : v.getLsbD k <;> cases hw : w.getLsbD k <;> simp_all

def signature {r n : ℕ} (C : Fin n → BitVec r) (l : List (Fin n)) : BitVec r :=
  l.foldr (fun j a => C j ^^^ a) 0

lemma signature_entry {r n : ℕ} (C : Fin n → BitVec r) (l : List (Fin n))
    (hl : l.Nodup) (i : Fin r) : entry (signature C l) i = ∑ j ∈ l.toFinset, entry (C j) i := by
  induction l with
  | nil => simp [signature, entry]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    simp only [signature, List.foldr_cons, entry_xor]
    rw [show l.foldr (fun j a => C j ^^^ a) 0 = signature C l from rfl, ih hl]
    simp [ha]

def smallLists (n : ℕ) : List (List (Fin n)) :=
  (List.range 5).flatMap fun k => (List.finRange n).sublistsLen k

lemma represent {n : ℕ} (s : Finset (Fin n)) (hs : s.card ≤ 4) :
    ∃ l ∈ smallLists n, l.Nodup ∧ l.toFinset = s := by
  let l := (List.finRange n).filter (fun j => j ∈ s)
  have hl : l.Nodup := (List.nodup_finRange n).filter _
  have he : l.toFinset = s := by ext j; simp [l]
  have hlen : l.length = s.card := by rw [← he, List.toFinset_card_of_nodup hl]
  refine ⟨l, ?_, hl, he⟩
  apply List.mem_flatMap.mpr
  refine ⟨l.length, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_sublistsLen_self List.filter_sublist

abbrev Item (r : ℕ) := ℕ × BitVec r

def rel {r : ℕ} (a b : Item r) : Prop := a.1 < b.1 ∨ a = b
instance {r : ℕ} : DecidableRel (rel (r := r)) := fun a b =>
  if h : a.1 < b.1 then isTrue (Or.inl h)
  else if e : a = b then isTrue (Or.inr e)
  else isFalse (by intro he; exact he.elim h e)
instance {r : ℕ} : IsTrans (Item r) rel where
  trans a b c hab hbc := by
    rcases hab with hab | rfl <;> rcases hbc with hbc | rfl
    · exact Or.inl (hab.trans hbc)
    · exact Or.inl hab
    · exact Or.inl hbc
    · exact Or.inr rfl

def check {r : ℕ} : List (Item r) → Bool
  | a :: b :: l => if rel a b then check (b :: l) else false
  | _ => true

lemma check_sound {r : ℕ} (l : List (Item r)) (h : check l = true) : l.IsChain rel := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons a l ih =>
    cases l with
    | nil => exact List.IsChain.singleton a
    | cons b l =>
      simp only [check] at h
      split at h
      · exact List.isChain_cons_cons.mpr ⟨by assumption, ih h⟩
      · contradiction

lemma chain_unique {r : ℕ} {l : List (Item r)} (h : l.IsChain rel) :
    ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2 := by
  have hp := List.isChain_iff_pairwise.mp h
  clear h
  induction hp with
  | nil => simp
  | @cons c l hc ht ih =>
    intro a ha b hb he
    by_cases hac : a = c
    · subst a
      by_cases hbc : b = c
      · subst b; rfl
      · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
        rcases hc _ hb' with hh | hh
        · exact False.elim (by omega)
        · exact congrArg Prod.snd hh
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left hac
      by_cases hbc : b = c
      · subst b
        rcases hc _ ha' with hh | hh
        · exact False.elim (by omega)
        · exact (congrArg Prod.snd hh).symm
      · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
        exact ih a ha' b hb' he

def item {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (l : List (Fin n)) : Item k := ((signature C l).toNat, signature K l)

def rawItems {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k) : List (Item k) :=
  (List.range 5).flatMap fun j =>
    List.sublistsLenAux j (List.finRange n) (item C K) []

lemma rawItems_eq {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k) :
    rawItems C K = (smallLists n).map (item C K) := by
  simp [rawItems, smallLists, List.map_flatMap, List.sublistsLenAux_eq]

def sortedItems {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k) : List (Item k) :=
  (rawItems C K).mergeSort (fun a b => a.1 ≤ b.1)

lemma small_unique {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (hc : (sortedItems C K).IsChain rel)
    {s t : Finset (Fin n)} (hs : s.card ≤ 4) (ht : t.card ≤ 4)
    (he : (fun i => ∑ j ∈ s, entry (C j) i) = (fun i => ∑ j ∈ t, entry (C j) i)) :
    (fun i => ∑ j ∈ s, entry (K j) i) = (fun i => ∑ j ∈ t, entry (K j) i) := by
  obtain ⟨a,ha,hna,rfl⟩ := represent s hs
  obtain ⟨b,hb,hnb,rfl⟩ := represent t ht
  have hs : signature C a = signature C b := by
    apply entry_injective
    ext i
    simpa [signature_entry C a hna, signature_entry C b hnb] using congrFun he i
  have hm (l : List (Fin n)) (hl : l ∈ smallLists n) : item C K l ∈ sortedItems C K := by
    simp only [sortedItems, rawItems_eq, List.mem_mergeSort]
    exact List.mem_map.mpr ⟨l,hl,rfl⟩
  have h := chain_unique hc _ (hm a ha) _ (hm b hb) (by simp [item,hs])
  change signature K a = signature K b at h
  ext i
  simpa [signature_entry K a hna, signature_entry K b hnb] using congrArg (fun v => entry v i) h

lemma binary_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hx : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  exact (hx x).resolve_left h

lemma support_mul {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (i : Fin r) :
    (H *ᵥ v) i = ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), H i j := by
  change ∑ j, H i j * v j = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : v j = 0
  · simp [h]
  · simp [binary_eq_one h]

lemma kernel_even {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (hc : ∀ j, ∑ i, H i j = 1) (v : Fin n → ZMod 2) (hv : H *ᵥ v = 0) :
    2 ∣ weight v := by
  let s := Finset.univ.filter fun j => v j ≠ 0
  apply (ZMod.natCast_eq_zero_iff _ 2).mp
  change (s.card : ZMod 2) = 0
  calc
    (s.card : ZMod 2) = ∑ j ∈ s, (1 : ZMod 2) := by simp
    _ = ∑ j ∈ s, ∑ i, H i j := by simp_rw [hc]
    _ = ∑ i, ∑ j ∈ s, H i j := Finset.sum_comm
    _ = 0 := by
      have he (i) : ∑ j ∈ s, H i j = 0 := by
        rw [← support_mul H v i, hv]; rfl
      simp_rw [he]; simp

lemma split_support {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card ≤ 8) :
    ∃ a b : Finset α, a.card ≤ 4 ∧ b.card ≤ 4 ∧ Disjoint a b ∧ a ∪ b = s := by
  obtain ⟨a,ha,hac⟩ := Finset.exists_subset_card_eq (show min s.card 4 ≤ s.card from min_le_left _ _)
  refine ⟨a,s \ a, ?_, ?_, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset ha⟩
  · omega
  · rw [Finset.card_sdiff_of_subset ha]; omega

lemma small_kernel {r k n : ℕ} (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (hc : (sortedItems C K).IsChain rel) (v : Fin n → ZMod 2)
    (hv : (Matrix.of fun i j => entry (C j) i) *ᵥ v = 0) (hw : weight v ≤ 8) :
    (Matrix.of fun i j => entry (K j) i) *ᵥ v = 0 := by
  let s := Finset.univ.filter fun j => v j ≠ 0
  obtain ⟨a,b,ha,hb,hab,hs⟩ := split_support s hw
  have hz (i) : ∑ j ∈ a, entry (C j) i + ∑ j ∈ b, entry (C j) i = 0 := by
    rw [← Finset.sum_union hab, hs]
    change ∑ j ∈ (Finset.univ.filter fun j => v j ≠ 0), (Matrix.of fun i j => entry (C j) i) i j = 0
    rw [← support_mul _ v i, hv]; rfl
  have he : (fun i => ∑ j ∈ a, entry (C j) i) = (fun i => ∑ j ∈ b, entry (C j) i) := by
    funext i
    exact (eq_neg_of_add_eq_zero_left (hz i)).trans (ZMod.neg_eq_self_mod_two _)
  have hk := small_unique C K hc ha hb he
  funext i
  change ((Matrix.of fun i j => entry (K j) i) *ᵥ v) i = 0
  rw [support_mul]
  change ∑ j ∈ s, entry (K j) i = 0
  rw [← hs, Finset.sum_union hab]
  have hi := congrFun hk i
  rw [hi]
  exact (eq_neg_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two _).symm)

lemma transpose_mulVec_mem {r n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (u : Fin r → ZMod 2) : H.transpose *ᵥ u ∈ rowSpace H := by
  have he : H.transpose *ᵥ u = ∑ i, u i • H i := by
    funext j
    simp [mulVec, dotProduct, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

lemma kernel_mem_row {r k n : ℕ} (H : Matrix (Fin r) (Fin n) (ZMod 2))
    (D : Matrix (Fin r) (Fin n) (ZMod 2)) (K : Matrix (Fin k) (Fin n) (ZMod 2))
    (E : Matrix (Fin n) (Fin k) (ZMod 2)) (h : H.transpose * D + E * K = 1) (v : Fin n → ZMod 2) (hv : K *ᵥ v = 0) :
    v ∈ rowSpace H := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) (ZMod 2) => M *ᵥ v) h
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at he
  rw [← he]
  exact transpose_mulVec_mem H (D *ᵥ v)

lemma rowspace_reindex {r c a b : Type} [Fintype c] [Fintype b]
    (H : Matrix r c (ZMod 2)) (er : a ≃ r) (ec : b ≃ c) (v : c → ZMod 2) :
    v ∘ ec ∈ rowSpace (H.submatrix er ec) ↔ v ∈ rowSpace H := by
  have forward {r c a b : Type} (H : Matrix r c (ZMod 2)) (er : a ≃ r) (ec : b ≃ c)
      (v : b → ZMod 2) (hv : v ∈ rowSpace (H.submatrix er ec)) :
      v ∘ ec.symm ∈ rowSpace H := by
    change v ∈ Submodule.span (ZMod 2) (Set.range (H.submatrix er ec)) at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i,rfl⟩ := hv
      apply Submodule.subset_span
      exact ⟨er i, by funext j; simp⟩
    | zero => exact Submodule.zero_mem _
    | add v w hv hw ihv ihw => exact Submodule.add_mem _ ihv ihw
    | smul k v hv ih => exact Submodule.smul_mem _ k ih
  constructor
  · intro h
    have hf := forward H er ec (v ∘ ec) h
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hf
  · intro h
    have he : (H.submatrix er ec).submatrix er.symm ec.symm = H := by ext i j; simp
    have hh : v ∈ rowSpace ((H.submatrix er ec).submatrix er.symm ec.symm) := by rwa [he]
    exact forward _ er.symm ec.symm v hh

end BBNew360Cert

set_option maxHeartbeats 0
open Matrix BBCode BBNew360Cert
namespace BBNew360Bits

def unit {n : ℕ} (j : Fin n) : BitVec n := (1 : BitVec n) <<< j.val

lemma unit_entry {n : ℕ} (j i : Fin n) : entry (unit j) i = if i = j then 1 else 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  by_cases h : i = j
  · subst i; simp [unit,entry,hn]
  · have hv : i.val ≠ j.val := by exact fun he => h (Fin.ext he)
    simp [unit,entry,hn,h]
    omega

def combination {r n : ℕ} (rows : Fin r → BitVec n) (c : BitVec r) : BitVec n :=
  (List.finRange r).foldr (fun i v => if c.getLsbD i.val then rows i ^^^ v else v) 0

lemma combination_entry {r n : ℕ} (rows : Fin r → BitVec n) (c : BitVec r) (j : Fin n) :
    entry (combination rows c) j = ∑ i, entry c i * entry (rows i) j := by
  have aux (l : List (Fin r)) :
      entry (l.foldr (fun i v => if c.getLsbD i.val then rows i ^^^ v else v) 0) j =
        (l.map (fun i => entry c i * entry (rows i) j)).sum := by
    induction l with
    | nil => simp [entry]
    | cons a l ih =>
      simp only [List.foldr_cons,List.map_cons,List.sum_cons]
      cases he : c.getLsbD a.val with
      | false =>
        rw [if_neg (by decide),ih]
        have ha : entry c a = 0 := by dsimp only [entry]; rw [he]; rfl
        rw [ha,zero_mul,zero_add]
      | true =>
        rw [if_pos (by decide),entry_xor,ih]
        have ha : entry c a = 1 := by dsimp only [entry]; rw [he]; rfl
        rw [ha,one_mul]
  rw [combination,aux]
  simp [← List.ofFn_eq_map,List.sum_ofFn]

lemma product {a b c : ℕ} (A : Fin a → BitVec b) (B : Fin b → BitVec c)
    (D : Fin a → BitVec c) (h : ∀ i, combination B (A i) = D i) :
    (Matrix.of fun i j => entry (A i) j) * (Matrix.of fun i j => entry (B i) j) =
      (Matrix.of fun i j => entry (D i) j) := by
  apply Matrix.ext
  intro i j
  change ∑ k, entry (A i) k * entry (B k) j = entry (D i) j
  rw [← combination_entry,h]

lemma decomposition {r n : ℕ} (rows : Fin r → BitVec n) (coeff : Fin n → BitVec r)
    (rem : Fin n → BitVec n)
    (h : ∀ j, combination rows (coeff j) ^^^ rem j = unit j) :
    (Matrix.of fun i j => entry (rows i) j).transpose *
        (Matrix.of fun i j => entry (coeff j) i) +
      (Matrix.of fun i j => entry (rem j) i) = 1 := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun v => entry v i) (h j)
  rw [entry_xor,combination_entry,unit_entry] at he
  change ∑ k, entry (rows k) i * entry (coeff j) k + entry (rem j) i = _
  simpa only [Matrix.one_apply,mul_comm] using he
end BBNew360Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BBNew360Cert BBNew360Bits
namespace BBNew360KernelData
def xmask (j : Fin 360) : BitVec 180 := BitVec.ofNat 180 (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 383123885216472214589586756787577295904684781082771457 else 766247770432944429179173513575154591809369561091801091) else (if j.val < 3 then 1427247692705959881058285969449495136382746630 else (if j.val < 4 then 2854495385411919762116571938898990272765493260 else 5708990770823839524233143877797980545530986520))) else (if j.val < 8 then (if j.val < 6 then 11417981541647679048466287755595961091061973040 else (if j.val < 7 then 22835963083295358096932575511191922182123946080 else 45671926166590716193865151022383844364247892160)) else (if j.val < 9 then 91343852333181432387730302044767688728495784320 else (if j.val < 10 then 182687704666362864775460604089535377456991568640 else 365375409332725729550921208179070754913983137280)))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then 730750818665451459101842416358141509827966274560 else 1461501637330902918203684832716283019655932549120) else (if j.val < 14 then 2923003274661805836407369665432566039311865098240 else (if j.val < 15 then 5846006549323611672814739330865132078623730196480 else 11692013098647223345629478661730264157247460392960))) else (if j.val < 19 then (if j.val < 17 then 23384026197294446691258957323460528314494920785920 else (if j.val < 18 then 46768052394588893382517914646921056628989841571840 else 93536104789177786765035829293842113257979683143680)) else (if j.val < 20 then 187072209578355573530071658587684226515959366287360 else (if j.val < 21 then 374144419156711147060143317175368453031918732574720 else 748288838313422294120286634350736906063837465149440))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then 1496577676626844588240573268701473812127674930298880 else 2993155353253689176481146537402947624255349860597760) else (if j.val < 25 then 5986310706507378352962293074805895248510699721195520 else (if j.val < 26 then 11972621413014756705924586149611790497021399442391040 else 23945242826029513411849172299223580994042798884782080))) else (if j.val < 30 then (if j.val < 28 then 47890485652059026823698344598447161988085597769564160 else (if j.val < 29 then 95780971304118053647396689196894323976171195539128320 else 191561942608236107294793378393788647952342391078256640)) else (if j.val < 31 then 576460753645600768 else (if j.val < 32 then 3758096384 else 6442450945)))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then 12884901890 else (if j.val < 35 then 25769803780 else 51539607560)) else (if j.val < 37 then 103079215120 else (if j.val < 38 then 206158430240 else 412316860480))) else (if j.val < 42 then (if j.val < 40 then 824633720960 else (if j.val < 41 then 1649267441920 else 3298534883840)) else (if j.val < 43 then 6597069767680 else (if j.val < 44 then 13194139535360 else 26388279070720)))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then 52776558141440 else 105553116282880) else (if j.val < 48 then 211106232565760 else (if j.val < 49 then 422212465131520 else 844424930263040))) else (if j.val < 53 then (if j.val < 51 then 1688849860526080 else (if j.val < 52 then 3377699721052160 else 6755399442104320)) else (if j.val < 54 then 13510798884208640 else (if j.val < 55 then 27021597768417280 else 54043195536834560)))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then 108086391073669120 else 216172782147338240) else (if j.val < 59 then 432345564294676480 else (if j.val < 60 then 864691128589352960 else 618970021083842018208120832))) else (if j.val < 64 then (if j.val < 62 then 4035225266123964416 else (if j.val < 63 then 6917529028714823680 else 13835058057429647360)) else (if j.val < 65 then 27670116114859294720 else (if j.val < 66 then 55340232229718589440 else 110680464459437178880))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then 221360928918874357760 else 442721857837748715520) else (if j.val < 70 then 885443715675497431040 else (if j.val < 71 then 1770887431350994862080 else 3541774862701989724160))) else (if j.val < 75 then (if j.val < 73 then 7083549725403979448320 else (if j.val < 74 then 14167099450807958896640 else 28334198901615917793280)) else (if j.val < 76 then 56668397803231835586560 else (if j.val < 77 then 113336795606463671173120 else 226673591212927342346240)))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then 453347182425854684692480 else (if j.val < 80 then 906694364851709369384960 else 1813388729703418738769920)) else (if j.val < 82 then 3626777459406837477539840 else (if j.val < 83 then 7253554918813674955079680 else 14507109837627349910159360))) else (if j.val < 87 then (if j.val < 85 then 29014219675254699820318720 else (if j.val < 86 then 58028439350509399640637440 else 116056878701018799281274880)) else (if j.val < 88 then 232113757402037598562549760 else (if j.val < 89 then 464227514804075197125099520 else 928455029608150394250199040))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then 664613999439882985558628873764077568 else 4332790137498830962146934784) else (if j.val < 93 then 7427640236865203154001592320 else (if j.val < 94 then 14855280473730406308003184640 else 29710560947460812616006369280))) else (if j.val < 98 then (if j.val < 96 then 59421121894921625232012738560 else (if j.val < 97 then 118842243789843250464025477120 else 237684487579686500928050954240)) else (if j.val < 99 then 475368975159373001856101908480 else (if j.val < 100 then 950737950318746003712203816960 else 1901475900637492007424407633920)))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then 3802951801274984014848815267840 else 7605903602549968029697630535680) else (if j.val < 104 then 15211807205099936059395261071360 else (if j.val < 105 then 30423614410199872118790522142720 else 60847228820399744237581044285440))) else (if j.val < 109 then (if j.val < 107 then 121694457640799488475162088570880 else (if j.val < 108 then 243388915281598976950324177141760 else 486777830563197953900648354283520)) else (if j.val < 110 then 973555661126395907801296708567040 else (if j.val < 111 then 1947111322252791815602593417134080 else 3894222644505583631205186834268160))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then 7788445289011167262410373668536320 else 15576890578022334524820747337072640) else (if j.val < 115 then 31153781156044669049641494674145280 else (if j.val < 116 then 62307562312089338099282989348290560 else 124615124624178676198565978696581120))) else (if j.val < 120 then (if j.val < 118 then 249230249248357352397131957393162240 else (if j.val < 119 then 498460498496714704794263914786324480 else 996920996993429409588527829572648960)) else (if j.val < 121 then 713623848014514935260287825854506393541804032 else (if j.val < 122 then 4652297985247205555163324710981206016 else 7975367975947435276708222636581191680)))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then 15950735951894870553416445273162383360 else (if j.val < 125 then 31901471903789741106832890546324766720 else 63802943807579482213665781092649533440)) else (if j.val < 127 then 127605887615158964427331562185299066880 else (if j.val < 128 then 255211775230317928854663124370598133760 else 510423550460635857709326248741196267520))) else (if j.val < 132 then (if j.val < 130 then 1020847100921271715418652497482392535040 else (if j.val < 131 then 2041694201842543430837304994964785070080 else 4083388403685086861674609989929570140160)) else (if j.val < 133 then 8166776807370173723349219979859140280320 else (if j.val < 134 then 16333553614740347446698439959718280560640 else 32667107229480694893396879919436561121280)))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then 65334214458961389786793759838873122242560 else 130668428917922779573587519677746244485120) else (if j.val < 138 then 261336857835845559147175039355492488970240 else (if j.val < 139 then 522673715671691118294350078710984977940480 else 1045347431343382236588700157421969955880960))) else (if j.val < 143 then (if j.val < 141 then 2090694862686764473177400314843939911761920 else (if j.val < 142 then 4181389725373528946354800629687879823523840 else 8362779450747057892709601259375759647047680)) else (if j.val < 144 then 16725558901494115785419202518751519294095360 else (if j.val < 145 then 33451117802988231570838405037503038588190720 else 66902235605976463141676810075006077176381440)))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then 133804471211952926283353620150012154352762880 else 267608942423905852566707240300024308705525760) else (if j.val < 149 then 535217884847811705133414480600048617411051520 else (if j.val < 150 then 1070435769695623410266828961200097234822103040 else 766247772217004045061623364898012053621238481570234368))) else (if j.val < 154 then (if j.val < 152 then 4995366924470859583704000893073232977339613184 else (if j.val < 153 then 8563486157564987282134631689600777878576824320 else 17126972315129974564269263379201555757153648640)) else (if j.val < 155 then 34253944630259949128538526758403111514307297280 else (if j.val < 156 then 68507889260519898257077053516806223028614594560 else 137015778521039796514154107033612446057229189120))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 274031557042079593028308214067224892114458378240 else 548063114084159186056616428134449784228916756480) else (if j.val < 160 then 1096126228168318372113232856268899568457833512960 else (if j.val < 161 then 2192252456336636744226465712537799136915667025920 else 4384504912673273488452931425075598273831334051840))) else (if j.val < 165 then (if j.val < 163 then 8769009825346546976905862850151196547662668103680 else (if j.val < 164 then 17538019650693093953811725700302393095325336207360 else 35076039301386187907623451400604786190650672414720)) else (if j.val < 166 then 70152078602772375815246902801209572381301344829440 else (if j.val < 167 then 140304157205544751630493805602419144762602689658880 else 280608314411089503260987611204838289525205379317760)))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then 561216628822179006521975222409676579050410758635520 else (if j.val < 170 then 1122433257644358013043950444819353158100821517271040 else 2244866515288716026087900889638706316201643034542080)) else (if j.val < 172 then 4489733030577432052175801779277412632403286069084160 else (if j.val < 173 then 8979466061154864104351603558554825264806572138168320 else 17958932122309728208703207117109650529613144276336640))) else (if j.val < 177 then (if j.val < 175 then 35917864244619456417406414234219301059226288552673280 else (if j.val < 176 then 71835728489238912834812828468438602118452577105346560 else 143671456978477825669625656936877204236905154210693120)) else (if j.val < 178 then 287342913956955651339251313873754408473810308421386240 else (if j.val < 179 then 574685827913911302678502627747508816947620616842772480 else 1149371655827822605357005255495017633895241233685544960)))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then 21778071482940061661655974875633169727489 else 43556142965880123323311949751266339454978) else (if j.val < 183 then 87112285931760246646623899502532678909956 else (if j.val < 184 then 174224571863520493293247799005065357819912 else 348449143727040986586495598010130715639824))) else (if j.val < 188 then (if j.val < 186 then 696898287454081973172991196020261431279648 else (if j.val < 187 then 1393796574908163946345982392040522862559296 else 2787593149816327892691964784081045725118592)) else (if j.val < 189 then 5575186299632655785383929568162090376495361 else (if j.val < 190 then 11150372599265311570767859136324180752990722 else 22300745198530623141535718272648361505981444)))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then 44601490397061246283071436545296723011962888 else 89202980794122492566142873090593446023925776) else (if j.val < 194 then 178405961588244985132285746181186892047851552 else (if j.val < 195 then 356811923176489970264571492362373784095703104 else 713623846352979940529142984724747568191406208))) else (if j.val < 199 then (if j.val < 197 then 1329227995784915872903807060280410368 else (if j.val < 198 then 2658455991569831745807614120560820736 else 5316911983139663491615228241121641472)) else (if j.val < 200 then 10633823966279326983230456482243282944 else (if j.val < 201 then 21267647932558653966460912964486565888 else 42535295865117307932921825928973131776))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then 85070591730234615865843651857946263552 else 170141183460469231731687303715892527104) else (if j.val < 205 then 340282366920938463463374607431785054208 else (if j.val < 206 then 680564733841876926926749214863570108416 else 1361129467683753853853498429727140216832))) else (if j.val < 210 then (if j.val < 208 then 2722258935367507707706996859454280433664 else (if j.val < 209 then 5444517870735015415413993718908560867328 else 10889035741470030830827987437817121734656)) else (if j.val < 211 then 23384026197294446691258957323460532818095621799936 else (if j.val < 212 then 46768052394588893382517914646921065636191243599872 else 93536104789177786765035829293842131272382487199744)))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then 187072209578355573530071658587684262544764974399488 else (if j.val < 215 then 374144419156711147060143317175368525089529948798976 else 748288838313422294120286634350737050179059897597952)) else (if j.val < 217 then 1496577676626844588240573268701474100358119795195904 else (if j.val < 218 then 2993155353253689176481146537402948200716239590391808 else 5986310706507378352962293074805895248510975647678464))) else (if j.val < 222 then (if j.val < 220 then 11972621413014756705924586149611790497021951295356928 else (if j.val < 221 then 23945242826029513411849172299223580994043902590713856 else 47890485652059026823698344598447161988087805181427712)) else (if j.val < 223 then 95780971304118053647396689196894323976175610362855424 else (if j.val < 224 then 191561942608236107294793378393788647952351220725710848 else 383123885216472214589586756787577295904702441451421696)))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then 766247770432944429179173513575154591809404882902843392 else 1427247692705959881058285969449565780004831232) else (if j.val < 228 then 2854495385411919762116571938899131560009662464 else (if j.val < 229 then 5708990770823839524233143877798263120019324928 else 11417981541647679048466287755596526240038649856))) else (if j.val < 233 then (if j.val < 231 then 22835963083295358096932575511193052480077299712 else (if j.val < 232 then 45671926166590716193865151022386104960154599424 else 91343852333181432387730302044772209920309198848)) else (if j.val < 234 then 182687704666362864775460604089544419840618397696 else (if j.val < 235 then 365375409332725729550921208179088839681236795392 else 730750818665451459101842416358177679362473590784)))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then 1461501637330902918203684832716355358724947181568 else 2923003274661805836407369665432710717449894363136) else (if j.val < 239 then 5846006549323611672814739330865421434899788726272 else (if j.val < 240 then 11692013098647223345629478661730842869799577452544 else 4835704431380021305688064))) else (if j.val < 244 then (if j.val < 242 then 9671408862760042611376128 else (if j.val < 243 then 19342817725520085222752256 else 38685635451040170445504512)) else (if j.val < 245 then 77371270902080340891009024 else (if j.val < 246 then 154742541804160681782018048 else 309485083608321363564036096))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then 618970167216642727128072192 else 296300826683963867136) else (if j.val < 250 then 592601653367927734272 else (if j.val < 251 then 1185203306735855468544 else 2370406613471710937088))) else (if j.val < 255 then (if j.val < 253 then 4740813226943421874176 else (if j.val < 254 then 9481626453886843748352 else 18963252907773687496704)) else (if j.val < 256 then 37926505815547374993408 else (if j.val < 257 then 75853011631093676244993 else 151706023262187352489986)))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then 303412046524374704979972 else (if j.val < 260 then 606824093048749409959944 else 1213648186097498819919888)) else (if j.val < 262 then 2427296372194997639839776 else (if j.val < 263 then 4854592744389995279679552 else 9709185488779990559359104))) else (if j.val < 267 then (if j.val < 265 then 19418370977559981118718208 else (if j.val < 266 then 38836741955119962237436416 else 77673483910239924474872832)) else (if j.val < 268 then 155346967820479848949745664 else (if j.val < 269 then 310693935640959697899491328 else 621387871281919395798982656))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then 5192298096474866913928363414388736 else 10384596192949733827856726828777472) else (if j.val < 273 then 20769192385899467655713453657554944 else (if j.val < 274 then 41538384771798935311426907315109888 else 83076769543597870622853814630219776))) else (if j.val < 278 then (if j.val < 276 then 166153539087195741245707629260439552 else (if j.val < 277 then 332307078174391482491415258520879104 else 664614156348782964982830517041758208)) else (if j.val < 279 then 318150590096347234248702296064 else (if j.val < 280 then 636301180192694468497404592128 else 1272602360385388936994809184256)))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then 2545204720770777873989618368512 else 5090409441541555747979236737024) else (if j.val < 284 then 10180818883083111495958473474048 else (if j.val < 285 then 20361637766166222991916946948096 else 40723275532332445983833893896192))) else (if j.val < 289 then (if j.val < 287 then 81446551064663739046164254687232 else (if j.val < 288 then 162893102129327478092328509374464 else 325786204258654956184657018748928)) else (if j.val < 290 then 651572408517309912369314037497856 else (if j.val < 291 then 1303144817034619824738628074995712 else 2606289634069239649477256149991424))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then 5212579268138479298954512299982848 else 10425158536276958597909024599965696) else (if j.val < 295 then 20850317072553917195818049199931392 else (if j.val < 296 then 41700634145107834391636098399862784 else 83401268290215668783272196799725568))) else (if j.val < 300 then (if j.val < 298 then 166802536580431337566544393599451136 else (if j.val < 299 then 333605073160862675133088787198902272 else 667210146321725350266177574397804544)) else (if j.val < 301 then 5575187628860651570318691937900629237694464 else (if j.val < 302 then 11150375257721303140637383875801258475388928 else 22300750515442606281274767751602516950777856)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then 44601501030885212562549535503205033901555712 else (if j.val < 305 then 89203002061770425125099071006410067803111424 else 178406004123540850250198142012820135606222848)) else (if j.val < 307 then 356812008247081700500396284025640271212445696 else (if j.val < 308 then 713624016494163401000792568051280542424891392 else 341611594916728215039556873008747380736))) else (if j.val < 312 then (if j.val < 310 then 683223189833456430079113746017494761472 else (if j.val < 311 then 1366446379666912860158227492034989522944 else 2732892759333825720316454984069979045888)) else (if j.val < 313 then 5465785518667651440632909968139958091776 else (if j.val < 314 then 10931571037335302881265819936279916183552 else 21863142074670605762531639872559832367104)))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 43726284149341211525063279745119664734208 else 87452568298681185110088427031469037191168) else (if j.val < 318 then 174905136597362370220176854062938074382336 else (if j.val < 319 then 349810273194724740440353708125876148764672 else 699620546389449480880707416251752297529344))) else (if j.val < 323 then (if j.val < 321 then 1399241092778898961761414832503504595058688 else (if j.val < 322 then 2798482185557797923522829665007009190117376 else 5596964371115595847045659330014018380234752)) else (if j.val < 324 then 11193928742231191694091318660028036760469504 else (if j.val < 325 then 22387857484462383388182637320056073520939008 else 44775714968924766776365274640112147041878016)))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then 89551429937849533552730549280224294083756032 else 179102859875699067105461098560448588167512064) else (if j.val < 329 then 358205719751398134210922197120897176335024128 else (if j.val < 330 then 716411439502796268421844394241794352670048256 else 5986312133755071058942456542695516368429783330062336))) else (if j.val < 334 then (if j.val < 332 then 11972624267510142117884913085391032736859566660124672 else (if j.val < 333 then 23945248535020284235769826170782065473719133320249344 else 47890497070040568471539652341564130947438266640498688)) else (if j.val < 335 then 95780994140081136943079304683128261894876533280997376 else (if j.val < 336 then 191561988280162273886158609366256523789753066561994752 else 383123976560324547772317218732513047579506133123989504))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then 766247953120649095544634437465026095159012266247979008 else 366802657025436881728838028976148780546695102464) else (if j.val < 340 then 733605314050873763457676057952297561093390204928 else (if j.val < 341 then 1467210628101747526915352115904595122186780409856 else 2934421256203495053830704231809190244373560819712))) else (if j.val < 345 then (if j.val < 343 then 5868842512406990107661408463618380488747121639424 else (if j.val < 344 then 11737685024813980215322816927236760977494243278848 else 23475370049627960430645633854473521954988486557696)) else (if j.val < 346 then 46950740099255920861291267708947043909976973115392 else (if j.val < 347 then 93901480198510512494587988442060469393168565010432 else 187802960397021024989175976884120938786337130020864)))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then 375605920794042049978351953768241877572674260041728 else (if j.val < 350 then 751211841588084099956703907536483755145348520083456 else 1502423683176168199913407815072967510290697040166912)) else (if j.val < 352 then 3004847366352336399826815630145935020581394080333824 else (if j.val < 353 then 6009694732704672799653631260291870041162788160667648 else 12019389465409345599307262520583740082325576321335296))) else (if j.val < 357 then (if j.val < 355 then 24038778930818691198614525041167480164651152642670592 else (if j.val < 356 then 48077557861637382397229050082334960329302305285341184 else 96155115723274764794458100164669920658604610570682368)) else (if j.val < 358 then 192310231446549529588916200329339841317209221141364736 else (if j.val < 359 then 384620462893099059177832400658679682634418442282729472 else 769240925786198118355664801317359365268836884565458944)))))))))
def xrow (i : Fin 180) : BitVec 360 := BitVec.ofNat 360 (if i.val < 90 then (if i.val < 45 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 115792089237316195423964836362690441289868079851618193499647599962318610366467 else 231584178474632390847929672725380882579736159703236386999295199924637220732934) else (if i.val < 3 then 463168356949264781695859345450761765159472319406472773998590399849274441465868 else (if i.val < 4 then 926336713898529563391718690901523530318944638812945547997180799698548882931736 else 1852673427797059126783437381803047060637889277625891095994361599397097765863472))) else (if i.val < 8 then (if i.val < 6 then 3705346855594118253566874763606094121275778555251782191988723198794195531726944 else (if i.val < 7 then 7410693711188236507133749527212188242551557110503564383977446397588391063453888 else 14821387422376473014267499054424376485103114221007128767954892795176782126907776)) else (if i.val < 9 then 29642774844752946028534998108848752970206228442014257535909785590353564253815552 else (if i.val < 10 then 59285549689505892057069996217697505940412456884028515071819571180707128507631104 else 118571099379011784114139992435395011880824913768057030143639142361414257015262208)))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then 237142198758023568228279984870790023761649827536114060287278284722828514030524416 else 474284397516047136456559969741580047523299655072228120574556569445657028061048832) else (if i.val < 14 then 948568795032094272913119939483160095046599310144456241149113138891314056122097664 else (if i.val < 15 then 1766847064784837190167275008568141707354541377951372179518585597516103680 else 3533694129569674380334550017136283414709082755902744359037171195032207360))) else (if i.val < 19 then (if i.val < 17 then 7067388259139348760669100034272566829418165511805488718074342390064414720 else (if i.val < 18 then 14134776518278697521338200068545133658836331023610977436148684780128829440 else 28269553036557395042676400137090267317672662047221954872297369560257658880)) else (if i.val < 20 then 56539106073114790085352800274180534635345324094443909744594739120515317760 else (if i.val < 21 then 113078212146229580170705600548361069270690648188887819489189478241030635520 else 226156424292459160341411201096722138541381296377775638978378956482061271040))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then 452312848583272816127033691692155196758563589277718851274743072222957535232 else 904625697166545632254067383384310393517127178555437702549486144445915070464) else (if i.val < 25 then 1809251394333091264508134766768620787034254357110875405098972288891830140928 else (if i.val < 26 then 3618502788666182529016269533537241574068508714221750810197944577783660281856 else 7237005577332365058032539067074483148137017428443501620395889155567320563712))) else (if i.val < 30 then (if i.val < 28 then 14474011154664730116065078134148966296274034856887003240791778311134641127424 else (if i.val < 29 then 28948022309329460232130156268297932592548069713774006481582403700765749149696 else 57896044618658920464260312536595865185096139427548012963164807401530424557569)) else (if i.val < 31 then 124330809102446660539268456707936759977947864779254168439896557340762315964035585015808 else (if i.val < 32 then 248661618204893321078536913415873519955895729558508336879793114681524631928071170031616 else 497323236409786642157073826831747039911791459117016673759586229363049263856142340063232)))) else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then 994646472819573284314147653663494079823582918234033347519172458726098527712284680126464 else (if i.val < 35 then 1989292945639146568628295307326988159647165836468066695038344917452197055424569360252928 else 3978585891278293137256590614653976319294331672936133390076689834904394110849138720505856)) else (if i.val < 37 then 7957171782556586274513181229307952638588663345872266780153379669808788221698277441011712 else (if i.val < 38 then 15914343565113172549026362458615905277177326691744533560306759339617576443396554882023424 else 31828687130226345098052724917231810554354653383489067120613518679235152886793109764046848))) else (if i.val < 42 then (if i.val < 40 then 63657374260452690196105449834463621108709306766978134241227037358470305773586219528093696 else (if i.val < 41 then 127314748520905380392210899668927242217418613533956268482454074716940611547172439056187392 else 254629497041810760784421799337854484434837227067912536964908149433881223094344878112374784)) else (if i.val < 43 then 509258994083621521568843598675708968869674454135825073929816298867762446188689756224749568 else (if i.val < 44 then 1018517988167243043137687197351417937739348908271650147859632597735524892377379512449499136 else 1897137590071117252113244732809572105145339473844979747339141541377071034736312320)))))) else (if i.val < 67 then (if i.val < 56 then (if i.val < 50 then (if i.val < 47 then (if i.val < 46 then 3794275180142234504226489465619144210290678947689959494678283082754142069472624640 else 7588550360284469008452978931238288420581357895379918989356566165508284138945249280) else (if i.val < 48 then 15177100720568938016905957862476576841162715790759837978713132331016568277890498560 else (if i.val < 49 then 30354201441137876033811915724953153682325431581519675957426264662033136555780997120 else 60708402882275752067623831449906307364650863163039351914852529324066273111561994240))) else (if i.val < 53 then (if i.val < 51 then 121416805764551504135247662899812614729301726326078703829705058648132546223123988480 else (if i.val < 52 then 242833611529103008270495325799625229458603452652157407659410117296265092446247976960 else 485667223056439169477857771826988367458618955971044681926927351500042158554551943168)) else (if i.val < 54 then 971334446112878338955715543653976734917237911942089363853854703000084317109103886336 else (if i.val < 55 then 1942668892225756677911431087307953469834475823884178727707709406000168634218207772672 else 3885337784451513355822862174615906939668951647768357455415418812000337268436415545344)))) else (if i.val < 61 then (if i.val < 58 then (if i.val < 57 then 7770675568903026711645724349231813879337903295536714910830837624000674536872831090688 else 15541351137806053423291448698463627758675806591073429821661675248001349073745662181376) else (if i.val < 59 then 31082702275612106846582897396927255517351613182146859643322112555964565688721032085504 else (if i.val < 60 then 62165404551224213693165794793854511034703226364293719286644225111927978455938531065856 else 133499189745056880150142936331245051935371940104981728180257763850390718693687887455780750753792))) else (if i.val < 64 then (if i.val < 62 then 266998379490113760300285872662490103870743880209963456360515527700781437387375774911561501507584 else (if i.val < 63 then 533996758980227520600571745324980207741487760419926912721031055401562874774751549823123003015168 else 1067993517960455041201143490649960415482975520839853825442062110803125749549503099646246006030336)) else (if i.val < 65 then 2135987035920910082402286981299920830965951041679707650884124221606251499099006199292492012060672 else (if i.val < 66 then 4271974071841820164804573962599841661931902083359415301768248443212502998198012398584984024121344 else 8543948143683640329609147925199683323863804166718830603536496886425005996396024797169968048242688))))) else (if i.val < 78 then (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then 17087896287367280659218295850399366647727608333437661207072993772850011992792049594339936096485376 else 34175792574734561318436591700798733295455216666875322414145987545700023985584099188679872192970752) else (if i.val < 70 then 68351585149469122636873183401597466590910433333750644828291975091400047971168198377359744385941504 else (if i.val < 71 then 136703170298938245273746366803194933181820866667501289656583950182800095942336396754719488771883008 else 273406340597876490547492733606389866363641733335002579313167900365600191884672793509438977543766016))) else (if i.val < 75 then (if i.val < 73 then 546812681195752981094985467212779732727283466670005158626335800731200383769345587018877955087532032 else (if i.val < 74 then 1093625362391505962189970934425559465454566933340010317252671601462400767538691174037755910175064064 else 2037035976341925728001943253965342596838276591745508847150988985232387724615335349510471680)) else (if i.val < 76 then 4074071952683851456003886507930685193676553183491017694301977970464775449230670699020943360 else (if i.val < 77 then 8148143905367702912007773015861370387353106366982035388603955940929550898461341398041886720 else 16296287810735405824015546031722740774706212733964070777207911881859101796922682796083773440)))) else (if i.val < 84 then (if i.val < 81 then (if i.val < 79 then 32592575621470811648031092063445481549412425467928141554415823763718203593845365592167546880 else (if i.val < 80 then 65185151242941623296062184126890963098824850935856283108831647527436407187690731184335093760 else 130370302485883246592124368253781926197649701871712566217663295054872814375381462368670187520)) else (if i.val < 82 then 260740604971766493184248736507563852395299403743425132435326590109745628750762924737340375040 else (if i.val < 83 then 521481209941635848780200131534086302101799762305325207957718809115144403403261806959952658432 else 1042962419883271697560400263068172604203599524610650415915437618230288806806523613919905316864))) else (if i.val < 87 then (if i.val < 85 then 2085924839766543395120800526136345208407199049221300831830875236460577613613047227839810633728 else (if i.val < 86 then 4171849679533086790241601052272690416814398098442601663661750472921155227226094455679621267456 else 8343699359066173580483202104545380833628796196885203327323500945842310454452188911359242534912)) else (if i.val < 88 then 16687398718132347160966404209090761667257592393770406654647001891684620908904377822718485069824 else (if i.val < 89 then 33374797436264694321932808418181523334515184787540813309292674555374694841975137218651588919296 else 66749594872529388643865616836363046669030369575081626618585349110748151743912141978532885561344))))))) else (if i.val < 135 then (if i.val < 112 then (if i.val < 101 then (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then 143343663499379469476163870317026930256060997086741832302942172146879793402831329563476742658465996996608 else 286687326998758938952327740634053860512121994173483664605884344293759586805662659126953485316931993993216) else (if i.val < 93 then 573374653997517877904655481268107721024243988346967329211768688587519173611325318253906970633863987986432 else (if i.val < 94 then 1146749307995035755809310962536215442048487976693934658423537377175038347222650636507813941267727975972864 else 2293498615990071511618621925072430884096975953387869316847074754350076694445301273015627882535455951945728))) else (if i.val < 98 then (if i.val < 96 then 4586997231980143023237243850144861768193951906775738633694149508700153388890602546031255765070911903891456 else (if i.val < 97 then 9173994463960286046474487700289723536387903813551477267388299017400306777781205092062511530141823807782912 else 18347988927920572092948975400579447072775807627102954534776598034800613555562410184125023060283647615565824)) else (if i.val < 99 then 36695977855841144185897950801158894145551615254205909069553196069601227111124820368250046120567295231131648 else (if i.val < 100 then 73391955711682288371795901602317788291103230508411818139106392139202454222249640736500092241134590462263296 else 146783911423364576743591803204635576582206461016823636278212784278404908444499281473000184482269180924526592)))) else (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 293567822846729153487183606409271153164412922033647272556425568556809816888998562946000368964538361849053184 else 587135645693458306974367212818542306328825844067294545112851137113619633777997125892000737929076723698106368) else (if i.val < 104 then 1174271291386916613948734425637084612657651688134589090225702274227239267555994251784001475858153447396212736 else (if i.val < 105 then 2187250724791000178857334425057242192714027740637326013348040116407333059303679876555051368783544320 else 4374501449582000357714668850114484385428055481274652026696080232814666118607359753110102737567088640))) else (if i.val < 109 then (if i.val < 107 then 8749002899164000715429337700228968770856110962549304053392160465629332237214719506220205475134177280 else (if i.val < 108 then 17498005798328001430858675400457937541712221925098608106784320931258664474429439012440410950268354560 else 34996011596656002861717350800915875083424443850197216213568641862517328948858878024880821900536709120)) else (if i.val < 110 then 69992023193312005723434701601831750166848887700394432427137283725034657897717756049761643801073418240 else (if i.val < 111 then 139984046386624011446869403203663500333697775400788864854274567450069315795435512099523287602146836480 else 279968092773248022893738806407327000667395550801577729708549134900138631590871024199046575204293672960))))) else (if i.val < 123 then (if i.val < 117 then (if i.val < 114 then (if i.val < 113 then 559936185544459009813040264318449744192201510460486333705700308978402977733610140154715462418424659968 else 1119872371088918019626080528636899488384403020920972667411400617956805955467220280309430924836849319936) else (if i.val < 115 then 2239744742177836039252161057273798976768806041841945334822801235913611910934440560618861849673698639872 else (if i.val < 116 then 4479489484355672078504322114547597953537612083683890669645602471827223821868881121237723699347397279744 else 8958978968711344157008644229095195907075224167367781339291204943654447643737762242475447398694794559488))) else (if i.val < 120 then (if i.val < 118 then 17917957937422688314017288458190391814150448334735562678582409887308895287475524484950894797389589118976 else (if i.val < 119 then 35835915874845376628034576916380783628300896669471125357163392526926413843065775599805243906703075835904 else 71671831749690753256069153832761567256601793338942250714326785053851498458137004223776869386620770451456)) else (if i.val < 121 then 523518245917962924170990541921210287823855143364746828560930390318326543173374046640057352192 else (if i.val < 122 then 1047036491835925848341981083842420575647710286729493657121860780636653086346748093280114704384 else 2094072983671851696683962167684841151295420573458987314243721561273306172693496186560229408768)))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 124 then 4188145967343703393367924335369682302590841146917974628487443122546612345386992373120458817536 else (if i.val < 125 then 8376291934687406786735848670739364605181682293835949256974886245093224690773984746240917635072 else 16752583869374813573471697341478729210363364587671898513949772490186449381547969492481835270144)) else (if i.val < 127 then 33505167738749627146943394682957458420726729175343797027899544980372898763095938984963670540288 else (if i.val < 128 then 67010335477499254293886789365914916841453458350687594055799089960745797526191877969927341080576 else 134020670954998508587773578731829833682906916701375188111598179921491595052383755939854682161152))) else (if i.val < 132 then (if i.val < 130 then 268041341909997017175547157463659667365813833402750376223196359842983190104767511879709364322304 else (if i.val < 131 then 536082683819994034351094314927319334731627666805500752446392719685966380209535023759418728644608 else 1072165367639988068702188629854638669463255333611001504892785439371932760419070047518837457289216)) else (if i.val < 133 then 2144330735279976137404377259709277338926510667222003009785570878743865520838140095037674914578432 else (if i.val < 134 then 4288661470559952274808754519418554677853021334444006019571141757487731041676280190075349829156864 else 8577322941119904549617509038837107710201486880177510750061959315971984250925878365309958493306880)))))) else (if i.val < 157 then (if i.val < 146 then (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then 17154645882239809099235018077674215420402973760355021500123918631943968501851756730619916986613760 else 34309291764479618198470036155348430840805947520710043000247837263887937003703513461239833973227520) else (if i.val < 138 then 68618583528959236396940072310696861681611895041420086000495674527775874007407026922479667946455040 else (if i.val < 139 then 137237167057918472793880144621393723363223790082840172000991349055551748014814053844959335892910080 else 274474334115836945587760289242787446726447580165680344001982698111103496029628107689918671785820160))) else (if i.val < 143 then (if i.val < 141 then 548948668231673891175520578485574893452895160331360688003965396222206992059256215379837343571640320 else (if i.val < 142 then 1097897336463347782351041156971149786905790320662721376007930792444413984118512430759674687143280640 else 8543950180719616664066173093123896867789371483698709256027229115015418392030238059172903446904832)) else (if i.val < 144 then 17087900361439233328132346186247793735578742967397418512054458230030836784060476118345806893809664 else (if i.val < 145 then 34175800722878466656264692372495587471157485934794837024108916460061673568120952236691613787619328 else 68351601445756933312529384744991174942314971869589674048217832920123347136241904473383227575238656)))) else (if i.val < 151 then (if i.val < 148 then (if i.val < 147 then 136703202891513866625058769489982349884629943739179348096435665840246694272483808946766455150477312 else 273406405783027733250117538979964699769259887478358696192871331680493388544967617893532910300954624) else (if i.val < 149 then 546812811566055466500235077959929399538519773424221852947101497708599630997912021617821834801053696 else (if i.val < 150 then 1093625623132110933000470155919858799077039546848443704466955304040467376722453946689955593499705344 else 562123436269234064563733072369228798735551212342114774833765137003998494985992160339081296318514069508))) else (if i.val < 154 then (if i.val < 152 then 1124246872538468129127466144738457597471102424684229549667530274007996989971984320678162592637028139016 else (if i.val < 153 then 2248493745076936258254932289476915194942204849368459099335060548015993979943968641356325185274056278032 else 4496987490153872516509864578953830389884409698736918198670121096031987959887937282712650370548112556064)) else (if i.val < 155 then 8993974980307745033019729157907660779768819397473836397340242192063975919775874565425300741096225112128 else (if i.val < 156 then 17987949960615490066039458315815321559537638794947672794680484384127951839551749130850601482192450224256 else 35975899921230980132078916631630643119075277589895345589360968768255903679103498261701202964384900448512))))) else (if i.val < 168 then (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 71951799842461960264157833263261286238150555179790691178721937536511807358206996523402405928769800897024 else 143903599684923920528315666526522572476301110359581382357443875073023614716413993046804811857539601794048) else (if i.val < 160 then 287807199369847841056631333053045144952602220719162764714887750146047229432827986093609623715079203588096 else (if i.val < 161 then 575614398739695682113262666106090289905204441438325529429775500292094458865655972187219247430158407176192 else 1151228797479391364226525332212180579810408882876651058859551000584188917731311944374438494860316814352384))) else (if i.val < 165 then (if i.val < 163 then 2302457594958782728453050664424361159620817765753302117719102001168377835462623888748876989720633628704768 else (if i.val < 164 then 4604915189917565456906101328848722319241635531506604235438204002336755670925247777497753979441267257409536 else 9209830379835130913812202657697442871636207930133436208784949416724178071717103662112415470856196570808320)) else (if i.val < 166 then 18419660759670261827624405315394885743272415860266872417569898833448356143434207324224830941712393141616640 else (if i.val < 167 then 36839321519340523655248810630789771486544831720533744835139797666896712286868414648449661883424786283233280 else 73678643038681047310497621261579542973089663441067489670279595333793424573736829296899323766849572566466560)))) else (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then 147357286077362094620995242523159085946179326882134979340559190667586849147473658593798647533699145132933120 else (if i.val < 170 then 294714572154724189241990485046318171892358653764269958681118381335173698294947317187597295067398290265866240 else 589429144309448378483980970092636343784717307528539917362236762670347396589894634375194590134796580531732480)) else (if i.val < 172 then 1178858288618896756967961940185272687569434615057079834724473525340694793179789268750389180269593161063464960 else (if i.val < 173 then 9173996651211010829455207953710574880808046559009229634868515574951167654923093236455285377930796118048768 else 18347993302422021658910415907421149761616093118018459269737031149902335309846186472910570755861592236097536))) else (if i.val < 177 then (if i.val < 175 then 36695986604844043317820831814842299523232186236036918539474062299804670619692372945821141511723184472195072 else (if i.val < 176 then 73391973209688086635641663629684599046464372472073837078948124599609341239384745891642283023446368944390144 else 146783946419376173271283327259369198092928744944147674157896249199218682478769491783284566046892737888780288)) else (if i.val < 178 then 293567892838752346542566654518738396185857489888295348315792498398437364957538983566569132093785475777560576 else (if i.val < 179 then 587135785677504693085133309037476792371714979776590696631584996796874729915077967133138264187570950481379329 else 1174271571355009386170266618074953584743429959553181391730674454155108294177768788174253314205897915161903106))))))))
def xH : Matrix (Fin 180) (Fin 360) (ZMod 2) := fun i j => entry (xmask j) i
def zmask (j : Fin 360) : BitVec 180 := BitVec.ofNat 180 (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 75557863725914323419393 else 151115727451828646838786) else (if j.val < 3 then 302231454903657293677572 else (if j.val < 4 then 604462909807314587355144 else 1208925819614629174710288))) else (if j.val < 8 then (if j.val < 6 then 2417851639229258349420576 else (if j.val < 7 then 4835703278458516698841152 else 9671406556917033397682304)) else (if j.val < 9 then 19342813113834066795364608 else (if j.val < 10 then 38685626227668133590729216 else 77371252455336267181458432)))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then 154742504910672534362916864 else 309485009821345068725833728) else (if j.val < 14 then 618970019642690137451667456 else (if j.val < 15 then 1152921504611057664 else 2305843009222115328))) else (if j.val < 19 then (if j.val < 17 then 4611686018444230656 else (if j.val < 18 then 9223372036888461312 else 18446744073776922624)) else (if j.val < 20 then 36893488147553845248 else (if j.val < 21 then 73786976295107690496 else 147573952590215380992))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then 295147905179357020161 else 590295810358714040322) else (if j.val < 25 then 1180591620717428080644 else (if j.val < 26 then 2361183241434856161288 else 4722366482869712322576))) else (if j.val < 30 then (if j.val < 28 then 9444732965739424645152 else (if j.val < 29 then 18889465931478849290304 else 37778931862957698580608)) else (if j.val < 31 then 81129638414606681696064956792832 else (if j.val < 32 then 162259276829213363392129913585664 else 324518553658426726784259827171328)))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then 649037107316853453568519654342656 else (if j.val < 35 then 1298074214633706907137039308685312 else 2596148429267413814274078617370624)) else (if j.val < 37 then 5192296858534827628548157234741248 else (if j.val < 38 then 10384593717069655257096314469482496 else 20769187434139310514192628938964992))) else (if j.val < 42 then (if j.val < 40 then 41538374868278621028385257877929984 else (if j.val < 41 then 83076749736557242056770515755859968 else 166153499473114484113541031511719936)) else (if j.val < 43 then 332306998946228968227082063023439872 else (if j.val < 44 then 664613997892457936454164126046879744 else 1237940039289901466712539136)))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then 2475880078579802933425078272 else 4951760157159605866850156544) else (if j.val < 48 then 9903520314319211733700313088 else (if j.val < 49 then 19807040628638423467400626176 else 39614081257276846934801252352))) else (if j.val < 53 then (if j.val < 51 then 79228162514553693869602504704 else (if j.val < 52 then 158456325029107387739205009408 else 316912650057061853974876913664)) else (if j.val < 54 then 633825300114123707949753827328 else (if j.val < 55 then 1267650600228247415899507654656 else 2535301200456494831799015309312)))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then 5070602400912989663598030618624 else 10141204801825979327196061237248) else (if j.val < 59 then 20282409603651958654392122474496 else (if j.val < 60 then 40564819207303917308784244948992 else 87112285931760246646920200329216621805568))) else (if j.val < 64 then (if j.val < 62 then 174224571863520493293840400658433243611136 else (if j.val < 63 then 348449143727040986587680801316866487222272 else 696898287454081973175361602633732974444544)) else (if j.val < 65 then 1393796574908163946350723205267465948889088 else (if j.val < 66 then 2787593149816327892701446410534931897778176 else 5575186299632655785402892821069863795556352))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then 11150372599265311570805785642139727591112704 else 22300745198530623141611571284279455182225408) else (if j.val < 70 then 44601490397061246283223142568558910364450816 else (if j.val < 71 then 89202980794122492566446285137117820728901632 else 178405961588244985132892570274235641457803264))) else (if j.val < 75 then (if j.val < 73 then 356811923176489970265785140548471282915606528 else (if j.val < 74 then 713623846352979940531570281096942565831213056 else 1329227995789770465648197055560024064)) else (if j.val < 76 then 2658455991579540931296394111120048128 else (if j.val < 77 then 5316911983159081862592788222240096256 else 10633823966318163725185576444480192512)))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then 21267647932636327450371152888960385024 else (if j.val < 80 then 42535295865272654900742305777920770048 else 85070591730545309801484611555841540096)) else (if j.val < 82 then 170141183461090619602969223111683080192 else (if j.val < 83 then 340282366920943299167805987453073883136 else 680564733841886598335611974906147766272))) else (if j.val < 87 then (if j.val < 85 then 1361129467683773196671223949812295532544 else (if j.val < 86 then 2722258935367546393342447899624591065088 else 5444517870735092786684895799249182130176)) else (if j.val < 88 then 10889035741470185573369791598498364260352 else (if j.val < 89 then 21778071482940371146739583196996728520704 else 43556142965880742293479166393993457041408))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then 93536104789177786765353979883938455988628757676032 else 187072209578355573530707959767876911977257515352064) else (if j.val < 93 then 374144419156711147061415919535753823954515030704128 else (if j.val < 94 then 748288838313422294122831839071507647909030061408256 else 1496577676626844588245663678143015295818060122816512))) else (if j.val < 98 then (if j.val < 96 then 2993155353253689176491327356286030591636120245633024 else (if j.val < 97 then 5986310706507378352982654712572061183272240491266048 else 11972621413014756705965309425144122366544480982532096)) else (if j.val < 99 then 23945242826029513411930618850288244733088961965064192 else (if j.val < 100 then 47890485652059026823861237700576489466177923930128384 else 95780971304118053647722475401152978932355847860256768)))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then 191561942608236107295444950802305957864711695720513536 else 383123885216472214590889901604611915729423391441027072) else (if j.val < 104 then 766247770432944429181779803209223831458846782882054144 else (if j.val < 105 then 1427247692711172460326424448748449579963252736 else 2854495385422344920652848897496899159926505472))) else (if j.val < 109 then (if j.val < 107 then 5708990770844689841305697794993798319853010944 else (if j.val < 108 then 11417981541689379682611395589987596639706021888 else 22835963083378759365222791179975193279412043776)) else (if j.val < 110 then 45671926166757518730445582359950386558824087552 else (if j.val < 111 then 91343852333515037460891164719900773117648175104 else 182687704667030074921782329439801546235296350208))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then 365375409332730921849017683045984665685211480064 else 730750818665461843698035366091969331370422960128) else (if j.val < 115 then 1461501637330923687396070732183938662740845920256 else (if j.val < 116 then 2923003274661847374792141464367877325481691840512 else 5846006549323694749584282928735754650963383681024))) else (if j.val < 120 then (if j.val < 118 then 11692013098647389499168565857471509301926767362048 else (if j.val < 119 then 23384026197294778998337131714943018603853534724096 else 46768052394589557996674263429886037207707069448192)) else (if j.val < 121 then 341611594916723379336278414492048621568 else (if j.val < 122 then 683223189833446758672556828984097243136 else 1366446379666893517345113657968194486272)))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then 2732892759333787034690227315936388972544 else (if j.val < 125 then 5465785518667574069380454631872777945088 else 10931571037335148138760909263745555890176)) else (if j.val < 127 then 21863142074670296277521818527491111780352 else (if j.val < 128 then 43726284149340592555043637054982223560704 else 87452568298681185110087274109964447121408))) else (if j.val < 132 then (if j.val < 130 then 174905136597362370220174548219928894242816 else (if j.val < 131 then 349810273194724740440349096439857788485632 else 699620546389449480880698192879715576971264)) else (if j.val < 133 then 1399241092778898961761396385759431153942528 else (if j.val < 134 then 2798482185557797923522792771518862307885056 else 5596964371115595847045585543037723542028289)))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then 11193928742231191694091171086075447084056578 else 22387857484462383388182342172150894168113156) else (if j.val < 138 then 44775714968924766776364684344301788336226312 else (if j.val < 139 then 89551429937849533552729368688603576672452624 else 179102859875699067105458737377207153344905248))) else (if j.val < 143 then (if j.val < 141 then 358205719751398134210917474754414306689810496 else (if j.val < 142 then 716411439502796268421834949508828613379620992 else 5575187628860651570299802471969150656839936)) else (if j.val < 144 then 11150375257721303140599604943938301313679872 else (if j.val < 145 then 22300750515442606281199209887876602627359744 else 44601501030885212562398419775753205254719488)))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then 89203002061770425124796839551506410509438976 else 178406004123540850249593679103012821018877952) else (if j.val < 149 then 356812008247081700499187358206025642037755904 else (if j.val < 150 then 713624016494163400998374716412051284075511808 else 366802657025431689431979494148520320419110060032))) else (if j.val < 154 then (if j.val < 152 then 733605314050863378863958988297040640838220120064 else (if j.val < 153 then 1467210628101726757727917976594081281676440240128 else 2934421256203453515455835953188162563352880480256)) else (if j.val < 155 then 5868842512406907030911671906376325126705760960512 else (if j.val < 156 then 11737685024813814061823343812752650253411521921024 else 23475370049627628123646687625505300506823043842048))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 46950740099255256247293375251010601013646087684096 else 93901480198510512494586750502021202027292175368192) else (if j.val < 160 then 187802960397021024989173501004042404054584350736384 else (if j.val < 161 then 375605920794042049978347002008084808109168701472768 else 751211841588084099956694004016169616218337402945536))) else (if j.val < 165 then (if j.val < 163 then 1502423683176168199913388008032339232436674805891072 else (if j.val < 164 then 3004847366352336399826776016064678464873349611782144 else 6009694732704672799653552032129355776825195690459136)) else (if j.val < 166 then 12019389465409345599307104064258711553650391380918272 else (if j.val < 167 then 24038778930818691198614208128517423107300782761836544 else 48077557861637382397228416257034846214601565523673088)))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then 96155115723274764794456832514069692429203131047346176 else (if j.val < 170 then 192310231446549529588913665028139384858406262094692352 else 384620462893099059177827330056278769716812524189384704)) else (if j.val < 172 then 769240925786198118355654660112557539433625048378769408 else (if j.val < 173 then 5986312133755071058922174133091864698006110956683264 else 11972624267510142117844348266183729396012221913366528))) else (if j.val < 177 then (if j.val < 175 then 23945248535020284235688696532367458792024443826733056 else (if j.val < 176 then 47890497070040568471377393064734917584048887653466112 else 95780994140081136942754786129469835168097775306932224)) else (if j.val < 178 then 191561988280162273885509572258939670336195550613864448 else (if j.val < 179 then 383123976560324547771019144517879340672391101227728896 else 766247953120649095542038289035758681344782202455457792)))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then 4294967299 else 8589934598) else (if j.val < 183 then 17179869196 else (if j.val < 184 then 34359738392 else 68719476784))) else (if j.val < 188 then (if j.val < 186 then 137438953568 else (if j.val < 187 then 274877907136 else 549755814272)) else (if j.val < 189 then 1099511628544 else (if j.val < 190 then 2199023257088 else 4398046514176)))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then 8796093028352 else 17592186056704) else (if j.val < 194 then 35184372113408 else (if j.val < 195 then 70368744226816 else 140737488453632))) else (if j.val < 199 then (if j.val < 197 then 281474976907264 else (if j.val < 198 then 562949953814528 else 1125899907629056)) else (if j.val < 200 then 2251799815258112 else (if j.val < 201 then 4503599630516224 else 9007199261032448))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then 18014398522064896 else 36028797044129792) else (if j.val < 205 then 72057594088259584 else (if j.val < 206 then 144115188176519168 else 288230376353038336))) else (if j.val < 210 then (if j.val < 208 then 576460752706076672 else (if j.val < 209 then 1879048192 else 2684354561)) else (if j.val < 211 then 4611686021648613376 else (if j.val < 212 then 9223372043297226752 else 18446744086594453504)))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then 36893488173188907008 else (if j.val < 215 then 73786976346377814016 else 147573952692755628032)) else (if j.val < 217 then 295147905385511256064 else (if j.val < 218 then 590295810771022512128 else 1180591621542045024256))) else (if j.val < 222 then (if j.val < 220 then 2361183243084090048512 else (if j.val < 221 then 4722366486168180097024 else 9444732972336360194048)) else (if j.val < 223 then 18889465944672720388096 else (if j.val < 224 then 37778931889345440776192 else 75557863778690881552384)))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then 151115727557381763104768 else 302231455114763526209536) else (if j.val < 228 then 604462910229527052419072 else (if j.val < 229 then 1208925820459054104838144 else 2417851640918108209676288))) else (if j.val < 233 then (if j.val < 231 then 4835703281836216419352576 else (if j.val < 232 then 9671406563672432838705152 else 19342813127344865677410304)) else (if j.val < 234 then 38685626254689731354820608 else (if j.val < 235 then 77371252509379462709641216 else 154742505018758925419282432)))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then 309485010037517850838564864 else 618970020075035701677129728) else (if j.val < 239 then 2017612633061982208 else (if j.val < 240 then 2882303762590859264 else 4951760160600285613417037824))) else (if j.val < 244 then (if j.val < 242 then 9903520321200571226834075648 else (if j.val < 243 then 19807040642401142453668151296 else 39614081284802284907336302592)) else (if j.val < 245 then 79228162569604569814672605184 else (if j.val < 246 then 158456325139209139629345210368 else 316912650278418279258690420736))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then 633825300556836558517380841472 else 1267650601113673117034761682944) else (if j.val < 250 then 2535301202227346234069523365888 else (if j.val < 251 then 5070602404454692468139046731776 else 10141204808909384936278093463552))) else (if j.val < 255 then (if j.val < 253 then 20282409617818769872556186927104 else (if j.val < 254 then 40564819235637539745112373854208 else 81129638471275079490224747708416)) else (if j.val < 256 then 162259276942550158980449495416832 else (if j.val < 257 then 324518553885100317960898990833664 else 649037107770200635921797981667328)))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then 1298074215540401271843595963334656 else (if j.val < 260 then 2596148431080802543687191926669312 else 5192296862161605087374383853338624)) else (if j.val < 262 then 10384593724323210174748767706677248 else (if j.val < 263 then 20769187448646420349497535413354496 else 41538374897292840698995070826708992))) else (if j.val < 267 then (if j.val < 265 then 83076749794585681397990141653417984 else (if j.val < 266 then 166153499589171362795980283306835968 else 332306999178342725591960566613671936)) else (if j.val < 268 then 664613998356685451183921133227343872 else (if j.val < 269 then 2166395068749415481073467392 else 3094850099366372191854657536))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then 5316911986853483609471369065818750976 else 10633823973706967218942738131637501952) else (if j.val < 273 then 21267647947413934437885476263275003904 else (if j.val < 274 then 42535295894827868875770952526550007808 else 85070591789655737751541905053100015616))) else (if j.val < 278 then (if j.val < 276 then 170141183579311475503083810106200031232 else (if j.val < 277 then 340282367158622951006167620212400062464 else 680564734317245902012335240424800124928)) else (if j.val < 279 then 1361129468634491804024670480849600249856 else (if j.val < 280 then 2722258937268983608049340961699200499712 else 5444517874537967216098681923398400999424)))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then 10889035749075934432197363846796801998848 else 21778071498151868864394727693593603997696) else (if j.val < 284 then 43556142996303737728789455387187207995392 else (if j.val < 285 then 87112285992607475457578910774374415990784 else 174224571985214950915157821548748831981568))) else (if j.val < 289 then (if j.val < 287 then 348449143970429901830315643097497663963136 else (if j.val < 288 then 696898287940859803660631286194995327926272 else 1393796575881719607321262572389990655852544)) else (if j.val < 290 then 2787593151763439214642525144779981311705088 else (if j.val < 291 then 5575186303526878429285050289559962623410176 else 11150372607053756858570100579119925246820352))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then 22300745214107513717140201158239850493640704 else 44601490428215027434280402316479700987281408) else (if j.val < 295 then 89202980856430054868560804632959401974562816 else (if j.val < 296 then 178405961712860109737121609265918803949125632 else 356811923425720219474243218531837607898251264))) else (if j.val < 300 then (if j.val < 298 then 713623846851440438948486437063675215796502528 else (if j.val < 299 then 2326148992623602777581662355490603008 else 3323069990700229721544897925599985664)) else (if j.val < 301 then 5708990774811523511587891496509401726372020224 else (if j.val < 302 then 11417981549623047023175782993018803452744040448 else 22835963099246094046351565986037606905488080896)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then 45671926198492188092703131972075213810976161792 else (if j.val < 305 then 91343852396984376185406263944150427621952323584 else 182687704793968752370812527888300855243904647168)) else (if j.val < 307 then 365375409587937504741625055776601710487809294336 else (if j.val < 308 then 730750819175875009483250111553203420975618588672 else 1461501638351750018966500223106406841951237177344))) else (if j.val < 312 then (if j.val < 310 then 2923003276703500037933000446212813683902474354688 else (if j.val < 311 then 5846006553407000075866000892425627367804948709376 else 11692013106814000151732001784851254735609897418752)) else (if j.val < 313 then 23384026213628000303464003569702509471219794837504 else (if j.val < 314 then 46768052427256000606928007139405018942439589675008 else 93536104854512001213856014278810037884879179350016)))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 187072209709024002427712028557620075769758358700032 else 374144419418048004855424057115240151539516717400064) else (if j.val < 318 then 748288838836096009710848114230480303079033434800128 else (if j.val < 319 then 1496577677672192019421696228460960606158066869600256 else 2993155355344384038843392456921921212316133739200512))) else (if j.val < 323 then (if j.val < 321 then 5986310710688768077686784913843842424632267478401024 else (if j.val < 322 then 11972621421377536155373569827687684849264534956802048 else 23945242842755072310747139655375369698529069913604096)) else (if j.val < 324 then 47890485685510144621494279310750739397058139827208192 else (if j.val < 325 then 95780971371020289242988558621501478794116279654416384 else 191561942742040578485977117243002957588232559308832768)))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then 383123885484081156971954234486005915176465118617665536 else 766247770968162313943908468972011830352930237235331072) else (if j.val < 329 then 2497683462235429791852000446536616488669806592 else (if j.val < 330 then 3568119233094127698430630796527544901237211136 else 4281743078117879643174857908348485409148239876))) else (if j.val < 334 then (if j.val < 332 then 8563486156235759286349715816696970818296479752 else (if j.val < 333 then 17126972312471518572699431633393941636592959504 else 34253944624943037145398863266787883273185919008)) else (if j.val < 335 then 68507889249886074290797726533575766546371838016 else (if j.val < 336 then 137015778499772148581595453067151533092743676032 else 274031556999544297163190906134303066185487352064))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then 548063113999088594326381812268606132370974704128 else 1096126227998177188652763624537212264741949408256) else (if j.val < 340 then 2192252455996354377305527249074424529483898816512 else (if j.val < 341 then 4384504911992708754611054498148849058967797633024 else 8769009823985417509222108996297698117935595266048))) else (if j.val < 345 then (if j.val < 343 then 17538019647970835018444217992595396235871190532096 else (if j.val < 344 then 35076039295941670036888435985190792471742381064192 else 70152078591883340073776871970381584943484762128384)) else (if j.val < 346 then 140304157183766680147553743940763169886969524256768 else (if j.val < 347 then 280608314367533360295107487881526339773939048513536 else 561216628735066720590214975763052679547878097027072)))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then 1122433257470133441180429951526105359095756194054144 else (if j.val < 350 then 2244866514940266882360859903052210718191512388108288 else 4489733029880533764721719806104421436383024776216576)) else (if j.val < 352 then 8979466059761067529443439612208842872766049552433152 else (if j.val < 353 then 17958932119522135058886879224417685745532099104866304 else 35917864239044270117773758448835371491064198209732608))) else (if j.val < 357 then (if j.val < 355 then 71835728478088540235547516897670742982128396419465216 else (if j.val < 356 then 143671456956177080471095033795341485964256792838930432 else 287342913912354160942190067590682971928513585677860864)) else (if j.val < 358 then 574685827824708321884380135181365943857027171355721728 else (if j.val < 359 then 1149371655649416643768760270362731887714054341637701633 else 766247771860192121885133394633440561258864697474547714)))))))))
def zH : Matrix (Fin 180) (Fin 360) (ZMod 2) := fun i j => entry (zmask j) i
end BBNew360KernelData

set_option maxHeartbeats 0
open Matrix BBCode
namespace BBNew360Symmetry

variable {l m : ℕ}

def shiftG (g : Grp l m) : Grp l m ≃ Grp l m := Equiv.addRight g

def shiftQ (g : Grp l m) : Qubit l m ≃ Qubit l m :=
  Equiv.sumCongr (shiftG g) (shiftG g)

def negG : Grp l m ≃ Grp l m := Equiv.neg _

def dualQ : Qubit l m ≃ Qubit l m :=
  (Equiv.sumCongr negG negG).trans (Equiv.sumComm _ _)

lemma HX_shift (A B : Poly l m) (g : Grp l m) :
    (HX A B).submatrix (shiftG g) (shiftQ g) = HX A B := by
  ext i j
  cases j <;> simp [HX,BBCode.circulant,Matrix.submatrix,shiftG,shiftQ]

lemma HZ_shift (A B : Poly l m) (g : Grp l m) :
    (HZ A B).submatrix (shiftG g) (shiftQ g) = HZ A B := by
  ext i j
  cases j <;> simp [HZ,BBCode.circulant,Matrix.submatrix,shiftG,shiftQ]

lemma HZ_dual (A B : Poly l m) :
    (HZ A B).submatrix negG dualQ = HX A B := by
  ext i j
  cases j <;> simp [HX,HZ,BBCode.circulant,Matrix.submatrix,negG,dualQ,sub_eq_add_neg,add_comm]

lemma HX_dual (A B : Poly l m) :
    (HX A B).submatrix negG dualQ = HZ A B := by
  ext i j
  cases j <;> simp [HX,HZ,BBCode.circulant,Matrix.submatrix,negG,dualQ,sub_eq_add_neg,add_comm]

lemma kernel_reindex {r c : Type} [Fintype r] [Fintype c]
    (H : Matrix r c (ZMod 2)) (er : r ≃ r) (ec : c ≃ c) (v : c → ZMod 2)
    (hv : H *ᵥ v = 0) : H.submatrix er ec *ᵥ (v ∘ ec) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ ec) ∘ ec.symm = v := by ext j; simp
  rw [he,hv]
  rfl

lemma weight_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (v : b → ZMod 2) : weight (v ∘ e) = weight v := by
  classical
  simp only [weight,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact e.sum_comp (fun j => if v j ≠ 0 then (1 : ℕ) else 0)

lemma x_to_z [NeZero l] [NeZero m] (A B : Poly l m) (v : Qubit l m → ZMod 2)
    (hv : IsXLogical A B v) : IsZLogical A B (v ∘ dualQ) := by
  constructor
  · have h := kernel_reindex (HZ A B) negG dualQ v hv.1
    rwa [HZ_dual] at h
  · intro h
    have he := (BBNew360Cert.rowspace_reindex (HX A B) negG dualQ v)
    rw [HX_dual] at he
    exact hv.2 (he.mp h)
end BBNew360Symmetry

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BBNew360Cert BBNew360Bits
namespace BBNew360KernelData
def polyA : Poly 6 30 := {(0,0),(0,1),(1,2)}
def polyB : Poly 6 30 := {(0,0),(0,8),(2,16)}
def er : Fin 180 ≃ Grp 6 30 where
  toFun i := ((i.val / 30 : ℕ), (i.val % 30 : ℕ))
  invFun g := ⟨g.1.val * 30 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 360 ≃ Qubit 6 30 where
  toFun i := if h : i.val < 180 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-180,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨180 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

namespace BBNew360Sparse

lemma col_three (a b c g : Grp 6 30) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 180) :
    circulant {a,b,c} (er i) g =
      entry (unit (er.symm (g-a)) ^^^ unit (er.symm (g-b)) ^^^ unit (er.symm (g-c))) i := by
  have eqg (t : Grp 6 30) : i = er.symm (g-t) ↔ g-er i = t := by
    rw [Equiv.eq_symm_apply]
    constructor <;> intro h <;> linear_combination -h
  simp only [entry_xor,unit_entry,eqg,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
  by_cases ha : g-er i = a
  · have hb : g-er i ≠ b := by simpa only [ha] using hab
    have hc : g-er i ≠ c := by simpa only [ha] using hac
    simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  · by_cases hb : g-er i = b
    · have hc : g-er i ≠ c := by simpa only [hb] using hbc
      simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    · by_cases hc : g-er i = c <;> simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]

def column (q : Qubit 6 30) : BitVec 180 :=
  match q with
  | Sum.inl g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,1))) ^^^ unit (er.symm (g-(1,2)))
  | Sum.inr g => unit (er.symm (g-(0,0))) ^^^ unit (er.symm (g-(0,8))) ^^^ unit (er.symm (g-(2,16)))

lemma column_entry (i : Fin 180) (q : Qubit 6 30) :
    HX polyA polyB (er i) q = entry (column q) i := by
  cases q with
  | inl g => exact col_three (0,0) (0,1) (1,2) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three (0,0) (0,8) (2,16) g (by decide) (by decide) (by decide) i

lemma xcolumn_bits : ∀ j, xmask j = column (eqb j) := by decide +kernel
lemma xtable_sparse : (HX polyA polyB).submatrix er eqb = xH := by
  ext i j
  change HX polyA polyB (er i) (eqb j) = entry (xmask j) i
  rw [xcolumn_bits,column_entry]
end BBNew360Sparse

namespace BBNew360Sparse
lemma col_three_z (a b c g : Grp 6 30) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 180) :
    circulant {a,b,c} g (er i) =
      entry (unit (er.symm (g+a)) ^^^ unit (er.symm (g+b)) ^^^ unit (er.symm (g+c))) i := by
  have eqg (t : Grp 6 30) : i = er.symm (g+t) ↔ er i-g = t := by
    rw [Equiv.eq_symm_apply]
    constructor <;> intro h <;> linear_combination h
  simp only [entry_xor,unit_entry,eqg,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
  by_cases ha : er i-g = a
  · have hb : er i-g ≠ b := by simpa only [ha] using hab
    have hc : er i-g ≠ c := by simpa only [ha] using hac
    simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  · by_cases hb : er i-g = b
    · have hc : er i-g ≠ c := by simpa only [hb] using hbc
      simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    · by_cases hc : er i-g = c <;> simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]


def zcolumn (q : Qubit 6 30) : BitVec 180 :=
  match q with
  | Sum.inl g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,8))) ^^^ unit (er.symm (g+(2,16)))
  | Sum.inr g => unit (er.symm (g+(0,0))) ^^^ unit (er.symm (g+(0,1))) ^^^ unit (er.symm (g+(1,2)))

lemma zcolumn_entry (i : Fin 180) (q : Qubit 6 30) :
    HZ polyA polyB (er i) q = entry (zcolumn q) i := by
  cases q with
  | inl g => exact col_three_z (0,0) (0,8) (2,16) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three_z (0,0) (0,1) (1,2) g (by decide) (by decide) (by decide) i

lemma zcolumn_bits : ∀ j, zmask j = zcolumn (eqb j) := by decide +kernel
lemma ztable_sparse : (HZ polyA polyB).submatrix er eqb = zH := by
  ext i j
  change HZ polyA polyB (er i) (eqb j) = entry (zmask j) i
  rw [zcolumn_bits,zcolumn_entry]
end BBNew360Sparse

lemma xtable : (HX polyA polyB).submatrix er eqb = xH := BBNew360Sparse.xtable_sparse
lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := BBNew360Sparse.ztable_sparse
lemma xcolParity : ∀ j, ∑ i, xH i j = 1 := by
  intro j
  change ∑ i, entry (xmask j) i = 1
  rw [BBNew360Sparse.xcolumn_bits]
  cases hq : eqb j with
  | inl g => simp [BBNew360Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
  | inr g => simp [BBNew360Sparse.column, entry_xor, unit_entry, Finset.sum_add_distrib] <;> decide +kernel
lemma indicator_three {α : Type} [DecidableEq α] (a b c x : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((if x = a then (1 : ZMod 2) else 0) + (if x = b then 1 else 0)) +
      (if x = c then 1 else 0) = if x = a ∨ x = b ∨ x = c then 1 else 0 := by
  by_cases ha : x = a
  · have hb : x ≠ b := by simpa only [ha] using hab
    have hc : x ≠ c := by simpa only [ha] using hac
    simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
  · by_cases hb : x = b
    · have hc : x ≠ c := by simpa only [hb] using hbc
      simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
    · by_cases hc : x = c <;> simp [ha,hb,hc,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc]
def rowFormula (i : Fin 180) : BitVec 360 :=
  unit (eqb.symm (Sum.inl (er i+(0,0)))) ^^^
  unit (eqb.symm (Sum.inl (er i+(0,1)))) ^^^
  unit (eqb.symm (Sum.inl (er i+(1,2)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,0)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(0,8)))) ^^^
  unit (eqb.symm (Sum.inr (er i+(2,16))))
lemma row_formula_bits : ∀ i, xrow i = rowFormula i := by decide +kernel
lemma row_formula_entry (i : Fin 180) (j : Fin 360) :
    entry (rowFormula i) j = HX polyA polyB (er i) (eqb j) := by
  cases hq : eqb j with
  | inl g =>
    have yes (t : Grp 6 30) : j = eqb.symm (Sum.inl (er i+t)) ↔ g-er i = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inl.injEq,sub_eq_iff_eq_add,add_comm]
    have no (t : Grp 6 30) : j ≠ eqb.symm (Sum.inr (er i+t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [rowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HX,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,1) (1,2) (g-er i) (by decide) (by decide) (by decide)
  | inr g =>
    have yes (t : Grp 6 30) : j = eqb.symm (Sum.inr (er i+t)) ↔ g-er i = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inr.injEq,sub_eq_iff_eq_add,add_comm]
    have no (t : Grp 6 30) : j ≠ eqb.symm (Sum.inl (er i+t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [rowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HX,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,8) (2,16) (g-er i) (by decide) (by decide) (by decide)
lemma xrow_entry (i : Fin 180) (j : Fin 360) : entry (xrow i) j = xH i j := by
  rw [row_formula_bits,row_formula_entry]
  exact congrFun (congrFun xtable i) j
end BBNew360KernelData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BBNew360Cert
namespace BBNew360Search

def pick {r : ℕ} [NeZero r] (s : BitVec r) : Fin r :=
  ((List.finRange r).find? fun i => s.getLsbD i.val).getD 0

lemma pick_spec {r : ℕ} [NeZero r] (s : BitVec r) (hs : s ≠ 0) :
    s.getLsbD (pick s).val = true := by
  unfold pick
  cases hf : (List.finRange r).find? (fun i => s.getLsbD i.val) with
  | none =>
    have he : s = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have h := List.find?_eq_none.mp hf ⟨i,hi⟩ (by simp)
      simpa using h
    exact False.elim (hs he)
  | some i =>
    simpa using List.find?_some hf

def ones {r : ℕ} (s : BitVec r) : ℕ :=
  ((List.finRange r).map fun i => (s.getLsbD i.val).toNat).sum

lemma ones_eq {r : ℕ} (s : BitVec r) : ones s = ∑ i : Fin r, (s.getLsbD i.val).toNat := by
  simp [ones, ← List.sum_ofFn, List.ofFn_eq_map]

lemma ones_xor_le {r : ℕ} (s t : BitVec r) : ones (s ^^^ t) ≤ ones s + ones t := by
  rw [ones_eq,ones_eq,ones_eq,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases s.getLsbD i.val <;> cases t.getLsbD i.val <;> decide

lemma ones_sig_le {r n : ℕ} (C : Fin n → BitVec r) (hC : ∀ j, ones (C j) ≤ 3)
    (l : List (Fin n)) : ones (signature C l) ≤ 3*l.length := by
  induction l with
  | nil => simp [signature,ones]
  | cons a l ih =>
    have h := ones_xor_le (C a) (signature C l)
    change ones (signature C (a::l)) ≤ _ at h
    have ha := hC a
    simp only [List.length_cons]
    omega

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) : ℕ → List (Fin n) → BitVec r → Bool
  | fuel, used, sy =>
    if 3 * fuel < ones sy then true
    else if sy = 0 then decide (fuel = 2) && decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => (nbr (pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr fuel (j :: used) (C j ^^^ sy)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) :
    check C K nbr fuel used sy =
      if 3 * fuel < ones sy then true
      else if sy = 0 then decide (fuel = 2) && decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => (nbr (pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr f (j :: used) (C j ^^^ sy) := by
  cases fuel <;> rfl
end BBNew360Search

set_option maxHeartbeats 0
open BBNew360Search
namespace BBNew360Count
lemma ones_xor_add {r : ℕ} (s t : BitVec r) :
    ones (s ^^^ t) + 2 * ∑ i : Fin r, (if s.getLsbD i.val then (t.getLsbD i.val).toNat else 0) =
    ones s + ones t := by
  rw [ones_eq,ones_eq,ones_eq,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases s.getLsbD i.val <;> cases t.getLsbD i.val <;> decide

lemma update_eq {r : ℕ} (s t : BitVec r) (ps : List (Fin r)) (hn : ps.Nodup)
    (hp : ps.toFinset = Finset.univ.filter (fun i => s.getLsbD i.val))
    (h3 : ones s = 3) :
    ones t + 3 - 2 * (ps.map fun i => (t.getLsbD i.val).toNat).sum = ones (s ^^^ t) := by
  have he : (ps.map fun i => (t.getLsbD i.val).toNat).sum =
      ∑ i : Fin r, (if s.getLsbD i.val then (t.getLsbD i.val).toNat else 0) := by
    rw [← List.sum_toFinset _ hn,hp,Finset.sum_filter]
  have h := ones_xor_add s t
  rw [h3,← he] at h
  omega
end BBNew360Count

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BBNew360Cert BBNew360Bits BBNew360Search
namespace BBNew360KernelData
def zrow (i : Fin 180) : BitVec 360 := BitVec.ofNat 360 (if i.val < 90 then (if i.val < 45 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 587135645693458306972370149197334256843920638049832247869921304826447483987157330569263522006596862785617921 else 1174271291386916613944740298394668513687841274454159939951132108363814643775311183306100361998352984406228994) else (if i.val < 3 then 2187250724783011924372502227117621365353169440088185681621190868845966922347877648835450442803576836 else (if i.val < 4 then 4374501449566023848745004454235242730706338880176371363242381737691933844695755297670900885607153672 else 8749002899132047697490008908470485461412677760352742726484763475383867689391510595341801771214307344))) else (if i.val < 8 then (if i.val < 6 then 17498005798264095394980017816940970922825355520705485452969526950767735378783021190683603542428614688 else (if i.val < 7 then 34996011596528190789960035633881941845650711041410970905939053901535470757566042381367207084857229376 else 69992023193056381579920071267763883691301422082821941811878107803070941515132084762734414169714458752)) else (if i.val < 9 then 139984046386112763159840142535527767382602844165643883623756215606141883030264169525468828338355175681 else (if i.val < 10 then 279968092772225526319680285071055534765205688331287767247512431212283766060528339050937656676710351362 else 559936185544451052639360570142111069530411376662575534495024862424567532121056678101875313353420702724)))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then 1119872371088902105278721140284222139060822753325151068990049724849135064242113356203750626706841405448 else 2239744742177804210557442280568444278121645506650302137980099449698270128484226712407501253413682810896) else (if i.val < 14 then 4479489484355608421114884561136888556243291013300604275960198899396540256968453424815002506827365621792 else (if i.val < 15 then 8958978968711216842229769122273777112486582026601208551920397798793080513936906849630005013654731243584 else 17917957937422433684459538244547554224973164053202417103840795597586161027873813699260010027309462487168))) else (if i.val < 19 then (if i.val < 17 then 35835915874844867368919076489095108449946328106404834207680163947480945323862354028423474366542822572288 else (if i.val < 18 then 71671831749689734737838152978190216899892656212809668415360327894961890647724708056846948733085645144576 else 143343663499379469475676305956380433799785312425619336830720655789923781295449416113693897466171290289152)) else (if i.val < 20 then 286687326998758938951352611912760867599570624851238673661441311579847562590898832227387794932342580578304 else (if i.val < 21 then 573374653997517877902705223825521735199141249702477347322882623159695125181797664454775589864685161156608 else 1146749307995035755805410447651043470398282499404954694645765246319390250363595328909551179729370322313216))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then 2293498615990071511610820895302086940796564998809909389291530492638780500727190657819102359458740644626432 else 4586997231980143023221641790604173881593129997619818778583060985277561001454381315638204718917481289252864) else (if i.val < 25 then 9173994463960286046443283581208347763186259995239637557166121970555122002908762631276409437834962578505728 else (if i.val < 26 then 18347988927920572092886567162416695526372519990479275114332243941110244005817525262552818875669925157011456 else 36695977855841144185773134324833391052745039980958550228664487882220488011635050525105637751339850314022912))) else (if i.val < 30 then (if i.val < 28 then 73391955711682288371546268649666782105490079961917100457328975764440976023270101050211275502679700628045824 else (if i.val < 29 then 146783911423364576743092537299333564210980159923834200914657951528881952046540202100422551005359401256091648 else 293567822846729153486185074598667128421960319847668401829315903057763904093080404200845102010718802512183296)) else (if i.val < 31 then 883423534446072861443179687091368030557121338623552771635596025453871104 else (if i.val < 32 then 5759265950624267915594786727844109285354222450783165712963731456 else 9873027345459825329900493131489215092876018219551490684762456064)))) else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then 19746054690919650659800986262978430185752036439102981369524912128 else (if i.val < 35 then 39492109381839301319601972525956860371504072878205962739049824256 else 78984218763678602639203945051913720743008145756411925478099648512)) else (if i.val < 37 then 157968437527357205278407890103827441486016291512823850956199297024 else (if i.val < 38 then 315936875054714410556815780207654882972032583025647701912398594048 else 631873750109428821113631560415309765944065166050142482321264082944))) else (if i.val < 42 then (if i.val < 40 then 1263747500218857642227263120830619531888130332100284964642528165888 else (if i.val < 41 then 2527495000437715284454526241661239063776260664200569929285056331776 else 5054990000875430568909052483322478127552521328401139858570112663552)) else (if i.val < 43 then 10109980001750861137818104966644956255105042656802279717140225327104 else (if i.val < 44 then 20219960003501722275636209933289912510210085313604559434280450654208 else 40439920007003444551272419866579825020420170627209118868560901308416)))))) else (if i.val < 67 then (if i.val < 56 then (if i.val < 50 then (if i.val < 47 then (if i.val < 46 then 80879840014006889102544839733159650040840341254418237737121802616832 else 161759680028012245709550240825153647694534590485622306230257804378112) else (if i.val < 48 then 323519360056024491419100481650307295389069180971244612460515608756224 else (if i.val < 49 then 647038720112048982838200963300614590778138361942489224921031217512448 else 1294077440224097965676401926601229181556276723884978449842062435024896))) else (if i.val < 53 then (if i.val < 51 then 2588154880448195931352803853202458363112553447769956899684124870049792 else (if i.val < 52 then 5176309760896391862705607706404916726225106895539913799368249740099584 else 10352619521792783725411215412809833452450213791079827598736499480199168)) else (if i.val < 54 then 20705239043585567450822430825619666904900427582159655197472998960398336 else (if i.val < 55 then 41410478087171134901644861651239333809800855164319310394945997920796672 else 82820956174342269803289723302478667619601710328638620789891995841593344)))) else (if i.val < 61 then (if i.val < 58 then (if i.val < 57 then 165641912348684539606579446604957335239203420657277241579783991683186688 else 331283824697369079213158893209914670478406841314554483159567983366373376) else (if i.val < 59 then 662567649394738158426317786419829340956813682629108966319135966732746752 else (if i.val < 60 then 1325135298789476316852635572839658681913627365258217932638271933465493504 else 948568797240653103882873921170293217062635859165282371710595930276212130931818496))) else (if i.val < 64 then (if i.val < 62 then 6183964726724345153541541252600214805396193639074337762288381747135545344 else (if i.val < 63 then 10601082390315810534820991046612480277522253886255792432088737156327079936 else 21202164780631621069641982093224960555044507772511584864177474312654159872)) else (if i.val < 65 then 42404329561263242139283964186449921110089015545023169728354948625308319744 else (if i.val < 66 then 84808659122526484278567928372899842220178031090046339456709897250616639488 else 169617318245052968557135856745799684440356062180092678913419794501233278976))))) else (if i.val < 78 then (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then 339234636490105937114271713491599368880712124360185357826839589002466557952 else 678469272980211874228543426983198737761424248719132775615546719234640838656) else (if i.val < 70 then 1356938545960423748457086853966397475522848497438265551231093438469281677312 else (if i.val < 71 then 2713877091920847496914173707932794951045696994876531102462186876938563354624 else 5427754183841694993828347415865589902091393989753062204924373753877126709248))) else (if i.val < 75 then (if i.val < 73 then 10855508367683389987656694831731179804182787979506124409848747507754253418496 else (if i.val < 74 then 21711016735366779975313389663462359608365575959012248819697495015508506836992 else 43422033470733559950626779326924719216731151918024497639394990031017013673984)) else (if i.val < 76 then 86844066941467119901253558653849438433462303836048995278789980062034027347968 else (if i.val < 77 then 173688133882934239802507117307698876866924607672097990557579960124066980954113 else 347376267765868479605014234615397753733849215344195981115159920248133961908226)))) else (if i.val < 84 then (if i.val < 81 then (if i.val < 79 then 694752535531736959210028469230795507467698430688391962230319840496267923816452 else (if i.val < 80 then 1389505071063473918420056938461591014935396861376783924460639680992535847632904 else 2779010142126947836840113876923182029870793722753567848921279361985071695265808)) else (if i.val < 82 then 5558020284253895673680227753846364059741587445507135697842558723970143390531616 else (if i.val < 83 then 11116040568507791347360455507692728119483174891014271395685117447940286781063232 else 22232081137015582694720911015385456238966349782028542791370234895880573562126464))) else (if i.val < 87 then (if i.val < 85 then 44464162274031165389441822030770912477932699564057085582740469791761147124252928 else (if i.val < 86 then 88928324548062330778883644061541824955865399128114171165480939583522294248505856 else 177856649096124661557767288123083649911730798256228342330961879167044588497011712)) else (if i.val < 88 then 355713298192249323115534576246167299823461596512456684661923758334089176994023424 else (if i.val < 89 then 711426596384498646231069152492334599646923193024913369323847516668178353988046848 else 1422853192768997292462138304984669199293846386049826738647695033336356707976093696))))))) else (if i.val < 135 then (if i.val < 112 then (if i.val < 101 then (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then 1018517990538665030714458526479422853503662549667937411275581274301756837277657611531976704 else 6639981565224659910369254564338199387937914000676877100471605431177627232901267456) else (if i.val < 93 then 11382825542151978339697106439877353594350771088419383096596356764091211951074443264 else (if i.val < 94 then 22765651084303956679394212879754707188701542176838766193192713528182423902148886528 else 45531302168607913358788425759509414377403084353677532386385427056364847804297773056))) else (if i.val < 98 then (if i.val < 96 then 91062604337215826717576851519018828754806168707355064772770854112729695608595546112 else (if i.val < 97 then 182125208674431653435153703038037657509612337414710129545541708225459391217191092224 else 364250417348863306870307406076075315019224674829420259091083416450918782434382184448)) else (if i.val < 99 then 728500834697726613740614812152150630038449349657511290187619857068219138083383148544 else (if i.val < 100 then 1457001669395453227481229624304301260076898699315022580375239714136438276166766297088 else 2914003338790906454962459248608602520153797398630045160750479428272876552333532594176)))) else (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 5828006677581812909924918497217205040307594797260090321500958856545753104667065188352 else 11656013355163625819849836994434410080615189594520180643001917713091506209334130376704) else (if i.val < 104 then 23312026710327251639699673988868820161230379189040361286003835426183012418668260753408 else (if i.val < 105 then 46624053420654503279399347977737640322460758378080722572007670852366024837336521506816 else 93248106841309006558798695955475280644921516756161445144015341704732049674673043013632))) else (if i.val < 109 then (if i.val < 107 then 186496213682618013117597391910950561289843033512322890288030683409462946427842552922112 else (if i.val < 108 then 372992427365236026235194783821901122579686067024645780576061366818925892855685105844224 else 745984854730472052470389567643802245159372134049291561152122733637851785711370211688448)) else (if i.val < 110 then 1491969709460944104940779135287604490318744268098583122304245467275703571422740423376896 else (if i.val < 111 then 2983939418921888209881558270575208980637488536197166244608490934551407142845480846753792 else 5967878837843776419763116541150417961274977072394332489216981869102814285690961693507584))))) else (if i.val < 123 then (if i.val < 117 then (if i.val < 114 then (if i.val < 113 then 11935757675687552839526233082300835922549954144788664978433963738205628571381923387015168 else 23871515351375105679052466164601671845099908289577329956867927476411257142763846774030336) else (if i.val < 115 then 47743030702750211358104932329203343690199816579154659913735854952822514285527693548060672 else (if i.val < 116 then 95486061405500422716209864658406687380399633158309319827471709905645028571055387096121344 else 190972122811000845432419729316813374760799266316618639654943419811290057142110774192242688))) else (if i.val < 120 then (if i.val < 118 then 381944245622001690864839458633626749521598532633237279309886839622580114284221548384485376 else (if i.val < 119 then 763888491244003381729678917267253499043197065266474558619773679245160228568443096768970752 else 1527776982488006763459357834534506998086394130532949117239547358490320457136886193537941504)) else (if i.val < 121 then 1093625364937800932604358721394367793188307416760941710300880804129012712862983278253828100478468096 else (if i.val < 122 then 7129625917170701301939559909432823563680139377841927252484212875880971933047479730117279744 else 12222215859904054107674862676276055984691153044285893683094140303630035622717271470071873536)))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 124 then 24444431719808108215349725352552111969382306088571787366188280607260071245434542940143747072 else (if i.val < 125 then 48888863439616216430699450705104223938764612177143574732376561214520142490869085880287494144 else 97777726879232432861398901410208447877529224354287149464753122429040284981738171760574988288)) else (if i.val < 127 then 195555453758464865722797802820416895755058448708574298929506244858080569963476343521149976576 else (if i.val < 128 then 391110907516929731445595605640833791510116897417148597859012489716161139926952687042299953152 else 782221815033859462891191211281667583020233794832869948026648247547048909757359686008497504256))) else (if i.val < 132 then (if i.val < 130 then 1564443630067718925782382422563335166040467589665739896053296495094097819514719372016995008512 else (if i.val < 131 then 3128887260135437851564764845126670332080935179331479792106592990188195639029438744033990017024 else 6257774520270875703129529690253340664161870358662959584213185980376391278058877488067980034048)) else (if i.val < 133 then 12515549040541751406259059380506681328323740717325919168426371960752782556117754976135960068096 else (if i.val < 134 then 25031098081083502812518118761013362656647481434651838336852743921505565112235509952271920136192 else 50062196162167005625036237522026725313294962869303676673705487843011130224471019904543840272384)))))) else (if i.val < 157 then (if i.val < 146 then (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then 100124392324334011250072475044053450626589925738607353347410975686022260448942039809087680544768 else 200248784648668022500144950088106901253179851477214706694821951372043282957845947159405068812288) else (if i.val < 138 then 400497569297336045000289900176213802506359702954429413389643902744086565915691894318810137624576 else (if i.val < 139 then 800995138594672090000579800352427605012719405908858826779287805488173131831383788637620275249152 else 1601990277189344180001159600704855210025438811817717653558575610976346263662767577275240550498304))) else (if i.val < 143 then (if i.val < 141 then 3203980554378688360002319201409710420050877623635435307117151221952692527325535154550481100996608 else (if i.val < 142 then 6407961108757376720004638402819420840101755247270870614234302443905385054651070309100962201993216 else 12815922217514753440009276805638841680203510494541741228468604887810770109302140618201924403986432)) else (if i.val < 144 then 25631844435029506880018553611277683360407020989083482456937209775621540218604281236403848807972864 else (if i.val < 145 then 51263688870059013760037107222555366720814041978166964913874419551243080437208562472807697615945728 else 102527377740118027520074214445110733441628083956333929827748839102486160874417124945615395231891456)))) else (if i.val < 151 then (if i.val < 148 then (if i.val < 147 then 205054755480236055040148428890221466883256167912667859655497678204972321748834249891230790463782912 else 410109510960472110080296857780442933766512335825335719310995356409944643497668499782461580927565824) else (if i.val < 149 then 820219021920944220160593715560885867533024671650671438621990712819889286995336999564923161855131648 else (if i.val < 150 then 1640438043841888440321187431121771735066049343301342877243981425639778573990673999129846323710263296 else 1174271294120980019923505203860296297584867981145621723976147343432072841628687927273764919590205606124847104))) else (if i.val < 154 then (if i.val < 152 then 7655377536740541735303757794911674778736093008138216151757707264552720410283206764019155686240813056 else (if i.val < 153 then 13123504350735107522569499448974173880528394746434688260755580173331628270721418904578134901641969664 else 26247008701470215045138998897948347761056789492869376521511160346663256541442837809156269803283939328)) else (if i.val < 155 then 52494017402940430090277997795896695522113578985738753043022320693326513082885675618312539606567878656 else (if i.val < 156 then 104988034805880860180555995591793391044227157971477506086044641386653026165771351236625079213135757312 else 209976069611761720361111991183586782088454315942955012172089282773306052331542702473250158426271514624))))) else (if i.val < 168 then (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then 419952139223523440722223982367173564176908631885910024344178565546612104663085404946500316852543029248 else 839904278447046881444447964734347128353817263770287553148918489927571822180078786678831389719285202944) else (if i.val < 160 then 1679808556894093762888895929468694256707634527540575106297836979855143644360157573357662779438570405888 else (if i.val < 161 then 3359617113788187525777791858937388513415269055081150212595673959710287288720315146715325558877140811776 else 6719234227576375051555583717874777026830538110162300425191347919420574577440630293430651117754281623552))) else (if i.val < 165 then (if i.val < 163 then 13438468455152750103111167435749554053661076220324600850382695838841149154881260586861302235508563247104 else (if i.val < 164 then 26876936910305500206222334871499108107322152440649201700765391677682298309762521173722604471017126494208 else 53753873820611000412444669742998216214644304881298403401530783355364596619525042347445208942034252988416)) else (if i.val < 166 then 107507747641222000824889339485996432429288609762596806803061566710729193239050084694890417884068505976832 else (if i.val < 167 then 215015495282444001649778678971992864858577219525193613606123133421457057250105622413947217341351630733312 else 430030990564888003299557357943985729717154439050387227212246266842914114500211244827894434682703261466624)))) else (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then 860061981129776006599114715887971459434308878100774454424492533685828229000422489655788869365406522933248 else (if i.val < 170 then 1720123962259552013198229431775942918868617756201548908848985067371656458000844979311577738730813045866496 else 3440247924519104026396458863551885837737235512403097817697970134743312916001689958623155477461626091732992)) else (if i.val < 172 then 6880495849038208052792917727103771675474471024806195635395940269486625832003379917246310954923252183465984 else (if i.val < 173 then 13760991698076416105585835454207543350948942049612391270791880538973251664006759834492621909846504366931968 else 27521983396152832211171670908415086701897884099224782541583761077946503328013519668985243819693008733863936))) else (if i.val < 177 then (if i.val < 175 then 55043966792305664422343341816830173403795768198449565083167522155893006656027039337970487639386017467727872 else (if i.val < 176 then 110087933584611328844686683633660346807591536396899130166335044311786013312054078675940975278772034935455744 else 220175867169222657689373367267320693615183072793798260332670088623572026624108157351881950557544069870911488)) else (if i.val < 178 then 440351734338445315378746734534641387230366145587596520665340177247144053248216314703763901115088139741822976 else (if i.val < 179 then 880703468676890630757493469069282774460732291175193041330680354494288106496432629407527802230176279483645952 else 1761406937353781261514986938138565548921464582350386082661360708988576212992865258815055604460352558967291904))))))))
def xcoef (j : Fin 360) : BitVec 180 := BitVec.ofNat 180 (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 474006621861032574523912005718100744738979840 else 948013243722065149047824011436201489477959680) else (if j.val < 3 then 815305869466394430949603296162584187874582527 else (if j.val < 4 then 903223949359935442945082028724128714793689088 else 379200207343139000616793960902569353484976128))) else (if j.val < 8 then (if j.val < 6 then 758400414686278001233587921805138706969952256 else (if j.val < 7 then 447415869072101894910575781380068234060103680 else 894831738144203789821151562760136468120207360)) else (if j.val < 9 then 7340678886686143498892797040932893459021824 else (if j.val < 10 then 14681357773372286997785594081865786918043648 else 1089513627323352557942553750034471805191266303)))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then 3484504729550368375144562989912762333405184 else 753870250156967501161659447483491265985404927) else (if j.val < 14 then 758400414686278001233587921805138706969960448 else (if j.val < 15 then 447415869072101894910575781380068234060120064 else 894831738144203789821151562760136468120240128))) else (if j.val < 19 then (if j.val < 17 then 362415784911675694368933028974584860138078208 else (if j.val < 18 then 724831569823351388737866057949169720276156416 else 727502108497402904786265639988677624666529791)) else (if j.val < 20 then 727616427421952390618406716376315588377583616 else (if j.val < 21 then 27985163467172895963443336206943100652765184 else 55970326934345791926886672413886201305530368))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then 469803384944969361570543379143251298833661952 else 939606769889938723141086758286502597667323904) else (if j.val < 25 then 96193854724525894483602806355769507089547264 else (if j.val < 26 then 192387709449051788967205612711539014179094528 else 731313373357473091383072185823542768814333951))) else (if j.val < 30 then (if j.val < 28 then 714331689503751316314467404017549825962287104 else (if j.val < 29 then 1106179656746459297913873312277570055813292031 else 59465757918021512465248714460601822544044032)) else (if j.val < 31 then 101210273454847075189427060540606297230520709384089 else (if j.val < 32 then 202419119662002773646968847711116048772964242624307 else 7674344956984660243378163721233207416726521116696)))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then 15348689913969320486756327442466414833453042233392 else (if j.val < 35 then 30698124288993218002294660301565859213547017863071 else 61394821330295059272702809292997040280246567305023)) else (if j.val < 37 then 7422536127158329330716468034303927600123582875527 else (if j.val < 38 then 14843645006625281929546424758473177053399697329935 else 101209704238678442017642957641387444182672776095718))) else (if j.val < 42 then (if j.val < 40 then 202417981229665507303400641912678342677269449789388 else (if j.val < 41 then 7675194377965172852170280817743089021609704323559 else 15348961508238968972454050325351499896371940225999)) else (if j.val < 43 then 30698668522879946154814347288176626897142981720160 else (if j.val < 44 then 61395909798068515577743421206256708106209861038272 else 7422536127158329330716468034303927617715768919943)))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then 14843645006625281929546424758473177088584069418767 else 29687290013249234631098302541111582828878150770207) else (if j.val < 48 then 59374580026498469262196605082223165657755227798591 else (if j.val < 49 then 118747732805304232564512151878476881820375146592382 else 237494038362917088397137792446819085493903898505468))) else (if j.val < 53 then (if j.val < 51 then 6305571908247757794161003646850370494509714235776 else (if j.val < 52 then 12609716568804138856435495983566062842173033792256 else 93998677301737401693457651439688729924567157473273)) else (if j.val < 54 then 187997354603474803386915302879377459849133241204723 else (if j.val < 55 then 24871175782937881200447778433849736609398110820760 else 49740924318184385669009045557564795071949826962224)))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then 30697252293390712155363444232980189229527911604120 else 61394504586781424310725650525922246000285530930992) else (if j.val < 59 then 7422223383961664595426984870469699938176820942951 else (if j.val < 60 then 14844446767923329190853969740939399876352568144079 else 358559641326783821797707212304810854939181056))) else (if j.val < 64 then (if j.val < 62 then 717119282653567643595414424609621709878362112 else (if j.val < 63 then 6990873930403401917458752673555343654322176 else 13981747860806803834917505347110687308644352)) else (if j.val < 65 then 1088125296533963061647648400552399422555234303 else (if j.val < 66 then 707843150771375785333864025767997061341184 else 748316926999409515982038049555201735441276927))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then 769594173287325733077417380846600575619473408 else 111940655197919579643524627015054304844267520) else (if j.val < 70 then 223881310395839159287049254030108609688535040 else (if j.val < 71 then 89202980794122492566142873090593446023921664 else 178405961588244985132285746181186892047843328))) else (if j.val < 75 then (if j.val < 73 then 356811923176489970264571492362373784095686656 else (if j.val < 74 then 713623846352979940529142984724747568191373312 else 358559641326783821792871507873430833633492992)) else (if j.val < 76 then 717119282653567643585743015746861667266985984 else (if j.val < 77 then 362762867609023068462002184070623041019772928 else 725525735218046136924004368141246082039545856)))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then 726102888672271938383158191617087084556984319 else (if j.val < 80 then 724817987771690457812191819633134508158492672 else 22388284166649030351013542720580940214583296)) else (if j.val < 82 then 44776568333298060702027085441161880429166592 else (if j.val < 83 then 89553136666596121404054170882323760858333184 else 179106273333192242808108341764647521716666368))) else (if j.val < 87 then (if j.val < 85 then 358212546666384485616216683529295043433332736 else (if j.val < 86 then 716425093332768971232433367058590086866665472 else 364151246250620413168621444553678054401310720)) else (if j.val < 88 then 728302492501240826337242889107356108802621440 else (if j.val < 89 then 731656360703365452092327300627481209110011903 else 713623846352979941150530856006666963990355968))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then 118475653122976247547986156088337795447120564582905 else 236949878998261118364087038806579045206163953021939) else (if j.val < 93 then 7407413425611039053387397484139370223572042774624 else (if j.val < 94 then 14813399603530701374889521598182194759067983147200 else 101329046711188499482102460606684882549193074808953))) else (if j.val < 98 then (if j.val < 96 then 202658093422376998964203683273331632639614783598835 else (if j.val < 97 then 122791115026441485051855287026633718420900388692382 else 245580802805191593371825300683170891153724674982716)) else (if j.val < 99 then 25219433137608282904850937851901543960556873942528 else (if j.val < 100 then 50437439027525189077816602333706542233037645483008 else 29349966146094426243126028754698935914801746010616)))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then 58699932292188852486250819569359739370833199743984 else 117399864584377704972501639138718325820161792640993) else (if j.val < 104 then 234799729168755409945003278277436651640322511540163 else (if j.val < 105 then 118475653122976242355688059613470881518757150194169 else 236949878998261107979490845856845217349437124244467))) else (if j.val < 109 then (if j.val < 107 then 122773449523336457897148252318447466929142118613401 else (if j.val < 108 then 245546899046672915794296504636894933858283163484979 else 25332229794219958251586380550908311373787963988448)) else (if j.val < 110 then 50664459588439916503171523161778490288805635699648 else (if j.val < 111 then 101329601963520620393430902775691491612436532852862 else 202657776679349864054975294241248305078026671026428))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then 122791069908281490084994033421262997718073981533822 else 245582139816562980169986828902487862977377670790396) else (if j.val < 115 then 25218930823659315277043943583113631279452359091839 else (if j.val < 116 then 50436434399627253822202613796130716870827542039807 else 29350811320414885374634682070161579107673041297415))) else (if j.val < 120 then (if j.val < 118 then 58700195393138394017384090770226612527268906450959 else (if j.val < 119 then 117400390786276788034766943600413939674263987519518 else 234800781572553576069532649260789746889757682761788)) else (if j.val < 121 then 358559639997555826007955634969623773353148416 else (if j.val < 122 then 717119279995111652015911269939247546706296832 else 362762872925935051601665675685851282141151232)))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then 725525745851870103203331351371702564282302464 else (if j.val < 125 then 726102867404624005824504225156174120071471103 else 724817945236394592694883886711308579187466240)) else (if j.val < 127 then 22388199096057300116397676876929082272530432 else (if j.val < 128 then 44776398192114600232795353753858164545060864 else 447415527460506978182360741823195225312722944))) else (if j.val < 132 then (if j.val < 130 then 894831054921013956364721483646390450625445888 else (if j.val < 131 then 7339323074130442904045248271565474302853120 else 14678646148260885808090496543130948605706240)) else (if j.val < 133 then 1089519093108871225593994382944439945149358079 else (if j.val < 134 then 3495436300587703678025828809849042249588736 else 753892113299042171767421979123363825817772031)))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then 758443800688060421506649521710276394866483200 else 89639909999388956501988908742405943338287104) else (if j.val < 138 then 179279819998777913003977817484811886676574208 else (if j.val < 139 then 0 else 0))) else (if j.val < 143 then (if j.val < 141 then 0 else (if j.val < 142 then 0 else 0)) else (if j.val < 144 then 0 else (if j.val < 145 then 0 else 0)))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then 0 else 0) else (if j.val < 149 then 0 else (if j.val < 150 then 0 else 118474225875283536395807001327501432023620767447545))) else (if j.val < 154 then (if j.val < 152 then 236947024502875696059728729284906318359164358751219 else (if j.val < 153 then 122767740532565634057624019174569668948596587626905 else 245535481065131268115248038349139337897192101511987)) else (if j.val < 155 then 25309393831136662893489447975397119451605840042464 else (if j.val < 156 then 50618787662273325786977658010756106444441387807680 else 101238258111187438961043172473646723923708037068926))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 202475088974683501190199833637158769700569679458556 else 7789338784183755827851588993624819319677619537799) else (if j.val < 160 then 15577250320676134923816666677114960492507770654479 else (if j.val < 161 then 99753911592118383708150940091859473265547691419622 else 199506395936545390684416606813622400843019280437196))) else (if j.val < 165 then (if j.val < 163 then 1852023791724773460702737505147092377226830576103 else (if j.val < 164 then 3702620335758170189518963700159506607606192731087 else 7405986177918348588944174037792640319611486730336)) else (if j.val < 166 then 14810545108145320446003074705488734951146871058624 else (if j.val < 167 then 29618913280743728281923687644418848887685515312766 else 59237826561487456563846137348799565316600738348284)))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then 0 else (if j.val < 170 then 0 else 0)) else (if j.val < 172 then 0 else (if j.val < 173 then 0 else 0))) else (if j.val < 177 then (if j.val < 175 then 0 else (if j.val < 176 then 0 else 0)) else (if j.val < 178 then 0 else (if j.val < 179 then 0 else 0)))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then 749688876382978958823875321430561031208837118 else 72130061389226032374380546315433986315272188) else (if j.val < 183 then 889767609436706531443456214837564210918481927 else (if j.val < 184 then 352287527496681177613542333129440344660819983 else 1383179221405980390999994063374620687410503648))) else (if j.val < 188 then (if j.val < 186 then 1339110751435228895488677992071094528426328000 else (if j.val < 187 then 569232518137519939496817638735101970454831231 else 1138465036275039878993635277470203939835920639)) else (if j.val < 189 then 849682381173347871475960420262261032203420159 else (if j.val < 190 then 272117070969963856440610705846375216938419199 else 544234141939927711643281373560291662510819327)))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then 1088468283879855422048622708988124553655619583 else 0) else (if j.val < 194 then 0 else (if j.val < 195 then 0 else 0))) else (if j.val < 199 then (if j.val < 197 then 0 else (if j.val < 198 then 0 else 0)) else (if j.val < 200 then 0 else (if j.val < 201 then 0 else 0))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then 0 else 0) else (if j.val < 205 then 0 else (if j.val < 206 then 0 else 0))) else (if j.val < 210 then (if j.val < 208 then 0 else (if j.val < 209 then 0 else 0)) else (if j.val < 211 then 0 else (if j.val < 212 then 0 else 0)))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then 0 else (if j.val < 215 then 0 else 0)) else (if j.val < 217 then 0 else (if j.val < 218 then 0 else 0))) else (if j.val < 222 then (if j.val < 220 then 0 else (if j.val < 221 then 0 else 0)) else (if j.val < 223 then 0 else (if j.val < 224 then 0 else 0)))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then 0 else 0) else (if j.val < 228 then 0 else (if j.val < 229 then 0 else 0))) else (if j.val < 233 then (if j.val < 231 then 0 else (if j.val < 232 then 0 else 0)) else (if j.val < 234 then 0 else (if j.val < 235 then 0 else 0)))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then 0 else 0) else (if j.val < 239 then 0 else (if j.val < 240 then 0 else 0))) else (if j.val < 244 then (if j.val < 242 then 0 else (if j.val < 243 then 0 else 0)) else (if j.val < 245 then 0 else (if j.val < 246 then 0 else 0))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then 0 else 0) else (if j.val < 250 then 0 else (if j.val < 251 then 0 else 0))) else (if j.val < 255 then (if j.val < 253 then 0 else (if j.val < 254 then 0 else 0)) else (if j.val < 256 then 0 else (if j.val < 257 then 0 else 0)))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then 0 else (if j.val < 260 then 0 else 0)) else (if j.val < 262 then 0 else (if j.val < 263 then 0 else 0))) else (if j.val < 267 then (if j.val < 265 then 0 else (if j.val < 266 then 0 else 0)) else (if j.val < 268 then 0 else (if j.val < 269 then 0 else 0))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then 0 else 0) else (if j.val < 273 then 0 else (if j.val < 274 then 0 else 0))) else (if j.val < 278 then (if j.val < 276 then 0 else (if j.val < 277 then 0 else 0)) else (if j.val < 279 then 0 else (if j.val < 280 then 0 else 0)))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then 0 else 0) else (if j.val < 284 then 0 else (if j.val < 285 then 0 else 0))) else (if j.val < 289 then (if j.val < 287 then 0 else (if j.val < 288 then 0 else 0)) else (if j.val < 290 then 0 else (if j.val < 291 then 0 else 0))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then 0 else 0) else (if j.val < 295 then 0 else (if j.val < 296 then 0 else 0))) else (if j.val < 300 then (if j.val < 298 then 0 else (if j.val < 299 then 0 else 0)) else (if j.val < 301 then 0 else (if j.val < 302 then 0 else 0)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then 0 else (if j.val < 305 then 0 else 0)) else (if j.val < 307 then 0 else (if j.val < 308 then 0 else 0))) else (if j.val < 312 then (if j.val < 310 then 0 else (if j.val < 311 then 0 else 0)) else (if j.val < 313 then 0 else (if j.val < 314 then 0 else 0)))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 0 else 0) else (if j.val < 318 then 0 else (if j.val < 319 then 0 else 0))) else (if j.val < 323 then (if j.val < 321 then 0 else (if j.val < 322 then 0 else 0)) else (if j.val < 324 then 0 else (if j.val < 325 then 0 else 0)))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then 0 else 0) else (if j.val < 329 then 0 else (if j.val < 330 then 0 else 0))) else (if j.val < 334 then (if j.val < 332 then 0 else (if j.val < 333 then 0 else 0)) else (if j.val < 335 then 0 else (if j.val < 336 then 0 else 0))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then 0 else 0) else (if j.val < 340 then 0 else (if j.val < 341 then 0 else 0))) else (if j.val < 345 then (if j.val < 343 then 0 else (if j.val < 344 then 0 else 0)) else (if j.val < 346 then 0 else (if j.val < 347 then 0 else 0)))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then 0 else (if j.val < 350 then 0 else 0)) else (if j.val < 352 then 0 else (if j.val < 353 then 0 else 0))) else (if j.val < 357 then (if j.val < 355 then 0 else (if j.val < 356 then 0 else 0)) else (if j.val < 358 then 0 else (if j.val < 359 then 0 else 0)))))))))
def xrem (j : Fin 360) : BitVec 360 := BitVec.ofNat 360 (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then 193236218465751787753589064856756629254910659297832386572706362168794005037705755538722030974467484738912256 else 386472436931503575507178127816375670212479837554262084346367542812531097141040406730589963684892454749732864) else (if j.val < 3 then 1906905234706788590104501587153092255450339730076597438460117806797535219950033095805352896720768150517317632 else (if j.val < 4 then 1151230873759403882575312794077266931951842174290331950565628136126224854931504772224032012763832187355136 else 2302459560268085019174677550138393014728007404789394059387213512418093936050459699453440565351193535053824))) else (if j.val < 8 then (if j.val < 6 then 4604916933285447292373407062260645180280337865787518277030384265001832098288369553912257670525916230451200 else (if j.val < 7 then 46013318105420408142031141231024719662677990895153154065188530243776748890849046281511472783100366307721216 else 92026634023590093538086334424033298476180304846515038288633017727719142007885542718028322106024261775785984)) else (if j.val < 9 then 147536466767236017333868385813860933709324477552248037938856908838428717944906786040662150184976571728658432 else (if j.val < 10 then 295072931347221311921760823589705726569473278160704806035969774917023080116001022236329676909776672617660416 else 2016312284298150389369224754278240898564831729699352741444625581410094526004181445876761486983453863225327616)))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then 367322617214654229099846008294049766915107267968862506016601980273883969923182959060243564533862229725937664 else 1904047319129922450674851721926542598490042764101028666141627711804373819770147559560531677395840008770813952) else (if j.val < 14 then 4609396422769802900794521946821782068836581156800818881306344463901228638545338007337072673032743596064768 else (if j.val < 15 then 46022277084389119358873371000146993439790477477179755273740449927951695618383042659218118063366452847575040 else 92044551981527515971770793962277846030405278010568240705736857096069035462953535473441612666556434855493632))) else (if j.val < 19 then (if j.val < 17 then 184089101775804307160529665449191055007377736487754068900603960034342893277809072969980358495248408708644864 else (if j.val < 18 then 368178201364357891575083382860365969165579796031716867959463877308851430781805596094966093530320346577633280 else 1906905234502814327395476033876823594309664025475827242930301556341145993354109964896241278800651668282146816)) else (if j.val < 20 then 1151230470082787351214783702775284011783581010152742954177859226674341001720003085167144737200635386003456 else (if j.val < 21 then 2302458752914851956453619367534427174391485076514216066611675693514326229627456325339666014224799932350464 else 4604915318578981166931290697052713499607293209237162291479308627194296685442362805684708568273129025044480))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then 46013317063258198637122856538624997150507578525843711935830421772597524236030828913122434584067985748525056 else 92026634126516397274245713077249994301015157051687423871660843545195048472061657826244869168135971497050112) else (if j.val < 25 then 147536466971486661010465493274678201860334152673154126406068467567729190777283394581173025449714562298281984 else (if j.val < 26 then 295072931755722599274955038511340262871492628402516982970392892375624025780754239317351427439252653756907520 else 2016312284570501268166657078101411002739961777827009240600472284499765741895301279959216615443658107860811776))) else (if j.val < 30 then (if j.val < 28 then 367322618848709440708785034986169526327235962101473881937836830136158633305516054204886551381796247251714048 else (if j.val < 29 then 1867243834352879286918688662342435167748626062789180159882784929189946334371556666799506897733061076968275968 else 78359709686529171397148353141990747354273188939549011831885952485955771606609478942935562146801486345011200)) else (if j.val < 31 then 1169970084890741329205904996253422399379732160051135995741530013613418639734698980036945151140166550624927744 else (if j.val < 32 then 2339940169781482656374774018069496302555207177512680848813934315828876457595112511941982058902645111087169536 else 1453200998403913300056139008302188690156262791648951024736847311112222566201620482425967379799377806262009856)))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then 557859416221244094968773369750194082083360194020280694728398917132096558554166680562820348571785758408441856 else (if j.val < 35 then 2110234794965806817928514024580781295034579651419857220703510874250918512736096180392626395855974924734693376 else 1871927009345031132750559376744727789811098119284564001592943213395398606767536916520929716550694323460505600)) else (if j.val < 37 then 2278608568375477203524631384631916763848810076451565702104360516340869422097346451179989952504357819131101184 else (if j.val < 38 then 2208674556164371903942794096846998727439558969347980964394642497575300425490037458095656829847460112253321216 else 1192389971685726730907082581768087206412428484820472522171711886666987649089513206696032351362363766570221568))) else (if j.val < 42 then (if j.val < 40 then 36237362784870958707696491119339612566795786085794604529345238227536879474370969127741627563472007131561984 else (if j.val < 41 then 950584607018050395064023462135927806497688519043899750313390581845865904753705661697994241201695316563197952 else 1901169214036100788091010949834507115024272832365328585695563993705821654362992483371197146537676305019699200)) else (if j.val < 43 then 17201305240117275029179672489850243446150982587031153538780877817452641709123028354138752259525466988216320 else (if j.val < 44 then 34402610480234548021323370542351988921197759451591392146344585648995128273827216683486168653336605869735936 else 2278608568375477203524631384631916763848850516371572704782664018327791572743193357775462569813839158035087360)))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then 2208674556164371903942794096846998727439639849187994969751249501549144726781731271286602064466422790061293568 else 2068806529554910582033143573239146513772042837877048229846676425232016679084994548463886430311413583274049536) else (if j.val < 48 then 1789070478523238660959818474061458227286024492198946019879274315357594939465333652663449785461571640539217920 else (if j.val < 49 then 1229598374272644094030156353230717015493707918176479415171508882863006949307780471192790536435996956123201536 else 110654167958705682916808059607250732758250447075337475597722060633665324766486658096466661845024058130825216))) else (if j.val < 53 then (if j.val < 51 then 1243345861884743602512314717229744664776000735027969755903260161033351580577617101722575160734466287637364736 else (if j.val < 52 then 138149143182904701918160762042654529293940286500789071992441786960264742450578759180827246307677049265848320 else 1159595416637806844966302827644605043072555594439166282765326684229099138991783925362555249167664394318905344)) else (if j.val < 54 then 2319190833275613689932605655289210086145111188878332565530653368458198277983567850725110498335328788637810688 else (if j.val < 55 then 1411702430380210175185184523803249442418397608783961625435594098610086154998735331794628604238686158288060416 else 474862280173837847263900375189664084578734034012772811057109662113733891292815219324934133316116790567239680)))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then 73334772240116617951615693995278862473812023189943337257861734073471881116817161303609229696405749691842560 else 146669544480233233866195413553209226976519840657415759584506298161033607089215482582427123527097171276988416) else (if j.val < 59 then 2055902227097345804042117912397743343343719921191742144720275292027401345108836077295851765877894040145362944 else (if j.val < 60 then 1763261873608109102940731177941303388458274453105862934695254878962454116368597870302589120728818226175148032 else 36884118332046018951298315145049789051583740894762786593558084152803369199539969921751957030512487166902272))) else (if j.val < 64 then (if j.val < 62 then 73768234476841315156620680354945848956650323804331614546326944020715469690896285651655192336805988766056448 else (if j.val < 63 then 147536466766431905530229438234527059093020764942401044319692675295686428463561181433524425347721178585759744 else 295072931345613088314482928431037977336865852941010818797641307831538501153309813022054227235265886331863040)) else (if j.val < 65 then 2016312284297094927696095336075764460250404646073436853499369235372263894795397305057431089455794009011126272 else (if j.val < 66 then 367322617208271396866896594665003806222199593815399852026157415251785573241696492463032212853477284494966784 else 1904047319134244421755715204513391808392535716310520379751637414679913277843774866811547728728155423529500672))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then 4609396448501380617240847331212155328549969596181224663900216397046518942727538346822873301431587017064448 else 9218790709752036451469770289922085306325638617577348017885497111240947302985974369888781500956198303694848) else (if j.val < 70 then 18437579232253350156963590644690441466134119249960737394981769937590625897788294547928841277693411039641600 else (if j.val < 71 then 205054755480236055040148428890221466883256167912667859655497678204972321748833069299610073052479488 else 410109510960472110080296857780442933766512335825335719310995356409944643497666138599220146104958976))) else (if j.val < 75 then (if j.val < 73 then 820219021920944220160593715560885867533024671650671438621990712819889286995332277198440292209917952 else (if j.val < 74 then 1640438043841888440321187431121771735066049343301342877243981425639778573990664554396880584419835904 else 36875159353077307734456084416242677465310359082501808707020219286509388415709330447454561201863999499534336)) else (if j.val < 76 then 73750316518903892722936220794469214081445041221212347572296395813184421057606111049914498943551528159412224 else (if j.val < 77 then 184089101776602161189648342197285972969104751462189257501171489707916679552244606811332054087418040960417792 else 368178201365953599633320736356555805089033825980587245160598936655999003330676663777669484714659611081179136)))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then 1906905234501733834624265532112249074024586526234131242078219151634569843314372382094592919627186184246001664 else (if j.val < 80 then 1151230463649892922103202712390904080445434489357939186768317810195471583610077350704077825599899644723200 else 2302458740049063098230457386765667311715192034924608531792592860556587393407604856413532191023328449789952)) else (if j.val < 82 then 4604915292847403450484966735515193774254707126057947221841142961278819013002659867832440921870186059923456 else (if j.val < 83 then 9209830585694804863933959033681891344252271662524751774556574524596816151719871603756638466052381957160960 else 18419661171389609727867918067363782688504543325049503549113149049193632303439743207513276932104763914321920))) else (if j.val < 87 then (if j.val < 85 then 36839322342779219455735836134727565377009086650099007098226298098387264606879486415026553864209527828643840 else (if j.val < 86 then 73678644685558438911471672269455130754018173300198014196452596196774529213758972830053107728419055657287680 else 184232445443293066775541464809965558611042222188142503015805004640145828037806017334857713450177381779111936)) else (if j.val < 88 then 368464888699335410805106981581914976372908767432493736189865966520457300301799484824720803440178292718567424 else (if j.val < 89 then 1906331859843414198998909102761281676007763197664522656013828769539529186894001792292578604194856484802134016 else 4481129922399450309556634159781063579166492881176644134400796468795675369416165811793805599869713252352))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then 2059288576789496438408815539648236270056493641840185580028310512799369943548745806464675519084658045147414528 else 1770034572992410371674126432442289243650668957535629577573416779094340646518550720533119719630372574123261952) else (if j.val < 93 then 1191526563210987517495808242532589957896759573530914756691965798797351605624262342610067642375270636669894656 else (if j.val < 94 then 34510545835392531885147812648345115535457963506679073569853062488264792543869240955812209589285747330908160 else 954038240917007248709120819077916800560364164202130812229381777971156389438227971504450129525812486316490752))) else (if j.val < 98 then (if j.val < 96 then 1908076481834014495381205663718485103149624122681790709527546385956402623732037102984108923185910644526284800 else (if j.val < 97 then 3494277391931082449615134061380263627877690563869501903351812296942990358313448220534760030639919024046080 else 6988554783862162862194293685412029284651175405268088875486454607975825572208056416278184195565509941395456)) else (if j.val < 99 then 1450569578299538702044303799621107101150984336070327137306925070082874418249046616548935340889828752518807552 else (if j.val < 100 then 552596576012494898945102952388030905839650345995912692130645893661349595919152340701639363240713988866048000 else 220175867169222657689373367267320693615183072793798260332670088623572026624106889701281722328142573167706112)))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then 440351734338445315378746734534641387230366145587596520665340177247144053248213779402563444656285146335412224 else 880703468676890630757493469069282774460732291175193041330680354494288106496427558805126889312570292670824448) else (if j.val < 104 then 1761406937353781261514986938138565548921464582350386082661360708988576212992855117610253778625140585341648896 else (if j.val < 105 then 2059288576789496437378361791433883686502468442358454887923794506999721716659288539193853782139020047038808064 else 1770034572992410371650254910450932572746875701161759336033510478893005014613921634123384489116784568068734976))) else (if j.val < 109 then (if j.val < 107 then 2069663218795422219117109398976501641020768190654805616593553667104915253762221244714515411362841474218590208 else (if j.val < 108 then 1790783857004261935127750125536168481783475197754460793373028799103392088819787045164707747564427422428299264 else 1233025131234690642366019656180137524488609329287508962159017850354601248016687256195306460641708519901364224)) else (if j.val < 110 then 117507681882798779588534665506091750748053269297396569572739995616853922184300228101498510256447185687150592 else (if j.val < 111 then 1229531326288916187168036616092576632363965801974088970392193031220433239996363275469982719225297779292110848 else 110520071991249871229604559768318464469870420393027500970307527334428061288071106675642363289340032575340544))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then 221040141795249019713233171498620788090565163842263732098871011909021766802329663506290103118503594311024640 else 442080283590498039426466342997241576181130327684527464197742023818043533604659327012580206237007188622049280) else (if j.val < 115 then 884160567180996078852932685994483152362260655369054928395484047636087067209318654025160412474014377244098560 else (if j.val < 116 then 1768321134361992157705865371988966304724521310738109856790968095272174134418637308050320824948028754488197120 else 2073090093869007924259912436799813699000474576981461786215072481427320262013584966794586797131933301356888064))) else (if j.val < 120 then (if j.val < 118 then 1797637607151433345413356201182792597742887970407773132616066427748202105322514489324850519102611076704894976 else (if j.val < 119 then 1246732631529033462937231807473385756407434874594133640645093107644221281022142144515592003718075828454555648 else 144922682471484420730958968092588214585704359910645926544890510196093988195210004742069596409181802793533440)) else (if j.val < 121 then 36875158259451942796655151811883956070942565894194391946078508985628585615924613369406045317774437882265600 else (if j.val < 122 then 73750316518903885593310303623767912141885131788388783892157017971257171231849226738812090635548875764531200 else 184089101776602173411864202101340080643967427738245242192324533993810357329472927301628627325735355587493888)))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then 368178201365953624077752456164664020438759178532699214542905025227786358885133304758262631191294240335331328 else (if j.val < 125 then 1906905234501733818327977713847810023620266835679957880137101273324381103971951274935793169068491116719898624 else 1151230463649795144376323479958042681544024280910061657543963879857972542273483692902984281435166723801088)) else (if j.val < 127 then 2302458740048867542776698921899944513912371618028853473343884999881589310734417540811345102693862607945728 else (if j.val < 128 then 4604915292847012339577449805783748178649066292266437104943727239928822847656285236628066745211254376235008 else 46013317011794260982415174756087066508591124691902261562759258953465086163397427491937714392647513438945280))) else (if j.val < 132 then (if j.val < 130 then 92026634023588521964830349512174133017182249383804523125518517906930172326794854983875428785295026877890560 else (if j.val < 131 then 147536466767232900668824110324527638893373192547413763725601534122464355139581670811501951026243053360775168 else 295072931347215078591672272611039136937570708151036257609459025485094354505350791778009278592309635881893888)) else (if j.val < 133 then 2016312284298162921214553114353371757745644804378885026600648017909428559891657042843560551619858546024251392 else (if j.val < 134 then 367322617214679357975653971385008444625019014655501607273428285866008986649860407486852418281652282695090176 else 1904047319129972447685862677294240911548818141073902254067325933748783771797524939052943015184321723234254848)))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then 4609396422869536182211340451193601717272286235774203674816733962453610508602501393077769861379955722551296 else 9218790658488347581410756529884978083770271896763306039718532242055130434735900462398574620852935714668544) else (if j.val < 138 then 18437579129725972416845563124616227021023385808332653438647840199218992161288146732948427517486885861588992 else (if j.val < 139 then 348449143727040986586495598010130648530944 else 696898287454081973172991196020261297061888))) else (if j.val < 143 then (if j.val < 141 then 1393796574908163946345982392040522594123776 else (if j.val < 142 then 2787593149816327892691964784081045188247552 else 5575186299632655785383929568162090376495104)) else (if j.val < 144 then 11150372599265311570767859136324180752990208 else (if j.val < 145 then 22300745198530623141535718272648361505980416 else 44601490397061246283071436545296723011960832)))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then 89202980794122492566142873090593446023921664 else 178405961588244985132285746181186892047843328) else (if j.val < 149 then 356811923176489970264571492362373784095686656 else (if j.val < 150 then 713623846352979940529142984724747568191373312 else 885017282668516417454856587573587388917600461212833163947647164994896567736580775387978483668733524547993600))) else (if j.val < 154 then (if j.val < 152 then 1770034565337032834909713175147174777835200922425666327895294329989793135473161550775956967337467049095987200 else (if j.val < 153 then 2069663231918926569852216921546001089994942071183200363028241922151504656269928861564375831461300041324429312 else 1790783883251270636597965170675167379731822958811250286242405309196570893835202278864428587761344556639977472)) else (if j.val < 155 then 1233025183728708045306449746458135320385304851401087947897770870540958858047517723594748141035542788324720640 else (if j.val < 156 then 117507786870833585469394846062087342541444313524554541050246035989569142245961162900381871044115722533863424 else 1229531116312846575406316254980585448777183713519773028203428720907947229052214919447370589459330266690486272))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then 110519652039110647706163837544336097296306243484395616592778906709456039399774394630418103757405007372091392 else 1104336434350218736542308978647968179077287508406379371918110438075422706066476851663289802079034712963153920) else (if j.val < 160 then 2208672868700437473084617957295936358154575016812758743836220876150845412132953703326579604158069425926307840 else (if j.val < 161 then 1192386625192117293502407357248477929356193882409015531146388829829400102950344556463130557820095287663788032 else 36230669797652083898346042080121058454326581262880622478699124552361787196033668661938040478935049318694912))) else (if j.val < 165 then (if j.val < 163 then 950597992992488144682724360214364914722626928689727714414682809196216089310380262629601415370769232188932096 else (if j.val < 164 then 1901195985984976287328412745991381331474149651656984513898148448406522023476341685234411494875824136271167488 else 17255269090007498555200969515587806978826632613481893174120308809718947575628869869541407147834334926340096)) else (if j.val < 166 then 34510538180014995073365964593827115986549059504492871417023447633527740006838899714291478429954341745983488 else (if j.val < 167 then 1395525611507233037621960457804276927747188567871877572271741569683829616203483274551355914409136686477869056 else 442508642427883570100416268754370559032058809599013562060278892863259991828025656706480510279329856784171008)))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then 374144419156711147060143317175368453031918731001856 else (if j.val < 170 then 748288838313422294120286634350736906063837462003712 else 1496577676626844588240573268701473812127674924007424)) else (if j.val < 172 then 2993155353253689176481146537402947624255349848014848 else (if j.val < 173 then 5986310706507378352962293074805895248510699696029696 else 11972621413014756705924586149611790497021399392059392))) else (if j.val < 177 then (if j.val < 175 then 23945242826029513411849172299223580994042798784118784 else (if j.val < 176 then 47890485652059026823698344598447161988085597568237568 else 95780971304118053647396689196894323976171195136475136)) else (if j.val < 178 then 191561942608236107294793378393788647952342390272950272 else (if j.val < 179 then 383123885216472214589586756787577295904684780545900544 else 766247770432944429179173513575154591809369561091801088)))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then 1464116656876698135595828982809993021763763482136629129725438670156112308187582475650975390167555931352596480 else 579690733166813768085189293203151241502618717585228047374707346617836864400376115144744612685829998752301056) else (if j.val < 183 then 2073049502870051101414939866464543989082556899679215422325853309589130382313264883019104929581591382563225600 else (if j.val < 184 then 1797556425153519697686375086074904679935948410080809489906410914085912190777455481749095448136212911010873344 else 224534392940171400680650878691893946427289618887502670212695425801797780072069374204103652937150364731310080))) else (if j.val < 188 then (if j.val < 186 then 449068785880342799324265782946439394883475032052534425494173681617685404999719908383415970008586401355923456 else (if j.val < 187 then 2334723426246307204474628395542804785391231457837729520652401051007134118571827435226933602305086657797292032 else 2320904271906031903805752144231426274320144589530717458821597855509868996564713978057635886071229799423016960)) else (if j.val < 189 then 2293265961038230581759059666110864019235710837521090519188327951628408305716588857659099975256985087269404672 else (if j.val < 190 then 2237989341489878660411650659804893238213360491487030598562577368150378192728522271053876875352714648529928192 else 2127436100205924092933820724717587037348379916752648572538114988448573455834157707973644716218282972104622080)))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then 1906329619825265680724136802580990776467594444227675790330934271804798337819241131658175021409596090093666304 else 6277101735386680763835789423207666416102355444464034512896) else (if j.val < 194 then 12554203470773361527671578846415332832204710888928069025792 else (if j.val < 195 then 25108406941546723055343157692830665664409421777856138051584 else 50216813883093446110686315385661331328818843555712276103168))) else (if j.val < 199 then (if j.val < 197 then 100433627766186892221372630771322662657637687111424552206336 else (if j.val < 198 then 200867255532373784442745261542645325315275374222849104412672 else 401734511064747568885490523085290650630550748445698208825344)) else (if j.val < 200 then 803469022129495137770981046170581301261101496891396417650688 else (if j.val < 201 then 1606938044258990275541962092341162602522202993782792835301376 else 3213876088517980551083924184682325205044405987565585670602752))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then 6427752177035961102167848369364650410088811975131171341205504 else 12855504354071922204335696738729300820177623950262342682411008) else (if j.val < 205 then 25711008708143844408671393477458601640355247900524685364822016 else (if j.val < 206 then 51422017416287688817342786954917203280710495801049370729644032 else 102844034832575377634685573909834406561420991602098741459288064))) else (if j.val < 210 then (if j.val < 208 then 205688069665150755269371147819668813122841983204197482918576128 else (if j.val < 209 then 411376139330301510538742295639337626245683966408394965837152256 else 822752278660603021077484591278675252491367932816789931674304512)) else (if j.val < 211 then 1645504557321206042154969182557350504982735865633579863348609024 else (if j.val < 212 then 3291009114642412084309938365114701009965471731267159726697218048 else 6582018229284824168619876730229402019930943462534319453394436096)))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then 13164036458569648337239753460458804039861886925068638906788872192 else (if j.val < 215 then 26328072917139296674479506920917608079723773850137277813577744384 else 52656145834278593348959013841835216159447547700274555627155488768)) else (if j.val < 217 then 105312291668557186697918027683670432318895095400549111254310977536 else (if j.val < 218 then 210624583337114373395836055367340864637790190801098222508621955072 else 421249166674228746791672110734681729275580381602196445017243910144))) else (if j.val < 222 then (if j.val < 220 then 842498333348457493583344221469363458551160763204392890034487820288 else (if j.val < 221 then 1684996666696914987166688442938726917102321526408785780068975640576 else 3369993333393829974333376885877453834204643052817571560137951281152)) else (if j.val < 223 then 6739986666787659948666753771754907668409286105635143120275902562304 else (if j.val < 224 then 13479973333575319897333507543509815336818572211270286240551805124608 else 26959946667150639794667015087019630673637144422540572481103610249216)))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then 53919893334301279589334030174039261347274288845081144962207220498432 else 107839786668602559178668060348078522694548577690162289924414440996864) else (if j.val < 228 then 215679573337205118357336120696157045389097155380324579848828881993728 else (if j.val < 229 then 431359146674410236714672241392314090778194310760649159697657763987456 else 862718293348820473429344482784628181556388621521298319395315527974912))) else (if j.val < 233 then (if j.val < 231 then 1725436586697640946858688965569256363112777243042596638790631055949824 else (if j.val < 232 then 3450873173395281893717377931138512726225554486085193277581262111899648 else 6901746346790563787434755862277025452451108972170386555162524223799296)) else (if j.val < 234 then 13803492693581127574869511724554050904902217944340773110325048447598592 else (if j.val < 235 then 27606985387162255149739023449108101809804435888681546220650096895197184 else 55213970774324510299478046898216203619608871777363092441300193790394368)))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then 110427941548649020598956093796432407239217743554726184882600387580788736 else 220855883097298041197912187592864814478435487109452369765200775161577472) else (if j.val < 239 then 441711766194596082395824375185729628956870974218904739530401550323154944 else (if j.val < 240 then 883423532389192164791648750371459257913741948437809479060803100646309888 else 1766847064778384329583297500742918515827483896875618958121606201292619776))) else (if j.val < 244 then (if j.val < 242 then 3533694129556768659166595001485837031654967793751237916243212402585239552 else (if j.val < 243 then 7067388259113537318333190002971674063309935587502475832486424805170479104 else 14134776518227074636666380005943348126619871175004951664972849610340958208)) else (if j.val < 245 then 28269553036454149273332760011886696253239742350009903329945699220681916416 else (if j.val < 246 then 56539106072908298546665520023773392506479484700019806659891398441363832832 else 113078212145816597093331040047546785012958969400039613319782796882727665664))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then 226156424291633194186662080095093570025917938800079226639565593765455331328 else 452312848583266388373324160190187140051835877600158453279131187530910662656) else (if j.val < 250 then 904625697166532776746648320380374280103671755200316906558262375061821325312 else (if j.val < 251 then 1809251394333065553493296640760748560207343510400633813116524750123642650624 else 3618502788666131106986593281521497120414687020801267626233049500247285301248))) else (if j.val < 255 then (if j.val < 253 then 7237005577332262213973186563042994240829374041602535252466099000494570602496 else (if j.val < 254 then 14474011154664524427946373126085988481658748083205070504932198000989141204992 else 28948022309329048855892746252171976963317496166410141009864396001978282409984)) else (if j.val < 256 then 57896044618658097711785492504343953926634992332820282019728792003956564819968 else (if j.val < 257 then 115792089237316195423570985008687907853269984665640564039457584007913129639936 else 231584178474632390847141970017375815706539969331281128078915168015826259279872)))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then 463168356949264781694283940034751631413079938662562256157830336031652518559744 else (if j.val < 260 then 926336713898529563388567880069503262826159877325124512315660672063305037119488 else 1852673427797059126777135760139006525652319754650249024631321344126610074238976)) else (if j.val < 262 then 3705346855594118253554271520278013051304639509300498049262642688253220148477952 else (if j.val < 263 then 7410693711188236507108543040556026102609279018600996098525285376506440296955904 else 14821387422376473014217086081112052205218558037201992197050570753012880593911808))) else (if j.val < 267 then (if j.val < 265 then 29642774844752946028434172162224104410437116074403984394101141506025761187823616 else (if j.val < 266 then 59285549689505892056868344324448208820874232148807968788202283012051522375647232 else 118571099379011784113736688648896417641748464297615937576404566024103044751294464)) else (if j.val < 268 then 237142198758023568227473377297792835283496928595231875152809132048206089502588928 else (if j.val < 269 then 474284397516047136454946754595585670566993857190463750305618264096412179005177856 else 948568795032094272909893509191171341133987714380927500611236528192824358010355712))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then 1897137590064188545819787018382342682267975428761855001222473056385648716020711424 else 3794275180128377091639574036764685364535950857523710002444946112771297432041422848) else (if j.val < 273 then 7588550360256754183279148073529370729071901715047420004889892225542594864082845696 else (if j.val < 274 then 15177100720513508366558296147058741458143803430094840009779784451085189728165691392 else 30354201441027016733116592294117482916287606860189680019559568902170379456331382784))) else (if j.val < 278 then (if j.val < 276 then 60708402882054033466233184588234965832575213720379360039119137804340758912662765568 else (if j.val < 277 then 121416805764108066932466369176469931665150427440758720078238275608681517825325531136 else 242833611528216133864932738352939863330300854881517440156476551217363035650651062272)) else (if j.val < 279 then 485667223056432267729865476705879726660601709763034880312953102434726071301302124544 else (if j.val < 280 then 971334446112864535459730953411759453321203419526069760625906204869452142602604249088 else 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176)))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then 3885337784451458141838923813647037813284813678104279042503624819477808570410416996352 else 7770675568902916283677847627294075626569627356208558085007249638955617140820833992704) else (if j.val < 284 then 15541351137805832567355695254588151253139254712417116170014499277911234281641667985408 else (if j.val < 285 then 31082702275611665134711390509176302506278509424834232340028998555822468563283335970816 else 62165404551223330269422781018352605012557018849668464680057997111644937126566671941632))) else (if j.val < 289 then (if j.val < 287 then 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 else (if j.val < 288 then 248661618204893321077691124073410420050228075398673858720231988446579748506266687766528 else 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056)) else (if j.val < 290 then 994646472819573284310764496293641680200912301594695434880927953786318994025066751066112 else (if j.val < 291 then 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224 else 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896 else 15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792) else (if j.val < 295 then 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584 else (if j.val < 296 then 63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168 else 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336))) else (if j.val < 300 then (if j.val < 298 then 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672 else (if j.val < 299 then 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344 else 1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688)) else (if j.val < 301 then 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376 else (if j.val < 302 then 4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752 else 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504)))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then 16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008 else (if j.val < 305 then 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016 else 65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032)) else (if j.val < 307 then 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064 else (if j.val < 308 then 260740604970814219042361048116400404614587954389239840081425977517360806369707098391474864128 else 521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256))) else (if j.val < 312 then (if j.val < 310 then 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512 else (if j.val < 311 then 2085924839766513752338888384931203236916703635113918720651407820138886450957656787131798913024 else 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048)) else (if j.val < 313 then 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096 else (if j.val < 314 then 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192 else 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384)))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768 else 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536) else (if j.val < 318 then 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072 else (if j.val < 319 then 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144 else 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))) else (if j.val < 323 then (if j.val < 321 then 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 else (if j.val < 322 then 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152 else 8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304)) else (if j.val < 324 then 17087896287367280659160173649356416916821636178853222159576332862577757806245124400183696695492608 else (if j.val < 325 then 34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216 else 68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432)))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then 136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864 else 273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728) else (if j.val < 329 then 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456 else (if j.val < 330 then 1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912 else 2187250724783011924372502227117621365353169430893212436425770606409952999199375923223513177023053824))) else (if j.val < 334 then (if j.val < 332 then 4374501449566023848745004454235242730706338861786424872851541212819905998398751846447026354046107648 else (if j.val < 333 then 8749002899132047697490008908470485461412677723572849745703082425639811996797503692894052708092215296 else 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592)) else (if j.val < 335 then 34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184 else (if j.val < 336 then 69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368 else 139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then 279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472 else 559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944) else (if j.val < 340 then 1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888 else (if j.val < 341 then 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776 else 4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552))) else (if j.val < 345 then (if j.val < 343 then 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104 else (if j.val < 344 then 17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208 else 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416)) else (if j.val < 346 then 71671831749689734737838152978190216899892655911508785116799651230841339877765150252188079784691427704832 else (if j.val < 347 then 143343663499379469475676305956380433799785311823017570233599302461682679755530300504376159569382855409664 else 286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328)))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656 else (if j.val < 350 then 1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312 else 2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624)) else (if j.val < 352 then 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248 else (if j.val < 353 then 9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496 else 18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992))) else (if j.val < 357 then (if j.val < 355 then 36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984 else (if j.val < 356 then 73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968 else 146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936)) else (if j.val < 358 then 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872 else (if j.val < 359 then 587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744 else 1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488)))))))))
def xD : Matrix (Fin 180) (Fin 360) (ZMod 2) := fun i j => entry (xcoef j) i
def xK : Matrix (Fin 360) (Fin 360) (ZMod 2) := fun i j => entry (xrem j) i
def zrowFormula (i : Fin 180) : BitVec 360 :=
  unit (eqb.symm (Sum.inl (er i-(0,0)))) ^^^
  unit (eqb.symm (Sum.inl (er i-(0,8)))) ^^^
  unit (eqb.symm (Sum.inl (er i-(2,16)))) ^^^
  unit (eqb.symm (Sum.inr (er i-(0,0)))) ^^^
  unit (eqb.symm (Sum.inr (er i-(0,1)))) ^^^
  unit (eqb.symm (Sum.inr (er i-(1,2))))
lemma zrow_formula_bits : ∀ i, zrow i = zrowFormula i := by decide +kernel
lemma zrow_formula_entry (i : Fin 180) (j : Fin 360) :
    entry (zrowFormula i) j = HZ polyA polyB (er i) (eqb j) := by
  cases hq : eqb j with
  | inl g =>
    have yes (t : Grp 6 30) : j = eqb.symm (Sum.inl (er i-t)) ↔ er i-g = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inl.injEq]
      constructor <;> intro h <;> linear_combination -h
    have no (t : Grp 6 30) : j ≠ eqb.symm (Sum.inr (er i-t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [zrowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HZ,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,Matrix.transpose_apply,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,8) (2,16) (er i-g) (by decide) (by decide) (by decide)
  | inr g =>
    have yes (t : Grp 6 30) : j = eqb.symm (Sum.inr (er i-t)) ↔ er i-g = t := by
      rw [Equiv.eq_symm_apply,hq,Sum.inr.injEq]
      constructor <;> intro h <;> linear_combination -h
    have no (t : Grp 6 30) : j ≠ eqb.symm (Sum.inl (er i-t)) := by
      intro h
      have hh := congrArg eqb h
      simpa only [Equiv.apply_symm_apply,hq,reduceCtorEq] using hh
    simp only [zrowFormula,entry_xor,unit_entry,yes,no,if_false,zero_add,add_zero]
    simp only [HZ,polyA,polyB,hq,Matrix.fromCols_apply_inl,Matrix.fromCols_apply_inr,Matrix.transpose_apply,BBCode.circulant,Finset.mem_insert,Finset.mem_singleton]
    exact indicator_three (0,0) (0,1) (1,2) (er i-g) (by decide) (by decide) (by decide)
lemma zrow_entry (i : Fin 180) (j : Fin 360) : entry (zrow i) j = zH i j := by
  rw [zrow_formula_bits,zrow_formula_entry]
  exact congrFun (congrFun ztable i) j
lemma xdecomp_bits : ∀ j, combination zrow (xcoef j) ^^^ xrem j = unit j := by decide +kernel
lemma xdecomp : zH.transpose * xD + xK = 1 := by
  have h := decomposition zrow xcoef xrem xdecomp_bits
  have he : (Matrix.of fun i j => entry (zrow i) j) = zH := by
    apply Matrix.ext; intro i j; exact zrow_entry i j
  rw [he] at h
  exact h
def xneighbors (i : Fin 180) : List (Fin 360) := (if i.val < 90 then (if i.val < 45 then (if i.val < 22 then (if i.val < 11 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then [0, 1, 32, 180, 188, 256] else [1, 2, 33, 181, 189, 257]) else (if i.val < 3 then [2, 3, 34, 182, 190, 258] else (if i.val < 4 then [3, 4, 35, 183, 191, 259] else [4, 5, 36, 184, 192, 260]))) else (if i.val < 8 then (if i.val < 6 then [5, 6, 37, 185, 193, 261] else (if i.val < 7 then [6, 7, 38, 186, 194, 262] else [7, 8, 39, 187, 195, 263])) else (if i.val < 9 then [8, 9, 40, 188, 196, 264] else (if i.val < 10 then [9, 10, 41, 189, 197, 265] else [10, 11, 42, 190, 198, 266])))) else (if i.val < 16 then (if i.val < 13 then (if i.val < 12 then [11, 12, 43, 191, 199, 267] else [12, 13, 44, 192, 200, 268]) else (if i.val < 14 then [13, 14, 45, 193, 201, 269] else (if i.val < 15 then [14, 15, 46, 194, 202, 240] else [15, 16, 47, 195, 203, 241]))) else (if i.val < 19 then (if i.val < 17 then [16, 17, 48, 196, 204, 242] else (if i.val < 18 then [17, 18, 49, 197, 205, 243] else [18, 19, 50, 198, 206, 244])) else (if i.val < 20 then [19, 20, 51, 199, 207, 245] else (if i.val < 21 then [20, 21, 52, 200, 208, 246] else [21, 22, 53, 201, 209, 247]))))) else (if i.val < 33 then (if i.val < 27 then (if i.val < 24 then (if i.val < 23 then [22, 23, 54, 180, 202, 248] else [23, 24, 55, 181, 203, 249]) else (if i.val < 25 then [24, 25, 56, 182, 204, 250] else (if i.val < 26 then [25, 26, 57, 183, 205, 251] else [26, 27, 58, 184, 206, 252]))) else (if i.val < 30 then (if i.val < 28 then [27, 28, 59, 185, 207, 253] else (if i.val < 29 then [28, 29, 30, 186, 208, 254] else [0, 29, 31, 187, 209, 255])) else (if i.val < 31 then [30, 31, 62, 210, 218, 286] else (if i.val < 32 then [31, 32, 63, 211, 219, 287] else [32, 33, 64, 212, 220, 288])))) else (if i.val < 39 then (if i.val < 36 then (if i.val < 34 then [33, 34, 65, 213, 221, 289] else (if i.val < 35 then [34, 35, 66, 214, 222, 290] else [35, 36, 67, 215, 223, 291])) else (if i.val < 37 then [36, 37, 68, 216, 224, 292] else (if i.val < 38 then [37, 38, 69, 217, 225, 293] else [38, 39, 70, 218, 226, 294]))) else (if i.val < 42 then (if i.val < 40 then [39, 40, 71, 219, 227, 295] else (if i.val < 41 then [40, 41, 72, 220, 228, 296] else [41, 42, 73, 221, 229, 297])) else (if i.val < 43 then [42, 43, 74, 222, 230, 298] else (if i.val < 44 then [43, 44, 75, 223, 231, 299] else [44, 45, 76, 224, 232, 270])))))) else (if i.val < 67 then (if i.val < 56 then (if i.val < 50 then (if i.val < 47 then (if i.val < 46 then [45, 46, 77, 225, 233, 271] else [46, 47, 78, 226, 234, 272]) else (if i.val < 48 then [47, 48, 79, 227, 235, 273] else (if i.val < 49 then [48, 49, 80, 228, 236, 274] else [49, 50, 81, 229, 237, 275]))) else (if i.val < 53 then (if i.val < 51 then [50, 51, 82, 230, 238, 276] else (if i.val < 52 then [51, 52, 83, 231, 239, 277] else [52, 53, 84, 210, 232, 278])) else (if i.val < 54 then [53, 54, 85, 211, 233, 279] else (if i.val < 55 then [54, 55, 86, 212, 234, 280] else [55, 56, 87, 213, 235, 281])))) else (if i.val < 61 then (if i.val < 58 then (if i.val < 57 then [56, 57, 88, 214, 236, 282] else [57, 58, 89, 215, 237, 283]) else (if i.val < 59 then [58, 59, 60, 216, 238, 284] else (if i.val < 60 then [30, 59, 61, 217, 239, 285] else [60, 61, 92, 240, 248, 316]))) else (if i.val < 64 then (if i.val < 62 then [61, 62, 93, 241, 249, 317] else (if i.val < 63 then [62, 63, 94, 242, 250, 318] else [63, 64, 95, 243, 251, 319])) else (if i.val < 65 then [64, 65, 96, 244, 252, 320] else (if i.val < 66 then [65, 66, 97, 245, 253, 321] else [66, 67, 98, 246, 254, 322]))))) else (if i.val < 78 then (if i.val < 72 then (if i.val < 69 then (if i.val < 68 then [67, 68, 99, 247, 255, 323] else [68, 69, 100, 248, 256, 324]) else (if i.val < 70 then [69, 70, 101, 249, 257, 325] else (if i.val < 71 then [70, 71, 102, 250, 258, 326] else [71, 72, 103, 251, 259, 327]))) else (if i.val < 75 then (if i.val < 73 then [72, 73, 104, 252, 260, 328] else (if i.val < 74 then [73, 74, 105, 253, 261, 329] else [74, 75, 106, 254, 262, 300])) else (if i.val < 76 then [75, 76, 107, 255, 263, 301] else (if i.val < 77 then [76, 77, 108, 256, 264, 302] else [77, 78, 109, 257, 265, 303])))) else (if i.val < 84 then (if i.val < 81 then (if i.val < 79 then [78, 79, 110, 258, 266, 304] else (if i.val < 80 then [79, 80, 111, 259, 267, 305] else [80, 81, 112, 260, 268, 306])) else (if i.val < 82 then [81, 82, 113, 261, 269, 307] else (if i.val < 83 then [82, 83, 114, 240, 262, 308] else [83, 84, 115, 241, 263, 309]))) else (if i.val < 87 then (if i.val < 85 then [84, 85, 116, 242, 264, 310] else (if i.val < 86 then [85, 86, 117, 243, 265, 311] else [86, 87, 118, 244, 266, 312])) else (if i.val < 88 then [87, 88, 119, 245, 267, 313] else (if i.val < 89 then [88, 89, 90, 246, 268, 314] else [60, 89, 91, 247, 269, 315]))))))) else (if i.val < 135 then (if i.val < 112 then (if i.val < 101 then (if i.val < 95 then (if i.val < 92 then (if i.val < 91 then [90, 91, 122, 270, 278, 346] else [91, 92, 123, 271, 279, 347]) else (if i.val < 93 then [92, 93, 124, 272, 280, 348] else (if i.val < 94 then [93, 94, 125, 273, 281, 349] else [94, 95, 126, 274, 282, 350]))) else (if i.val < 98 then (if i.val < 96 then [95, 96, 127, 275, 283, 351] else (if i.val < 97 then [96, 97, 128, 276, 284, 352] else [97, 98, 129, 277, 285, 353])) else (if i.val < 99 then [98, 99, 130, 278, 286, 354] else (if i.val < 100 then [99, 100, 131, 279, 287, 355] else [100, 101, 132, 280, 288, 356])))) else (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then [101, 102, 133, 281, 289, 357] else [102, 103, 134, 282, 290, 358]) else (if i.val < 104 then [103, 104, 135, 283, 291, 359] else (if i.val < 105 then [104, 105, 136, 284, 292, 330] else [105, 106, 137, 285, 293, 331]))) else (if i.val < 109 then (if i.val < 107 then [106, 107, 138, 286, 294, 332] else (if i.val < 108 then [107, 108, 139, 287, 295, 333] else [108, 109, 140, 288, 296, 334])) else (if i.val < 110 then [109, 110, 141, 289, 297, 335] else (if i.val < 111 then [110, 111, 142, 290, 298, 336] else [111, 112, 143, 291, 299, 337]))))) else (if i.val < 123 then (if i.val < 117 then (if i.val < 114 then (if i.val < 113 then [112, 113, 144, 270, 292, 338] else [113, 114, 145, 271, 293, 339]) else (if i.val < 115 then [114, 115, 146, 272, 294, 340] else (if i.val < 116 then [115, 116, 147, 273, 295, 341] else [116, 117, 148, 274, 296, 342]))) else (if i.val < 120 then (if i.val < 118 then [117, 118, 149, 275, 297, 343] else (if i.val < 119 then [118, 119, 120, 276, 298, 344] else [90, 119, 121, 277, 299, 345])) else (if i.val < 121 then [120, 121, 152, 196, 300, 308] else (if i.val < 122 then [121, 122, 153, 197, 301, 309] else [122, 123, 154, 198, 302, 310])))) else (if i.val < 129 then (if i.val < 126 then (if i.val < 124 then [123, 124, 155, 199, 303, 311] else (if i.val < 125 then [124, 125, 156, 200, 304, 312] else [125, 126, 157, 201, 305, 313])) else (if i.val < 127 then [126, 127, 158, 202, 306, 314] else (if i.val < 128 then [127, 128, 159, 203, 307, 315] else [128, 129, 160, 204, 308, 316]))) else (if i.val < 132 then (if i.val < 130 then [129, 130, 161, 205, 309, 317] else (if i.val < 131 then [130, 131, 162, 206, 310, 318] else [131, 132, 163, 207, 311, 319])) else (if i.val < 133 then [132, 133, 164, 208, 312, 320] else (if i.val < 134 then [133, 134, 165, 209, 313, 321] else [134, 135, 166, 180, 314, 322])))))) else (if i.val < 157 then (if i.val < 146 then (if i.val < 140 then (if i.val < 137 then (if i.val < 136 then [135, 136, 167, 181, 315, 323] else [136, 137, 168, 182, 316, 324]) else (if i.val < 138 then [137, 138, 169, 183, 317, 325] else (if i.val < 139 then [138, 139, 170, 184, 318, 326] else [139, 140, 171, 185, 319, 327]))) else (if i.val < 143 then (if i.val < 141 then [140, 141, 172, 186, 320, 328] else (if i.val < 142 then [141, 142, 173, 187, 321, 329] else [142, 143, 174, 188, 300, 322])) else (if i.val < 144 then [143, 144, 175, 189, 301, 323] else (if i.val < 145 then [144, 145, 176, 190, 302, 324] else [145, 146, 177, 191, 303, 325])))) else (if i.val < 151 then (if i.val < 148 then (if i.val < 147 then [146, 147, 178, 192, 304, 326] else [147, 148, 179, 193, 305, 327]) else (if i.val < 149 then [148, 149, 150, 194, 306, 328] else (if i.val < 150 then [120, 149, 151, 195, 307, 329] else [2, 150, 151, 226, 330, 338]))) else (if i.val < 154 then (if i.val < 152 then [3, 151, 152, 227, 331, 339] else (if i.val < 153 then [4, 152, 153, 228, 332, 340] else [5, 153, 154, 229, 333, 341])) else (if i.val < 155 then [6, 154, 155, 230, 334, 342] else (if i.val < 156 then [7, 155, 156, 231, 335, 343] else [8, 156, 157, 232, 336, 344]))))) else (if i.val < 168 then (if i.val < 162 then (if i.val < 159 then (if i.val < 158 then [9, 157, 158, 233, 337, 345] else [10, 158, 159, 234, 338, 346]) else (if i.val < 160 then [11, 159, 160, 235, 339, 347] else (if i.val < 161 then [12, 160, 161, 236, 340, 348] else [13, 161, 162, 237, 341, 349]))) else (if i.val < 165 then (if i.val < 163 then [14, 162, 163, 238, 342, 350] else (if i.val < 164 then [15, 163, 164, 239, 343, 351] else [16, 164, 165, 210, 344, 352])) else (if i.val < 166 then [17, 165, 166, 211, 345, 353] else (if i.val < 167 then [18, 166, 167, 212, 346, 354] else [19, 167, 168, 213, 347, 355])))) else (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then [20, 168, 169, 214, 348, 356] else (if i.val < 170 then [21, 169, 170, 215, 349, 357] else [22, 170, 171, 216, 350, 358])) else (if i.val < 172 then [23, 171, 172, 217, 351, 359] else (if i.val < 173 then [24, 172, 173, 218, 330, 352] else [25, 173, 174, 219, 331, 353]))) else (if i.val < 177 then (if i.val < 175 then [26, 174, 175, 220, 332, 354] else (if i.val < 176 then [27, 175, 176, 221, 333, 355] else [28, 176, 177, 222, 334, 356])) else (if i.val < 178 then [29, 177, 178, 223, 335, 357] else (if i.val < 179 then [0, 178, 179, 224, 336, 358] else [1, 150, 179, 225, 337, 359]))))))))
def xpos (j : Fin 360) : List (Fin 180) := (if j.val < 180 then (if j.val < 90 then (if j.val < 45 then (if j.val < 22 then (if j.val < 11 then (if j.val < 5 then (if j.val < 2 then (if j.val < 1 then [0, 29, 178] else [0, 1, 179]) else (if j.val < 3 then [1, 2, 150] else (if j.val < 4 then [2, 3, 151] else [3, 4, 152]))) else (if j.val < 8 then (if j.val < 6 then [4, 5, 153] else (if j.val < 7 then [5, 6, 154] else [6, 7, 155])) else (if j.val < 9 then [7, 8, 156] else (if j.val < 10 then [8, 9, 157] else [9, 10, 158])))) else (if j.val < 16 then (if j.val < 13 then (if j.val < 12 then [10, 11, 159] else [11, 12, 160]) else (if j.val < 14 then [12, 13, 161] else (if j.val < 15 then [13, 14, 162] else [14, 15, 163]))) else (if j.val < 19 then (if j.val < 17 then [15, 16, 164] else (if j.val < 18 then [16, 17, 165] else [17, 18, 166])) else (if j.val < 20 then [18, 19, 167] else (if j.val < 21 then [19, 20, 168] else [20, 21, 169]))))) else (if j.val < 33 then (if j.val < 27 then (if j.val < 24 then (if j.val < 23 then [21, 22, 170] else [22, 23, 171]) else (if j.val < 25 then [23, 24, 172] else (if j.val < 26 then [24, 25, 173] else [25, 26, 174]))) else (if j.val < 30 then (if j.val < 28 then [26, 27, 175] else (if j.val < 29 then [27, 28, 176] else [28, 29, 177])) else (if j.val < 31 then [28, 30, 59] else (if j.val < 32 then [29, 30, 31] else [0, 31, 32])))) else (if j.val < 39 then (if j.val < 36 then (if j.val < 34 then [1, 32, 33] else (if j.val < 35 then [2, 33, 34] else [3, 34, 35])) else (if j.val < 37 then [4, 35, 36] else (if j.val < 38 then [5, 36, 37] else [6, 37, 38]))) else (if j.val < 42 then (if j.val < 40 then [7, 38, 39] else (if j.val < 41 then [8, 39, 40] else [9, 40, 41])) else (if j.val < 43 then [10, 41, 42] else (if j.val < 44 then [11, 42, 43] else [12, 43, 44])))))) else (if j.val < 67 then (if j.val < 56 then (if j.val < 50 then (if j.val < 47 then (if j.val < 46 then [13, 44, 45] else [14, 45, 46]) else (if j.val < 48 then [15, 46, 47] else (if j.val < 49 then [16, 47, 48] else [17, 48, 49]))) else (if j.val < 53 then (if j.val < 51 then [18, 49, 50] else (if j.val < 52 then [19, 50, 51] else [20, 51, 52])) else (if j.val < 54 then [21, 52, 53] else (if j.val < 55 then [22, 53, 54] else [23, 54, 55])))) else (if j.val < 61 then (if j.val < 58 then (if j.val < 57 then [24, 55, 56] else [25, 56, 57]) else (if j.val < 59 then [26, 57, 58] else (if j.val < 60 then [27, 58, 59] else [58, 60, 89]))) else (if j.val < 64 then (if j.val < 62 then [59, 60, 61] else (if j.val < 63 then [30, 61, 62] else [31, 62, 63])) else (if j.val < 65 then [32, 63, 64] else (if j.val < 66 then [33, 64, 65] else [34, 65, 66]))))) else (if j.val < 78 then (if j.val < 72 then (if j.val < 69 then (if j.val < 68 then [35, 66, 67] else [36, 67, 68]) else (if j.val < 70 then [37, 68, 69] else (if j.val < 71 then [38, 69, 70] else [39, 70, 71]))) else (if j.val < 75 then (if j.val < 73 then [40, 71, 72] else (if j.val < 74 then [41, 72, 73] else [42, 73, 74])) else (if j.val < 76 then [43, 74, 75] else (if j.val < 77 then [44, 75, 76] else [45, 76, 77])))) else (if j.val < 84 then (if j.val < 81 then (if j.val < 79 then [46, 77, 78] else (if j.val < 80 then [47, 78, 79] else [48, 79, 80])) else (if j.val < 82 then [49, 80, 81] else (if j.val < 83 then [50, 81, 82] else [51, 82, 83]))) else (if j.val < 87 then (if j.val < 85 then [52, 83, 84] else (if j.val < 86 then [53, 84, 85] else [54, 85, 86])) else (if j.val < 88 then [55, 86, 87] else (if j.val < 89 then [56, 87, 88] else [57, 88, 89]))))))) else (if j.val < 135 then (if j.val < 112 then (if j.val < 101 then (if j.val < 95 then (if j.val < 92 then (if j.val < 91 then [88, 90, 119] else [89, 90, 91]) else (if j.val < 93 then [60, 91, 92] else (if j.val < 94 then [61, 92, 93] else [62, 93, 94]))) else (if j.val < 98 then (if j.val < 96 then [63, 94, 95] else (if j.val < 97 then [64, 95, 96] else [65, 96, 97])) else (if j.val < 99 then [66, 97, 98] else (if j.val < 100 then [67, 98, 99] else [68, 99, 100])))) else (if j.val < 106 then (if j.val < 103 then (if j.val < 102 then [69, 100, 101] else [70, 101, 102]) else (if j.val < 104 then [71, 102, 103] else (if j.val < 105 then [72, 103, 104] else [73, 104, 105]))) else (if j.val < 109 then (if j.val < 107 then [74, 105, 106] else (if j.val < 108 then [75, 106, 107] else [76, 107, 108])) else (if j.val < 110 then [77, 108, 109] else (if j.val < 111 then [78, 109, 110] else [79, 110, 111]))))) else (if j.val < 123 then (if j.val < 117 then (if j.val < 114 then (if j.val < 113 then [80, 111, 112] else [81, 112, 113]) else (if j.val < 115 then [82, 113, 114] else (if j.val < 116 then [83, 114, 115] else [84, 115, 116]))) else (if j.val < 120 then (if j.val < 118 then [85, 116, 117] else (if j.val < 119 then [86, 117, 118] else [87, 118, 119])) else (if j.val < 121 then [118, 120, 149] else (if j.val < 122 then [119, 120, 121] else [90, 121, 122])))) else (if j.val < 129 then (if j.val < 126 then (if j.val < 124 then [91, 122, 123] else (if j.val < 125 then [92, 123, 124] else [93, 124, 125])) else (if j.val < 127 then [94, 125, 126] else (if j.val < 128 then [95, 126, 127] else [96, 127, 128]))) else (if j.val < 132 then (if j.val < 130 then [97, 128, 129] else (if j.val < 131 then [98, 129, 130] else [99, 130, 131])) else (if j.val < 133 then [100, 131, 132] else (if j.val < 134 then [101, 132, 133] else [102, 133, 134])))))) else (if j.val < 157 then (if j.val < 146 then (if j.val < 140 then (if j.val < 137 then (if j.val < 136 then [103, 134, 135] else [104, 135, 136]) else (if j.val < 138 then [105, 136, 137] else (if j.val < 139 then [106, 137, 138] else [107, 138, 139]))) else (if j.val < 143 then (if j.val < 141 then [108, 139, 140] else (if j.val < 142 then [109, 140, 141] else [110, 141, 142])) else (if j.val < 144 then [111, 142, 143] else (if j.val < 145 then [112, 143, 144] else [113, 144, 145])))) else (if j.val < 151 then (if j.val < 148 then (if j.val < 147 then [114, 145, 146] else [115, 146, 147]) else (if j.val < 149 then [116, 147, 148] else (if j.val < 150 then [117, 148, 149] else [148, 150, 179]))) else (if j.val < 154 then (if j.val < 152 then [149, 150, 151] else (if j.val < 153 then [120, 151, 152] else [121, 152, 153])) else (if j.val < 155 then [122, 153, 154] else (if j.val < 156 then [123, 154, 155] else [124, 155, 156]))))) else (if j.val < 168 then (if j.val < 162 then (if j.val < 159 then (if j.val < 158 then [125, 156, 157] else [126, 157, 158]) else (if j.val < 160 then [127, 158, 159] else (if j.val < 161 then [128, 159, 160] else [129, 160, 161]))) else (if j.val < 165 then (if j.val < 163 then [130, 161, 162] else (if j.val < 164 then [131, 162, 163] else [132, 163, 164])) else (if j.val < 166 then [133, 164, 165] else (if j.val < 167 then [134, 165, 166] else [135, 166, 167])))) else (if j.val < 174 then (if j.val < 171 then (if j.val < 169 then [136, 167, 168] else (if j.val < 170 then [137, 168, 169] else [138, 169, 170])) else (if j.val < 172 then [139, 170, 171] else (if j.val < 173 then [140, 171, 172] else [141, 172, 173]))) else (if j.val < 177 then (if j.val < 175 then [142, 173, 174] else (if j.val < 176 then [143, 174, 175] else [144, 175, 176])) else (if j.val < 178 then [145, 176, 177] else (if j.val < 179 then [146, 177, 178] else [147, 178, 179])))))))) else (if j.val < 270 then (if j.val < 225 then (if j.val < 202 then (if j.val < 191 then (if j.val < 185 then (if j.val < 182 then (if j.val < 181 then [0, 22, 134] else [1, 23, 135]) else (if j.val < 183 then [2, 24, 136] else (if j.val < 184 then [3, 25, 137] else [4, 26, 138]))) else (if j.val < 188 then (if j.val < 186 then [5, 27, 139] else (if j.val < 187 then [6, 28, 140] else [7, 29, 141])) else (if j.val < 189 then [0, 8, 142] else (if j.val < 190 then [1, 9, 143] else [2, 10, 144])))) else (if j.val < 196 then (if j.val < 193 then (if j.val < 192 then [3, 11, 145] else [4, 12, 146]) else (if j.val < 194 then [5, 13, 147] else (if j.val < 195 then [6, 14, 148] else [7, 15, 149]))) else (if j.val < 199 then (if j.val < 197 then [8, 16, 120] else (if j.val < 198 then [9, 17, 121] else [10, 18, 122])) else (if j.val < 200 then [11, 19, 123] else (if j.val < 201 then [12, 20, 124] else [13, 21, 125]))))) else (if j.val < 213 then (if j.val < 207 then (if j.val < 204 then (if j.val < 203 then [14, 22, 126] else [15, 23, 127]) else (if j.val < 205 then [16, 24, 128] else (if j.val < 206 then [17, 25, 129] else [18, 26, 130]))) else (if j.val < 210 then (if j.val < 208 then [19, 27, 131] else (if j.val < 209 then [20, 28, 132] else [21, 29, 133])) else (if j.val < 211 then [30, 52, 164] else (if j.val < 212 then [31, 53, 165] else [32, 54, 166])))) else (if j.val < 219 then (if j.val < 216 then (if j.val < 214 then [33, 55, 167] else (if j.val < 215 then [34, 56, 168] else [35, 57, 169])) else (if j.val < 217 then [36, 58, 170] else (if j.val < 218 then [37, 59, 171] else [30, 38, 172]))) else (if j.val < 222 then (if j.val < 220 then [31, 39, 173] else (if j.val < 221 then [32, 40, 174] else [33, 41, 175])) else (if j.val < 223 then [34, 42, 176] else (if j.val < 224 then [35, 43, 177] else [36, 44, 178])))))) else (if j.val < 247 then (if j.val < 236 then (if j.val < 230 then (if j.val < 227 then (if j.val < 226 then [37, 45, 179] else [38, 46, 150]) else (if j.val < 228 then [39, 47, 151] else (if j.val < 229 then [40, 48, 152] else [41, 49, 153]))) else (if j.val < 233 then (if j.val < 231 then [42, 50, 154] else (if j.val < 232 then [43, 51, 155] else [44, 52, 156])) else (if j.val < 234 then [45, 53, 157] else (if j.val < 235 then [46, 54, 158] else [47, 55, 159])))) else (if j.val < 241 then (if j.val < 238 then (if j.val < 237 then [48, 56, 160] else [49, 57, 161]) else (if j.val < 239 then [50, 58, 162] else (if j.val < 240 then [51, 59, 163] else [14, 60, 82]))) else (if j.val < 244 then (if j.val < 242 then [15, 61, 83] else (if j.val < 243 then [16, 62, 84] else [17, 63, 85])) else (if j.val < 245 then [18, 64, 86] else (if j.val < 246 then [19, 65, 87] else [20, 66, 88]))))) else (if j.val < 258 then (if j.val < 252 then (if j.val < 249 then (if j.val < 248 then [21, 67, 89] else [22, 60, 68]) else (if j.val < 250 then [23, 61, 69] else (if j.val < 251 then [24, 62, 70] else [25, 63, 71]))) else (if j.val < 255 then (if j.val < 253 then [26, 64, 72] else (if j.val < 254 then [27, 65, 73] else [28, 66, 74])) else (if j.val < 256 then [29, 67, 75] else (if j.val < 257 then [0, 68, 76] else [1, 69, 77])))) else (if j.val < 264 then (if j.val < 261 then (if j.val < 259 then [2, 70, 78] else (if j.val < 260 then [3, 71, 79] else [4, 72, 80])) else (if j.val < 262 then [5, 73, 81] else (if j.val < 263 then [6, 74, 82] else [7, 75, 83]))) else (if j.val < 267 then (if j.val < 265 then [8, 76, 84] else (if j.val < 266 then [9, 77, 85] else [10, 78, 86])) else (if j.val < 268 then [11, 79, 87] else (if j.val < 269 then [12, 80, 88] else [13, 81, 89]))))))) else (if j.val < 315 then (if j.val < 292 then (if j.val < 281 then (if j.val < 275 then (if j.val < 272 then (if j.val < 271 then [44, 90, 112] else [45, 91, 113]) else (if j.val < 273 then [46, 92, 114] else (if j.val < 274 then [47, 93, 115] else [48, 94, 116]))) else (if j.val < 278 then (if j.val < 276 then [49, 95, 117] else (if j.val < 277 then [50, 96, 118] else [51, 97, 119])) else (if j.val < 279 then [52, 90, 98] else (if j.val < 280 then [53, 91, 99] else [54, 92, 100])))) else (if j.val < 286 then (if j.val < 283 then (if j.val < 282 then [55, 93, 101] else [56, 94, 102]) else (if j.val < 284 then [57, 95, 103] else (if j.val < 285 then [58, 96, 104] else [59, 97, 105]))) else (if j.val < 289 then (if j.val < 287 then [30, 98, 106] else (if j.val < 288 then [31, 99, 107] else [32, 100, 108])) else (if j.val < 290 then [33, 101, 109] else (if j.val < 291 then [34, 102, 110] else [35, 103, 111]))))) else (if j.val < 303 then (if j.val < 297 then (if j.val < 294 then (if j.val < 293 then [36, 104, 112] else [37, 105, 113]) else (if j.val < 295 then [38, 106, 114] else (if j.val < 296 then [39, 107, 115] else [40, 108, 116]))) else (if j.val < 300 then (if j.val < 298 then [41, 109, 117] else (if j.val < 299 then [42, 110, 118] else [43, 111, 119])) else (if j.val < 301 then [74, 120, 142] else (if j.val < 302 then [75, 121, 143] else [76, 122, 144])))) else (if j.val < 309 then (if j.val < 306 then (if j.val < 304 then [77, 123, 145] else (if j.val < 305 then [78, 124, 146] else [79, 125, 147])) else (if j.val < 307 then [80, 126, 148] else (if j.val < 308 then [81, 127, 149] else [82, 120, 128]))) else (if j.val < 312 then (if j.val < 310 then [83, 121, 129] else (if j.val < 311 then [84, 122, 130] else [85, 123, 131])) else (if j.val < 313 then [86, 124, 132] else (if j.val < 314 then [87, 125, 133] else [88, 126, 134])))))) else (if j.val < 337 then (if j.val < 326 then (if j.val < 320 then (if j.val < 317 then (if j.val < 316 then [89, 127, 135] else [60, 128, 136]) else (if j.val < 318 then [61, 129, 137] else (if j.val < 319 then [62, 130, 138] else [63, 131, 139]))) else (if j.val < 323 then (if j.val < 321 then [64, 132, 140] else (if j.val < 322 then [65, 133, 141] else [66, 134, 142])) else (if j.val < 324 then [67, 135, 143] else (if j.val < 325 then [68, 136, 144] else [69, 137, 145])))) else (if j.val < 331 then (if j.val < 328 then (if j.val < 327 then [70, 138, 146] else [71, 139, 147]) else (if j.val < 329 then [72, 140, 148] else (if j.val < 330 then [73, 141, 149] else [104, 150, 172]))) else (if j.val < 334 then (if j.val < 332 then [105, 151, 173] else (if j.val < 333 then [106, 152, 174] else [107, 153, 175])) else (if j.val < 335 then [108, 154, 176] else (if j.val < 336 then [109, 155, 177] else [110, 156, 178]))))) else (if j.val < 348 then (if j.val < 342 then (if j.val < 339 then (if j.val < 338 then [111, 157, 179] else [112, 150, 158]) else (if j.val < 340 then [113, 151, 159] else (if j.val < 341 then [114, 152, 160] else [115, 153, 161]))) else (if j.val < 345 then (if j.val < 343 then [116, 154, 162] else (if j.val < 344 then [117, 155, 163] else [118, 156, 164])) else (if j.val < 346 then [119, 157, 165] else (if j.val < 347 then [90, 158, 166] else [91, 159, 167])))) else (if j.val < 354 then (if j.val < 351 then (if j.val < 349 then [92, 160, 168] else (if j.val < 350 then [93, 161, 169] else [94, 162, 170])) else (if j.val < 352 then [95, 163, 171] else (if j.val < 353 then [96, 164, 172] else [97, 165, 173]))) else (if j.val < 357 then (if j.val < 355 then [98, 166, 174] else (if j.val < 356 then [99, 167, 175] else [100, 168, 176])) else (if j.val < 358 then [101, 169, 177] else (if j.val < 359 then [102, 170, 178] else [103, 171, 179])))))))))
lemma xpos_nodup : ∀ j, (xpos j).Nodup := by decide +kernel
lemma xpos_signature : ∀ j, signature unit (xpos j) = xmask j := by decide +kernel
lemma xpos_length : ∀ j, (xpos j).length = 3 := by decide +kernel
lemma entry_nonzero_iff {r : ℕ} (v : BitVec r) (i : Fin r) :
    entry v i ≠ 0 ↔ v.getLsbD i.val = true := by
  unfold entry
  cases v.getLsbD i.val <;> decide
lemma xpos_spec (j : Fin 360) : (xpos j).Nodup ∧ (xpos j).toFinset = Finset.univ.filter (fun i => (xmask j).getLsbD i.val) := by
  refine ⟨xpos_nodup j, ?_⟩
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
  rw [← entry_nonzero_iff]
  have he : entry (xmask j) i = if i ∈ xpos j then 1 else 0 := by
    rw [← xpos_signature,signature_entry unit (xpos j) (xpos_nodup j) i]
    simp [unit_entry]
  rw [he]
  by_cases hi : i ∈ xpos j <;> simp [hi]
lemma ones_card {r : ℕ} (v : BitVec r) :
    ones v = (Finset.univ.filter fun i : Fin r => v.getLsbD i.val).card := by
  rw [ones_eq,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases v.getLsbD i.val <;> rfl
lemma xthree (j : Fin 360) : ones (xmask j) = 3 := by
  rw [ones_card,← (xpos_spec j).2,List.toFinset_card_of_nodup (xpos_nodup j),xpos_length]
def xupdate (j : Fin 360) (sy : BitVec 180) (pc : ℕ) : ℕ :=
  pc + 3 - 2 * ((xpos j).map fun i => (sy.getLsbD i.val).toNat).sum
lemma xupdate_spec (j : Fin 360) (sy : BitVec 180) : xupdate j sy (ones sy) = ones (xmask j ^^^ sy) :=
  BBNew360Count.update_eq (xmask j) sy (xpos j) (xpos_spec j).1 (xpos_spec j).2 (xthree j)
lemma xones (j : Fin 360) : ones (xmask j) ≤ 3 := (xthree j).le
lemma xpos_cover : ∀ j, (xpos j).all (fun i => decide (j ∈ xneighbors i)) = true := by decide +kernel
lemma xcover (i : Fin 180) (j : Fin 360) (h : entry (xmask j) i = 1) : j ∈ xneighbors i := by
  have hb : (xmask j).getLsbD i.val = true := by
    cases he : (xmask j).getLsbD i.val with
    | true => rfl
    | false =>
      have hz : entry (xmask j) i = 0 := by dsimp only [entry]; rw [he]; rfl
      rw [hz] at h
      exact False.elim (zero_ne_one h)
  have hi : i ∈ (xpos j).toFinset := by rw [(xpos_spec j).2]; simpa using hb
  have hh := List.all_eq_true.mp (xpos_cover j) i (List.mem_toFinset.mp hi)
  exact of_decide_eq_true hh
lemma weight_equiv {a b : Type} [Fintype a] [Fintype b]
    (e : a ≃ b) (v : b → ZMod 2) : weight (v ∘ e) = weight v := by
  classical
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact e.sum_comp (fun j => if v j ≠ 0 then (1 : ℕ) else 0)

lemma unindex_kernel (H : Matrix (Grp 6 30) (Qubit 6 30) (ZMod 2))
    (v : Fin 360 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 6 30) (Qubit 6 30) (ZMod 2))
    (v : Qubit 6 30 → ZMod 2) (hv : H *ᵥ v = 0) :
    H.submatrix er eqb *ᵥ (v ∘ eqb) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ eqb) ∘ eqb.symm = v := by funext i; simp
  rw [he,hv]
  rfl

end BBNew360KernelData

set_option maxHeartbeats 0
namespace BBNew360High

def seek {r : ℕ} (s : BitVec r) : ℕ → ℕ
  | 0 => 0
  | fuel+1 => if s.getLsbD fuel then fuel else seek s fuel

lemma seek_spec {r : ℕ} (s : BitVec r) (fuel : ℕ)
    (hex : ∃ i, i < fuel ∧ s.getLsbD i = true) :
    seek s fuel < fuel ∧ s.getLsbD (seek s fuel) = true := by
  induction fuel with
  | zero => obtain ⟨i,hi,_⟩ := hex; omega
  | succ f ih =>
    rw [seek]
    cases hb : s.getLsbD f with
    | true => simp only [hb,ite_true]; exact ⟨by omega,True.intro⟩
    | false =>
      simp only [hb,Bool.false_eq_true,ite_false]
      have hh : ∃ i, i < f ∧ s.getLsbD i = true := by
        obtain ⟨i,hi,hbit⟩ := hex
        refine ⟨i,?_,hbit⟩
        by_contra hn
        have he : i = f := by omega
        subst i
        rw [hb] at hbit
        contradiction
      have h := ih hh
      exact ⟨by omega,h.2⟩

lemma seek_lt {r : ℕ} (s : BitVec r) (hs : s ≠ 0) :
    seek s r < r ∧ s.getLsbD (seek s r) = true := by
  apply seek_spec
  by_contra h
  apply hs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : s.getLsbD i ≠ true := by intro he; exact h ⟨i,hi,he⟩
  simpa using hn

def pick {r : ℕ} [NeZero r] (s : BitVec r) : Fin r :=
  if h : s = 0 then 0 else ⟨seek s r,(seek_lt s h).1⟩

lemma pick_spec {r : ℕ} [NeZero r] (s : BitVec r) (hs : s ≠ 0) :
    s.getLsbD (pick s).val = true := by
  simpa only [pick,dif_neg hs] using (seek_lt s hs).2
end BBNew360High

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BBNew360Cert
namespace BBNew360Grow

open BBNew360Search

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) : ℕ → List (Fin n) → BitVec r → Bool
  | fuel, used, sy =>
    if 3 * fuel < ones sy then true
    else if sy = 0 then decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => (nbr (BBNew360High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr fuel (j :: used) (C j ^^^ sy)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) :
    check C K nbr fuel used sy =
      if 3 * fuel < ones sy then true
      else if sy = 0 then decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => (nbr (BBNew360High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr f (j :: used) (C j ^^^ sy) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (BBNew360High.pick sy), j ∉ used → check C K nbr fuel (j::used) (C j ^^^ sy) = true) :
    check C K nbr (fuel+1) used sy = true := by
  rw [check_eq]
  by_cases hp : 3*(fuel+1) < ones sy
  · simp only [if_pos hp]
  · rw [if_neg hp,if_neg hs]
    apply List.all_eq_true.mpr
    intro j hj
    by_cases hu : j ∈ used
    · simp [hu]
    · simpa only [if_neg hu] using hc j hj hu
end BBNew360Grow

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BBNew360Cert BBNew360Search
namespace BBNew360Grow

lemma completion_bound {r n : ℕ} (C : Fin n → BitVec r) (hC : ∀ j, ones (C j) ≤ 3)
    (T : Finset (Fin n)) (hT : ∀ i, ∑ j ∈ T, entry (C j) i = 0)
    (fuel : ℕ) (used : List (Fin n)) (hn : used.Nodup) (hu : used.toFinset ⊆ T)
    (hb : T.card ≤ used.length + fuel) : ones (signature C used) ≤ 3 * fuel := by
  classical
  let R := T \ used.toFinset
  let l := (List.finRange n).filter (fun j => j ∈ R)
  have hln : l.Nodup := (List.nodup_finRange n).filter _
  have hle : l.toFinset = R := by ext j; simp [l]
  have hlen : l.length = R.card := by rw [← hle,List.toFinset_card_of_nodup hln]
  have he : signature C l = signature C used := by
    apply entry_injective
    ext i
    rw [signature_entry C l hln i,hle,signature_entry C used hn i]
    dsimp only [R]
    have hs := Finset.sum_sdiff (f := fun j => entry (C j) i) hu
    rw [hT] at hs
    exact (eq_neg_of_add_eq_zero_left hs).trans (ZMod.neg_eq_self_mod_two _)
  have h := ones_sig_le C hC l
  rw [he,hlen] at h
  have hcard : R.card = T.card - used.length := by
    rw [Finset.card_sdiff_of_subset hu,List.toFinset_card_of_nodup hn]
  have hlecard : used.length ≤ T.card := by
    rw [← List.toFinset_card_of_nodup hn]
    exact Finset.card_le_card hu
  rw [hcard] at h
  omega

lemma extract {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (hC : ∀ j, ones (C j) ≤ 3)
    (hcover : ∀ i j, entry (C j) i = 1 → j ∈ nbr i)
    (T : Finset (Fin n)) (hT : ∀ i, ∑ j ∈ T, entry (C j) i = 0)
    (fuel : ℕ) (used : List (Fin n)) (hn : used.Nodup) (hu : used.toFinset ⊆ T)
    (hb : T.card ≤ used.length + fuel)
    (hc : check C K nbr fuel used (signature C used) = true) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ used.toFinset ⊆ S ∧
      (∀ i, ∑ j ∈ S, entry (C j) i = 0) ∧ (∀ i, ∑ j ∈ S, entry (K j) i = 0) := by
  classical
  induction fuel using Nat.strong_induction_on generalizing used with
  | h fuel ih =>
    have hbound := completion_bound C hC T hT fuel used hn hu hb
    rw [check_eq,if_neg (by omega : ¬ 3*fuel < ones (signature C used))] at hc
    by_cases hz : signature C used = 0
    · have hh : signature K used = 0 := by simpa [hz] using hc
      refine ⟨used.toFinset,hu,Finset.Subset.refl _,?_,?_⟩
      · intro i
        rw [← signature_entry C used hn i,hz]
        simp [entry]
      · intro i
        rw [← signature_entry K used hn i,hh]
        simp [entry]
    · cases fuel with
      | zero =>
        have he : used.toFinset = T := Finset.eq_of_subset_of_card_le hu (by
          rw [List.toFinset_card_of_nodup hn]; simpa using hb)
        apply False.elim
        apply hz
        apply entry_injective
        ext i
        rw [signature_entry C used hn i,he,hT]
        simp [entry]
      | succ f =>
        let i := BBNew360High.pick (signature C used)
        have hp : entry (signature C used) i = 1 := by
          simp [entry,i,BBNew360High.pick_spec _ hz]
        have hex : ∃ j ∈ T, j ∉ used ∧ entry (C j) i = 1 := by
          by_contra hnot
          have he : ∑ j ∈ used.toFinset, entry (C j) i = ∑ j ∈ T, entry (C j) i := by
            apply Finset.sum_subset hu
            intro j hj hjn
            by_contra hne
            exact hnot ⟨j,hj,by simpa using hjn,binary_eq_one hne⟩
          rw [← signature_entry C used hn i,hT,hp] at he
          exact one_ne_zero he
        obtain ⟨j,hj,hju,hji⟩ := hex
        have hjnbr := hcover i j hji
        have hall : (nbr i).all (fun j => if j ∈ used then true else
            check C K nbr f (j :: used) (C j ^^^ signature C used)) = true := by
          simpa only [hz,if_false] using hc
        have hchild := List.all_eq_true.mp hall j hjnbr
        rw [if_neg hju] at hchild
        have hsub : (j :: used).toFinset ⊆ T := by simpa using Finset.insert_subset hj hu
        obtain ⟨S,hST,hUS,hSC,hSK⟩ := ih f (by omega) (j::used)
          (List.nodup_cons.mpr ⟨hju,hn⟩) hsub (by simp only [List.length_cons]; omega)
          (by simpa only [signature,List.foldr_cons] using hchild)
        refine ⟨S,hST,?_,hSC,hSK⟩
        · exact (Finset.subset_insert j used.toFinset).trans (by simpa using hUS)
end BBNew360Grow

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BBNew360Cert BBNew360Search BBNew360KernelData
namespace BBNew360Chunk

lemma pair_chunk (anchor j : Fin 360) (hj : j ≠ anchor)
    (hc : BBNew360Grow.check xmask xrem xneighbors 8 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Qubit 6 30 → ZMod 2) (ha : v (eqb anchor) ≠ 0) (hvj : v (eqb j) ≠ 0)
    (hw : weight v ≤ 10) (hv : HX polyA polyB *ᵥ v = 0) :
    ∃ u : Qubit 6 30 → ZMod 2,
      HX polyA polyB *ᵥ u = 0 ∧ u ∈ rowSpace (HZ polyA polyB) ∧
      u (eqb anchor) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := by
  classical
  let w := v ∘ eqb
  let T := Finset.univ.filter fun j => w j ≠ 0
  have hwi : xH *ᵥ w = 0 := by rw [← xtable]; exact index_kernel _ v hv
  have hT : ∀ i, ∑ j ∈ T, entry (xmask j) i = 0 := by
    intro i
    change ∑ j ∈ (Finset.univ.filter fun j => w j ≠ 0), xH i j = 0
    rw [← support_mul xH w i,hwi]
    rfl
  have hn : [j,anchor].Nodup := by simpa using hj
  have hu : [j,anchor].toFinset ⊆ T := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl <;> simpa [T,w] using (by assumption : v _ ≠ 0)
  have hc' : BBNew360Grow.check xmask xrem xneighbors 8 [j,anchor]
      (signature xmask [j,anchor]) = true := by simpa [signature] using hc
  have hweight : T.card ≤ 10 := by
    change weight (v ∘ eqb) ≤ 10
    rwa [weight_equiv]
  obtain ⟨S,hST,hAS,hSC,hSK⟩ := BBNew360Grow.extract xmask xrem xneighbors xones xcover T hT
    8 [j,anchor] hn hu (by simpa using hweight) hc'
  let z : Fin 360 → ZMod 2 := fun q => if q ∈ S then 1 else 0
  have hzS : (Finset.univ.filter fun q => z q ≠ 0) = S := by ext q; simp [z]
  have hzX : xH *ᵥ z = 0 := by
    ext i
    rw [support_mul,hzS]
    exact hSC i
  have hzK : xK *ᵥ z = 0 := by
    ext i
    rw [support_mul,hzS]
    exact hSK i
  have hdec : zH.transpose * xD + (1 : Matrix (Fin 360) (Fin 360) (ZMod 2)) * xK = 1 := by
    simpa only [Matrix.one_mul] using xdecomp
  have hmem := kernel_mem_row zH xD xK 1 hdec z hzK
  let u := z ∘ eqb.symm
  have hue : u ∘ eqb = z := by ext q; simp [u]
  have hux : HX polyA polyB *ᵥ u = 0 := by
    apply unindex_kernel
    rwa [xtable]
  have humem : u ∈ rowSpace (HZ polyA polyB) := by
    apply (rowspace_reindex (HZ polyA polyB) er eqb u).mp
    rwa [ztable,hue]
  have haS : anchor ∈ S := hAS (by simp)
  refine ⟨u,hux,humem,?_,?_⟩
  · simp [u,z,haS]
  · intro q hq
    have hqS : eqb.symm q ∈ S := by simpa [u,z] using hq
    have hqT := hST hqS
    simpa [T,w] using hqT
end BBNew360Chunk

set_option maxHeartbeats 0
open BBNew360Cert BBNew360Search
namespace BBNew360FastGrow

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ) :
    ℕ → List (Fin n) → BitVec r → ℕ → Bool
  | fuel, used, sy, pc =>
    if sy = 0 then decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => if 3*(fuel+1) < pc then true else (nbr (BBNew360High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr upd fuel (j :: used) (C j ^^^ sy) (upd j sy pc)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) (pc : ℕ) :
    check C K nbr upd fuel used sy pc =
      if sy = 0 then decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => if 3*(f+1) < pc then true else (nbr (BBNew360High.pick sy)).all fun j => if j ∈ used then true else
            check C K nbr upd f (j :: used) (C j ^^^ sy) (upd j sy pc) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) (pc : ℕ) (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (BBNew360High.pick sy), j ∉ used →
      check C K nbr upd fuel (j::used) (C j ^^^ sy) (upd j sy pc) = true) :
    check C K nbr upd (fuel+1) used sy pc = true := by
  rw [check_eq,if_neg hs]
  change (if 3*(fuel+1) < pc then true else (nbr (BBNew360High.pick sy)).all fun j =>
    if j ∈ used then true else check C K nbr upd fuel (j::used) (C j ^^^ sy) (upd j sy pc)) = true
  by_cases hp : 3*(fuel+1) < pc
  · simp only [if_pos hp]
  · rw [if_neg hp]
    apply List.all_eq_true.mpr
    intro j hj
    by_cases hu : j ∈ used
    · simp [hu]
    · simpa only [if_neg hu] using hc j hj hu

lemma sound {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (hupd : ∀ j sy, upd j sy (ones sy) = ones (C j ^^^ sy))
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (hc : check C K nbr upd fuel used sy (ones sy) = true) :
    BBNew360Grow.check C K nbr fuel used sy = true := by
  induction fuel generalizing used sy with
  | zero =>
    rw [BBNew360Grow.check_eq]
    by_cases hp : 3*0 < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      by_cases hz : sy = 0
      · simpa only [check_eq,if_pos hz] using hc
      · rw [if_neg hz]
  | succ f ih =>
    rw [BBNew360Grow.check_eq]
    by_cases hp : 3*(f+1) < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      rw [check_eq] at hc
      by_cases hz : sy = 0
      · rwa [if_pos hz] at *
      · rw [if_neg hz]
        rw [if_neg hz] at hc
        change (if 3*(f+1) < ones sy then true else (nbr (BBNew360High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr upd f (j::used) (C j ^^^ sy) (upd j sy (ones sy))) = true at hc
        rw [if_neg hp] at hc
        apply List.all_eq_true.mpr
        intro j hj
        have hh := List.all_eq_true.mp hc j hj
        by_cases hu : j ∈ used
        · simp [hu]
        · rw [if_neg hu,hupd] at hh
          simpa only [if_neg hu] using ih (j::used) (C j ^^^ sy) hh
end BBNew360FastGrow

open BBNew360Cert BBNew360Search BBNew360KernelData
namespace BBNew360KernelSearch
lemma anchor180_5_0_0 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [141, 142, 322, 180] 1393796576855275268296616539715753559982081 6 = true := by decide +kernel
lemma anchor180_5_0_2 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [173, 142, 322, 180] 17958932119522135060184953439051466439641018012794881 6 = true := by decide +kernel
lemma anchor180_5_0_3 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [187, 142, 322, 180] 1298074214633780694108919461576833 6 = true := by decide +kernel
lemma anchor180_5_0_4 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [321, 142, 322, 180] 10889037039544245464645575034882926575617 6 = true := by decide +kernel
lemma anchor180_5_0_5 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [329, 142, 322, 180] 713623846354278014743786210151822226406506497 6 = true := by decide +kernel
lemma anchor180_5_1_1 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [144, 143, 322, 180] 22300745206319068429338033502420400842211329 6 = true := by decide +kernel
lemma anchor180_5_1_2 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [175, 143, 322, 180] 71835728478088540238143665326938230583369939359367169 6 = true := by decide +kernel
lemma anchor180_5_1_3 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [189, 143, 322, 180] 2596148429267487601241543007011331 6 = true := by decide +kernel
lemma anchor180_5_1_4 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [301, 143, 322, 180] 2661052139999137012340718620729409537 6 = true := by decide +kernel
lemma anchor180_5_1_5 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [323, 143, 322, 180] 43556145562028552590947124945399014490113 6 = true := by decide +kernel
lemma anchor180_5_2_0 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [26, 174, 322, 180] 11972621413014756705924586149611864283997694335123457 6 = true := by decide +kernel
lemma anchor180_5_2_2 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [175, 174, 322, 180] 59863107076224156128888242318826885408407472555687937 6 = true := by decide +kernel
lemma anchor180_5_2_3 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [220, 174, 322, 180] 11972621413014756705924586149611864283998798041055233 6 = true := by decide +kernel
lemma anchor180_5_2_4 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [332, 174, 322, 180] 11972627122005527529845240021170348763674028770590721 6 = true := by decide +kernel
lemma anchor180_5_2_5 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [354, 174, 322, 180] 12066157517803934492689938891555763454606048093011969 6 = true := by decide +kernel
lemma anchor180_5_3_0 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [66, 188, 322, 180] 36893488164603166976 4 = true := by decide +kernel
lemma anchor180_5_3_1 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [67, 188, 322, 180] 147573952624040345856 4 = true := by decide +kernel
lemma anchor180_5_3_2 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [98, 188, 322, 180] 475368975085586025561267896576 4 = true := by decide +kernel
lemma anchor180_5_3_3 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [246, 188, 322, 180] 309485009821345068730024192 4 = true := by decide +kernel
lemma anchor180_5_3_4 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [254, 188, 322, 180] 18889465931478853484800 4 = true := by decide +kernel
lemma anchor180_5_4_0 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [120, 300, 322, 180] 713623846685286939475390916203607106684715009 6 = true := by decide +kernel
lemma anchor180_5_4_1 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [121, 300, 322, 180] 3323069989462308645512425424124116993 6 = true := by decide +kernel
lemma anchor180_5_4_2 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [152, 300, 322, 180] 8563486156235759286349734779949878591719735297 6 = true := by decide +kernel
lemma anchor180_5_4_3 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [196, 300, 322, 180] 18963252907773423321345 6 = true := by decide +kernel
lemma anchor180_5_4_5 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 6 [308, 300, 322, 180] 340282366920943318129905973721890291713 6 = true := by decide +kernel
lemma anchor180_5_0 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 7 [142, 322, 180] 2787593151114402107325745478189964112953345 5 = true := by
  apply BBNew360FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BBNew360High.pick (2787593151114402107325745478189964112953345 : BitVec 180)) = [141, 142, 173, 187, 321, 329] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor180_5_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor180_5_0_2
    · exact anchor180_5_0_3
    · exact anchor180_5_0_4
    · exact anchor180_5_0_5
lemma anchor180_5_1 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 7 [143, 322, 180] 11150372601861460000035346737565723760001025 5 = true := by
  apply BBNew360FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BBNew360High.pick (11150372601861460000035346737565723760001025 : BitVec 180)) = [143, 144, 175, 189, 301, 323] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor180_5_1_1
    · exact anchor180_5_1_2
    · exact anchor180_5_1_3
    · exact anchor180_5_1_4
    · exact anchor180_5_1_5
lemma anchor180_5_2 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 7 [174, 322, 180] 35917864239044270117773758448835445278040493018578945 5 = true := by
  apply BBNew360FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BBNew360High.pick (35917864239044270117773758448835445278040493018578945 : BitVec 180)) = [26, 174, 175, 220, 332, 354] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor180_5_2_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor180_5_2_2
    · exact anchor180_5_2_3
    · exact anchor180_5_2_4
    · exact anchor180_5_2_5
lemma anchor180_5_3 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 7 [188, 322, 180] 73786976294842401024 3 = true := by
  apply BBNew360FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BBNew360High.pick (73786976294842401024 : BitVec 180)) = [66, 67, 98, 246, 254, 322] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor180_5_3_0
    · exact anchor180_5_3_1
    · exact anchor180_5_3_2
    · exact anchor180_5_3_3
    · exact anchor180_5_3_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor180_5_4 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 7 [300, 322, 180] 1329227995784934836156714833703600129 5 = true := by
  apply BBNew360FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BBNew360High.pick (1329227995784934836156714833703600129 : BitVec 180)) = [120, 121, 152, 196, 300, 308] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor180_5_4_0
    · exact anchor180_5_4_1
    · exact anchor180_5_4_2
    · exact anchor180_5_4_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor180_5_4_5
lemma anchor180_5 : BBNew360FastGrow.check xmask xrem xneighbors xupdate 8 [322, 180] 5575186299632655785384003355138385218895873 4 = true := by
  apply BBNew360FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BBNew360High.pick (5575186299632655785384003355138385218895873 : BitVec 180)) = [142, 143, 174, 188, 300, 322] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor180_5_0
    · exact anchor180_5_1
    · exact anchor180_5_2
    · exact anchor180_5_3
    · exact anchor180_5_4
    · exact False.elim (hju (by decide +kernel))
end BBNew360KernelSearch
theorem bound (v : BBCode.Qubit 6 30 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0,0)) ≠ 0)
    (hb : v (Sum.inr (4,22)) ≠ 0) :
    ∃ u : BBCode.Qubit 6 30 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)}) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := by
  have h0 := hb
  have hc := BBNew360FastGrow.sound xmask xrem xneighbors xupdate xupdate_spec
    8 [322,180] (xmask 322 ^^^ xmask 180)
    (by rw [show (xmask 322 ^^^ xmask 180) = (5575186299632655785384003355138385218895873 : BitVec 180) from by decide +kernel]
        simpa only [show BBNew360Search.ones (5575186299632655785384003355138385218895873 : BitVec 180) = 4 from by decide +kernel] using BBNew360KernelSearch.anchor180_5)
  have hh := BBNew360Chunk.pair_chunk 180 322 (by decide +kernel) hc v
    (by simpa only [show eqb (180 : Fin 360) = (Sum.inr (0,0)) from by decide +kernel] using ha)
    (by simpa only [show eqb (322 : Fin 360) = (Sum.inr (4,22)) from by decide +kernel] using h0) hw hv
  simpa only [polyA,polyB,show eqb (180 : Fin 360) = (Sum.inr (0,0)) from by decide +kernel] using hh
end BBNew360Split_right_companion322

theorem solution (v : BBCode.Qubit 6 30 → ZMod 2)
    (hv : BBCode.HX {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0,0)) ≠ 0)
    (hb : v (Sum.inr (4,22)) ≠ 0) :
    ∃ u : BBCode.Qubit 6 30 → ZMod 2,
      BBCode.HX {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(0,0),(0,1),(1,2)} {(0,0),(0,8),(2,16)}) ∧
      u (Sum.inr (0,0)) ≠ 0 ∧ ∀ p, u p ≠ 0 → v p ≠ 0 := BBNew360Split_right_companion322.bound v hv hw ha hb
#print axioms solution
