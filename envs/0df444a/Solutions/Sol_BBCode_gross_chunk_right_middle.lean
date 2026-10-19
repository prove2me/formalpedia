-- Prove2me | solution 1 for BBCode.gross_chunk_right_middle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T10:11:07.785981+00:00
-- url     : https://prove2.me/submissions/bc5b624e-4534-40e6-8dbe-109f2a933ba6

import Definitions.Def_BBCode_Setting
open Matrix
namespace BB144Split_right_middle
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode
namespace BB144Cert

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

end BB144Cert

set_option maxHeartbeats 0
open Matrix BBCode BB144Cert
namespace BB144Bits

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
end BB144Bits

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB144Cert BB144Bits
namespace BB144KernelData
def xmask (j : Fin 144) : BitVec 72 := BitVec.ofNat 72 (if j.val < 72 then (if j.val < 36 then (if j.val < 18 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 18014398509482032 else 36028797018964001) else (if j.val < 3 then 72057594037927939 else 144115188075855878)) else (if j.val < 6 then (if j.val < 5 then 288230376151711756 else 576460752303423512) else (if j.val < 7 then 1152921504606850048 else (if j.val < 8 then 2305843009213696064 else 4611686018427388096)))) else (if j.val < 13 then (if j.val < 11 then (if j.val < 10 then 9223372036854776192 else 18446744073709552384) else (if j.val < 12 then 36893488147419104768 else 73786976294838403072)) else (if j.val < 15 then (if j.val < 14 then 147573952589676548096 else 295147905179352838144) else (if j.val < 16 then 590295810358705676288 else (if j.val < 17 then 1180591620717411352576 else 2361183241434822705152))))) else (if j.val < 27 then (if j.val < 22 then (if j.val < 20 then (if j.val < 19 then 12582913 else 8650754) else (if j.val < 21 then 786436 else 1572872)) else (if j.val < 24 then (if j.val < 23 then 3145744 else 6291488) else (if j.val < 25 then 805306432 else (if j.val < 26 then 553648256 else 50331904)))) else (if j.val < 31 then (if j.val < 29 then (if j.val < 28 then 100663808 else 201327616) else (if j.val < 30 then 402655232 else 51539611648)) else (if j.val < 33 then (if j.val < 32 then 35433488384 else 3221241856) else (if j.val < 34 then 6442483712 else (if j.val < 35 then 12884967424 else 25769934848)))))) else (if j.val < 54 then (if j.val < 45 then (if j.val < 40 then (if j.val < 38 then (if j.val < 37 then 3298535145472 else 2267743256576) else (if j.val < 39 then 206159478784 else 412318957568)) else (if j.val < 42 then (if j.val < 41 then 824637915136 else 1649275830272) else (if j.val < 43 then 211106249310208 else (if j.val < 44 then 145135568420864 else 13194206642176)))) else (if j.val < 49 then (if j.val < 47 then (if j.val < 46 then 26388413284352 else 52776826568704) else (if j.val < 48 then 105553653137408 else 13510799955853312)) else (if j.val < 51 then (if j.val < 50 then 9288676378935296 else 844429225099264) else (if j.val < 52 then 1688858450198528 else (if j.val < 53 then 3377716900397056 else 6755433800794112))))) else (if j.val < 63 then (if j.val < 58 then (if j.val < 56 then (if j.val < 55 then 864691197174611968 else 594475288251858944) else (if j.val < 57 then 54043470406352896 else 108086940812705792)) else (if j.val < 60 then (if j.val < 59 then 216173881625411584 else 432347763250823168) else (if j.val < 61 then 55340236619175165952 else (if j.val < 62 then 38046418448118972416 else 3458782106006585344)))) else (if j.val < 67 then (if j.val < 65 then (if j.val < 64 then 6917564212013170688 else 13835128424026341376) else (if j.val < 66 then 27670256848052682752 else 3541775143627210620928)) else (if j.val < 69 then (if j.val < 68 then 2434970780679614234624 else 221362054784421462016) else (if j.val < 70 then 442724109568842924032 else (if j.val < 71 then 885448219137685848064 else 1770896438275371696128))))))) else (if j.val < 108 then (if j.val < 90 then (if j.val < 81 then (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then 74939897799445053448 else 149879795598890106896) else (if j.val < 75 then 299759591197780213792 else 599519182395560427521)) else (if j.val < 78 then (if j.val < 77 then 1199038364791120855042 else 2398076729582241710084) else (if j.val < 79 then 73786976294838206977 else (if j.val < 80 then 147573952589676413954 else 295147905179352827908)))) else (if j.val < 85 then (if j.val < 83 then (if j.val < 82 then 590295810358705651784 else 1180591620717411303568) else (if j.val < 84 then 2361183241434822607136 else 32833)) else (if j.val < 87 then (if j.val < 86 then 65666 else 131332) else (if j.val < 88 then 4616 else (if j.val < 89 then 9232 else 18464))))) else (if j.val < 99 then (if j.val < 94 then (if j.val < 92 then (if j.val < 91 then 2101312 else 4202624) else (if j.val < 93 then 8405248 else 295424)) else (if j.val < 96 then (if j.val < 95 then 590848 else 1181696) else (if j.val < 97 then 134483968 else (if j.val < 98 then 268967936 else 537935872)))) else (if j.val < 103 then (if j.val < 101 then (if j.val < 100 then 18907136 else 37814272) else (if j.val < 102 then 75628544 else 8606973952)) else (if j.val < 105 then (if j.val < 104 then 17213947904 else 34427895808) else (if j.val < 106 then 1210056704 else (if j.val < 107 then 2420113408 else 4840226816)))))) else (if j.val < 126 then (if j.val < 117 then (if j.val < 112 then (if j.val < 110 then (if j.val < 109 then 550846332928 else 1101692665856) else (if j.val < 111 then 2203385331712 else 77443629056)) else (if j.val < 114 then (if j.val < 113 then 154887258112 else 309774516224) else (if j.val < 115 then 35254165307392 else (if j.val < 116 then 70508330614784 else 141016661229568)))) else (if j.val < 121 then (if j.val < 119 then (if j.val < 118 then 4956392259584 else 9912784519168) else (if j.val < 120 then 19825569038336 else 2256266579673088)) else (if j.val < 123 then (if j.val < 122 then 4512533159346176 else 9025066318692352) else (if j.val < 124 then 317209104613376 else (if j.val < 125 then 634418209226752 else 1268836418453504))))) else (if j.val < 135 then (if j.val < 130 then (if j.val < 128 then (if j.val < 127 then 144401061099077632 else 288802122198155264) else (if j.val < 129 then 577604244396310528 else 20301382695256064)) else (if j.val < 132 then (if j.val < 131 then 40602765390512128 else 81205530781024256) else (if j.val < 133 then 9241667910340968448 else (if j.val < 134 then 18483335820681936896 else 36966671641363873792)))) else (if j.val < 139 then (if j.val < 137 then (if j.val < 136 then 1299288492496388096 else 2598576984992776192) else (if j.val < 138 then 5197153969985552384 else 591466746261821980672)) else (if j.val < 141 then (if j.val < 140 then 1182933492523643961344 else 2365866985047287922688) else (if j.val < 142 then 83154463519768838144 else (if j.val < 143 then 166308927039537676288 else 332617854079075352576))))))))
def xH : Matrix (Fin 72) (Fin 144) (ZMod 2) := fun i j => entry (xmask j) i
def zmask (j : Fin 144) : BitVec 72 := BitVec.ofNat 72 (if j.val < 72 then (if j.val < 36 then (if j.val < 18 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 4168 else 8336) else (if j.val < 3 then 16672 else 33281)) else (if j.val < 6 then (if j.val < 5 then 66562 else 133124) else (if j.val < 7 then 266752 else (if j.val < 8 then 533504 else 1067008)))) else (if j.val < 13 then (if j.val < 11 then (if j.val < 10 then 2129984 else 4259968) else (if j.val < 12 then 8519936 else 17072128)) else (if j.val < 15 then (if j.val < 14 then 34144256 else 68288512) else (if j.val < 16 then 136318976 else (if j.val < 17 then 272637952 else 545275904))))) else (if j.val < 27 then (if j.val < 22 then (if j.val < 20 then (if j.val < 19 then 1092616192 else 2185232384) else (if j.val < 21 then 4370464768 else 8724414464)) else (if j.val < 24 then (if j.val < 23 then 17448828928 else 34897657856) else (if j.val < 25 then 69927436288 else (if j.val < 26 then 139854872576 else 279709745152)))) else (if j.val < 31 then (if j.val < 29 then (if j.val < 28 then 558362525696 else 1116725051392) else (if j.val < 30 then 2233450102784 else 4475355922432)) else (if j.val < 33 then (if j.val < 32 then 8950711844864 else 17901423689728) else (if j.val < 34 then 35735201644544 else (if j.val < 35 then 71470403289088 else 142940806578176)))))) else (if j.val < 54 then (if j.val < 45 then (if j.val < 40 then (if j.val < 38 then (if j.val < 37 then 286422779035648 else 572845558071296) else (if j.val < 39 then 1145691116142592 else 2287052905250816)) else (if j.val < 42 then (if j.val < 41 then 4574105810501632 else 9148211621003264) else (if j.val < 43 then 18331057858281472 else (if j.val < 44 then 36662115716562944 else 73324231433125888)))) else (if j.val < 49 then (if j.val < 47 then (if j.val < 46 then 146371385936052224 else 292742771872104448) else (if j.val < 48 then 585485543744208896 else 1173187702930014208)) else (if j.val < 51 then (if j.val < 50 then 2346375405860028416 else 4692750811720056832) else (if j.val < 52 then 9367768699907342336 else (if j.val < 53 then 18735537399814684672 else 37471074799629369344))))) else (if j.val < 63 then (if j.val < 58 then (if j.val < 56 then (if j.val < 55 then 75084012987520909312 else 150168025975041818624) else (if j.val < 57 then 300336051950083637248 else 599537196794069909504)) else (if j.val < 60 then (if j.val < 59 then 1199074393588139819008 else 2398148787176279638016) else (if j.val < 61 then 83010348331692982273 else (if j.val < 62 then 166020696663385964546 else 332041393326771929092)))) else (if j.val < 67 then (if j.val < 65 then (if j.val < 64 then 591448731863312498696 else 1182897463726624997392) else (if j.val < 66 then 2365794927453249994784 else 590295810358705651777)) else (if j.val < 69 then (if j.val < 68 then 1180591620717411303554 else 2361183241434822607108) else (if j.val < 70 then 73786976294838206984 else (if j.val < 71 then 147573952589676413968 else 295147905179352827936))))))) else (if j.val < 108 then (if j.val < 90 then (if j.val < 81 then (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then 262150 else 524300) else (if j.val < 75 then 1048600 else 2097200)) else (if j.val < 78 then (if j.val < 77 then 4194337 else 8388611) else (if j.val < 79 then 16777600 else (if j.val < 80 then 33555200 else 67110400)))) else (if j.val < 85 then (if j.val < 83 then (if j.val < 82 then 134220800 else 268437568) else (if j.val < 84 then 536871104 else 1073766400)) else (if j.val < 87 then (if j.val < 86 then 2147532800 else 4295065600) else (if j.val < 88 then 8590131200 else (if j.val < 89 then 17180004352 else 34359750656))))) else (if j.val < 99 then (if j.val < 94 then (if j.val < 92 then (if j.val < 91 then 68721049600 else 137442099200) else (if j.val < 93 then 274884198400 else 549768396800)) else (if j.val < 96 then (if j.val < 95 then 1099520278528 else 2199024041984) else (if j.val < 97 then 4398147174400 else (if j.val < 98 then 8796294348800 else 17592588697600)))) else (if j.val < 103 then (if j.val < 101 then (if j.val < 100 then 35185177395200 else 70369297825792) else (if j.val < 102 then 140737538686976 else 281481419161600)) else (if j.val < 105 then (if j.val < 104 then 562962838323200 else 1125925676646400) else (if j.val < 106 then 2251851353292800 else (if j.val < 107 then 4503635060850688 else 9007202475966464)))))) else (if j.val < 126 then (if j.val < 117 then (if j.val < 112 then (if j.val < 110 then (if j.val < 109 then 18014810826342400 else 36029621652684800) else (if j.val < 111 then 72059243305369600 else 144118486610739200)) else (if j.val < 114 then (if j.val < 113 then 288232643894444032 else 576460958461853696) else (if j.val < 115 then 1152947892885913600 else (if j.val < 116 then 2305895785771827200 else 4611791571543654400)))) else (if j.val < 121 then (if j.val < 119 then (if j.val < 118 then 9223583143087308800 else 18446889209244418048) else (if j.val < 120 then 36893501341558636544 else 73788665144698470400)) else (if j.val < 123 then (if j.val < 122 then 147577330289396940800 else 295154660578793881600) else (if j.val < 124 then 590309321157587763200 else (if j.val < 125 then 1180600909391642755072 else 2361184085859752738816))))) else (if j.val < 135 then (if j.val < 130 then (if j.val < 128 then (if j.val < 127 then 108086391056891905 else 216172782113783810) else (if j.val < 129 then 432345564227567620 else 864691128455135240)) else (if j.val < 132 then (if j.val < 131 then 594475150812905488 else 54043195528445984) else (if j.val < 133 then 6917529027641081920 else (if j.val < 134 then 13835058055282163840 else 27670116110564327680)))) else (if j.val < 139 then (if j.val < 137 then (if j.val < 136 then 55340232221128655360 else 38046409652025951232) else (if j.val < 138 then 3458764513820542976 else 442721857769029242880)) else (if j.val < 141 then (if j.val < 140 then 885443715538058485760 else 1770887431076116971520) else (if j.val < 142 then 3541774862152233943040 else (if j.val < 143 then 2434970217729660878848 else 221360928884514750464))))))))
def zrow (i : Fin 72) : BitVec 144 := BitVec.ofNat 144 (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 85070591730234842614374727400357363720 else 170141183460469387719661034013066264592) else (if i.val < 3 then 340282366920938477930233647238484066336 else 680564733841876955860467294476968132609)) else (if i.val < 6 then (if i.val < 5 then 1361129467683753911720934588953936265218 else 2722258935367507823441869177907872530436) else (if i.val < 7 then 5444517870735029922597616070753226064385 else (if i.val < 8 then 10889035741470040804613573211096950506498 else 21778071482940062568645487491784399390724)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 43556142965880125137290974983568798777416 else 87112285931760250274581949967137597554832) else (if i.val < 12 then 174224571863520500549163899934275195109664 else 348449143727041915041525062045336822906945)) else (if i.val < 15 then (if i.val < 14 then 696898287454082611485823952544465541988482 else 1393796574908164004374421733542722980151556) else (if i.val < 16 then 2787593149816328008748843467085445960045064 else (if i.val < 17 then 5575186299632656017497686934170891920090128 else 11150372599265312034995373868341783840180256))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 59421126608064736064805277760 else 40852030741150514810965729408) else (if i.val < 21 then 3713839007322072303286632704 else 7427678014644144606556750336)) else (if i.val < 24 then (if i.val < 23 then 14855356029288289213113500672 else 29710712058576578426227001344) else (if i.val < 25 then 3802952102916143108147537776640 else (if i.val < 26 then 2614529967433632947901806682112 else 237685696468612627410344493056)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 475371392937225254819632021504 else 950742785874450509639264043008) else (if i.val < 30 then 1901485571748901019278528086016 else 243388934586633158921442417704960)) else (if i.val < 33 then (if i.val < 32 then 167329917915752508665715627655168 else 15211884573991208154262047555584) else (if i.val < 34 then 30423769147982416308456449376256 else (if i.val < 35 then 60847538295964832616912898752512 else 121695076591929665233825797505024)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 15576891813544522170972314733117440 else 10709114746608160554605800169930752) else (if i.val < 39 then 973560612735437321872771043557376 else 1947121225470874643741212760080384)) else (if i.val < 42 then (if i.val < 41 then 3894242450941749287482425520160768 else 7788484901883498574964851040321536) else (if i.val < 43 then 996921076066849418942228142919516160 else (if i.val < 44 then 685383343782922275494771210875568128 else 62307879215067988599857346787672064)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 124615758430135977199437616645144576 else 249231516860271954398875233290289152) else (if i.val < 48 then 498463033720543908797750466580578304 else 63802948868278362812302601146849034240)) else (if i.val < 51 then (if i.val < 50 then 43864534002107025631665357496036360192 else 3987704269764351270390870194411012096) else (if i.val < 52 then 7975408539528702540764007465289252864 else (if i.val < 53 then 15950817079057405081528014930578505728 else 31901634158114810163056029861157011456))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 4083388727569815219987366473398338191360 else 2807330176134849640426582879746327052288) else (if i.val < 57 then 255213073264918481305015692442304774144 else 510426146529836962608896477778512183296)) else (if i.val < 60 then (if i.val < 59 then 1020852293059673925217792955557024366592 else 2041704586119347850435585911114048733184) else (if i.val < 61 then 261336878564468174079191454297493644247040 else (if i.val < 62 then 179669131272630376987301304303764931346432 else 16333636688954782803521004316307505545216)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 32667273377909565606969374577824779730944 else 65334546755819131213938749155649559461888) else (if i.val < 66 then 130669093511638262427877498311299118923776 else 16725560228125963141068253075039593231810560)) else (if i.val < 69 then (if i.val < 68 then 11498824401448344127187283475440955606171648 else 1045352748093106099425344276243680354893824) else (if i.val < 70 then 2090705496186212198846039972980785902780416 else (if i.val < 71 then 4181410992372424397692079945961571805560832 else 8362821984744848795384159891923143611121664)))))))
def zH : Matrix (Fin 72) (Fin 144) (ZMod 2) := fun i j => entry (zmask j) i
lemma zrow_bits : ∀ i j, (zrow i).getLsbD j.val = (zmask j).getLsbD i.val := by decide +kernel
lemma zrow_entry (i : Fin 72) (j : Fin 144) : entry (zrow i) j = zH i j := by
  change entry (zrow i) j = entry (zmask j) i
  unfold entry; rw [zrow_bits]
def xcoef (j : Fin 144) : BitVec 72 := BitVec.ofNat 72 (if j.val < 72 then (if j.val < 36 then (if j.val < 18 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 232044391480976225410 else 81729046819824172641) else (if j.val < 3 then 5198422806479652864 else 1)) else (if j.val < 6 then (if j.val < 5 then 9243924177055158339 else 151183914935362097822) else (if j.val < 7 then 79129835416584345696 else (if j.val < 8 then 9243924177055159363 else 151183914935362099870)))) else (if j.val < 13 then (if j.val < 11 then (if j.val < 10 then 232044391480976225474 else 238257496943896283682) else (if j.val < 12 then 231037590123883833250 else 232044391480976258243)) else (if j.val < 15 then (if j.val < 14 then 229014144650326465121 else 86780777664006796604) else (if j.val < 16 then 163599711355783249122 else (if j.val < 17 then 90972399113393916450 else 156382337741841732254))))) else (if j.val < 27 then (if j.val < 22 then (if j.val < 20 then (if j.val < 19 then 73931412610102591488 else 147862825220205182976) else (if j.val < 21 then 91979200470477911356 else 154360853728309181666)) else (if j.val < 24 then (if j.val < 23 then 80140577423351336185 else 159128233410798524915) else (if j.val < 25 then 9243924176920641536 else (if j.val < 26 then 13137674732602918619 else 15736886136111631213)))) else (if j.val < 31 then (if j.val < 29 then (if j.val < 28 then 1299605701601001472 else 2599211403202002944) else (if j.val < 30 then 5198422806404005888 else 153061248035298114786)) else (if j.val < 33 then (if j.val < 32 then 82739788843733208313 else 164326656251562269171) else (if j.val < 34 then 83174764902464094208 else (if j.val < 35 then 160422772560961996507 else 76530624018185928273)))))) else (if j.val < 54 then (if j.val < 45 then (if j.val < 40 then (if j.val < 38 then (if j.val < 37 then 84181565709786021888 else 158401289646970242779) else (if j.val < 39 then 81729044625566678609 else 162305172143499279586)) else (if j.val < 42 then (if j.val < 41 then 88373187865079171618 else 151183915245212242590) else (if j.val < 43 then 226992625391235398882 else (if j.val < 44 then 230024956903397510393 else 222805120888169606351)))) else (if j.val < 49 then (if j.val < 47 then (if j.val < 46 then 237242818143130647778 else 238257487063596648994) else (if j.val < 48 then 231037609954293098402 else 74939897799445053440)) else (if j.val < 51 then (if j.val < 50 then 149879795598890106880 else 86789804933710820668) else (if j.val < 52 then 163599957036368297186 else (if j.val < 53 then 90971764850071947810 else 156381069215197794974))))) else (if j.val < 63 then (if j.val < 58 then (if j.val < 56 then (if j.val < 55 then 73786976294838206464 else 147573952589676412928) else (if j.val < 57 then 91401490952138208572 else 154376584999513521378)) else (if j.val < 60 then (if j.val < 59 then 80181190101526367481 else 159209458767148587507) else (if j.val < 61 then 0 else (if j.val < 62 then 0 else 0)))) else (if j.val < 67 then (if j.val < 65 then (if j.val < 64 then 0 else 0) else (if j.val < 66 then 0 else 0)) else (if j.val < 69 then (if j.val < 68 then 0 else 0) else (if j.val < 70 then 0 else (if j.val < 71 then 0 else 0))))))) else (if j.val < 108 then (if j.val < 90 then (if j.val < 81 then (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then 9243924177055158337 else 160422772562836390619) else (if j.val < 75 then 76530624013344519761 else 5198422806479652896)) else (if j.val < 78 then (if j.val < 77 then 0 else 0) else (if j.val < 79 then 157106749397264544963 else (if j.val < 80 then 79129835416584346209 else 0)))) else (if j.val < 85 then (if j.val < 83 then (if j.val < 82 then 0 else 0) else (if j.val < 84 then 0 else 0)) else (if j.val < 87 then (if j.val < 86 then 0 else 0) else (if j.val < 88 then 0 else (if j.val < 89 then 0 else 0))))) else (if j.val < 99 then (if j.val < 94 then (if j.val < 92 then (if j.val < 91 then 0 else 0) else (if j.val < 93 then 0 else 0)) else (if j.val < 96 then (if j.val < 95 then 0 else 0) else (if j.val < 97 then 0 else (if j.val < 98 then 0 else 0)))) else (if j.val < 103 then (if j.val < 101 then (if j.val < 100 then 0 else 0) else (if j.val < 102 then 0 else 0)) else (if j.val < 105 then (if j.val < 104 then 0 else 0) else (if j.val < 106 then 0 else (if j.val < 107 then 0 else 0)))))) else (if j.val < 126 then (if j.val < 117 then (if j.val < 112 then (if j.val < 110 then (if j.val < 109 then 0 else 0) else (if j.val < 111 then 0 else 0)) else (if j.val < 114 then (if j.val < 113 then 0 else 0) else (if j.val < 115 then 0 else (if j.val < 116 then 0 else 0)))) else (if j.val < 121 then (if j.val < 119 then (if j.val < 118 then 0 else 0) else (if j.val < 120 then 0 else 0)) else (if j.val < 123 then (if j.val < 122 then 0 else 0) else (if j.val < 124 then 0 else (if j.val < 125 then 0 else 0))))) else (if j.val < 135 then (if j.val < 130 then (if j.val < 128 then (if j.val < 127 then 0 else 0) else (if j.val < 129 then 0 else 0)) else (if j.val < 132 then (if j.val < 131 then 0 else 0) else (if j.val < 133 then 0 else (if j.val < 134 then 0 else 0)))) else (if j.val < 139 then (if j.val < 137 then (if j.val < 136 then 0 else 0) else (if j.val < 138 then 0 else 0)) else (if j.val < 141 then (if j.val < 140 then 0 else 0) else (if j.val < 142 then 0 else (if j.val < 143 then 0 else 0))))))))
def xrem (j : Fin 144) : BitVec 144 := BitVec.ofNat 144 (if j.val < 72 then (if j.val < 36 then (if j.val < 18 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then 6473386298533336779858749847188202319773696 else 2590494650188288765045473851822845827481600) else (if j.val < 3 then 12736805482902284568570283936164349984374784 else 85070591730234842614374727400357363712)) else (if j.val < 6 then (if j.val < 5 then 3178565476150685518437270030771801598984192 else 19662270921528455909579098877600152537792512) else (if j.val < 7 then 7507876702551710038332788178630331022180352 else (if j.val < 8 then 3265677762082445763876148702280422497714176 else 19836495493391976410128262777534427732901888)))) else (if j.val < 13 then (if j.val < 11 then (if j.val < 10 then 6478830816404071790438534349424888750538752 else 15746591482376376618236160556496235637243904) else (if j.val < 12 then 9540885601170914779489022239491996245819392 else 9266509036812129956205244979593392269819904)) else (if j.val < 15 then (if j.val < 14 then 18184652671580402564721540395578895659696128 else 1061718357501593296996412507413001092988928) else (if j.val < 16 then 2123436714683660652508115013130149295030272 else (if j.val < 17 then 4246789667558917974835353299076671632048128 else 8493495573309432619489829870969716306083840))))) else (if j.val < 27 then (if j.val < 22 then (if j.val < 20 then (if j.val < 19 then 16726135594578476501510225705065217513226240 else 11499890063766711215856275809446333039771648) else (if j.val < 21 then 1047399002143180644548376018208564092862464 else 2094797983836701034372821016303330813542400)) else (if j.val < 24 then (if j.val < 23 then 4184235211935588937169531492854536314290176 else 8363109668133364742762952445956947315785728) else (if j.val < 25 then 36823452960855068286250627482963224297472 else (if j.val < 26 then 68202388375493674815513988030174177787904 else 130960259204770887874040709124596084768768)))) else (if j.val < 31 then (if j.val < 29 then (if j.val < 28 then 261919209631285473714005219386947998318592 else 180750052042530526556935894637875977781248) else (if j.val < 30 then 18411736865020632242797245139731936706560 else 2356700989494724370320040158909646355038208)) else (if j.val < 33 then (if j.val < 32 then 4364952856031595188192895233931147378425856 else 8381456589105336823938605383974149425201152) else (if j.val < 34 then 16762829416402270317696334040764671892389888 else (if j.val < 35 then 11568003330721953699643897256824062577999872 else 1178351159361320463539023688942843949219840)))))) else (if j.val < 54 then (if j.val < 45 then (if j.val < 40 then (if j.val < 38 then (if j.val < 37 then 17023711571744778974337210937811860065353728 else 11746679274186930592054576506782418905071616) else (if j.val < 39 then 1192614679071233827489307644723536584507392 else 2385228049683659304197331686200633167183872)) else (if j.val < 42 then (if j.val < 41 then 4427451473511012637223581768110043977220096 else 8511898321165719303276081931928865597292544) else (if j.val < 43 then 19081685991604213329213453097220676236869632 else (if j.val < 44 then 15862711855269533751507053765444848909811712 else 9424763582600174596094255101893194255695872)))) else (if j.val < 49 then (if j.val < 47 then (if j.val < 46 then 18849443423836614742483868684435016042676224 else 15746590792869647330018514694231801227902976) else (if j.val < 48 then 9540885530935712505087806713825371598356480 else 16986897106690431315147444493026814880382976)) else (if j.val < 51 then (if j.val < 50 then 11678493532720974504174584707124176546168832 else 1061686384782060882228865135318899877740544) else (if j.val < 52 then 2123372769564121764453009057076434717114368 else (if j.val < 53 then 4246745539128243528906018114152869434228736 else 8493491078256487057812036228305738868457472))))) else (if j.val < 63 then (if j.val < 58 then (if j.val < 56 then (if j.val < 55 then 16725560228125963141068253057025194722328576 else 11498824401448344127187283439412158587207680) else (if j.val < 57 then 1045352748093106099425344204186086316965888 else 2090705496186212198846039828865597826924544)) else (if j.val < 60 then (if j.val < 59 then 4181410992372424397692079657731195653849088 else 8362821984744848795384159315462391307698176) else (if j.val < 61 then 1152921504606846976 else (if j.val < 62 then 2305843009213693952 else 4611686018427387904)))) else (if j.val < 67 then (if j.val < 65 then (if j.val < 64 then 9223372036854775808 else 18446744073709551616) else (if j.val < 66 then 36893488147419103232 else 73786976294838206464)) else (if j.val < 69 then (if j.val < 68 then 147573952589676412928 else 295147905179352825856) else (if j.val < 70 then 590295810358705651712 else (if j.val < 71 then 1180591620717411303424 else 2361183241434822606848))))))) else (if j.val < 108 then (if j.val < 90 then (if j.val < 81 then (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then 3178395334967225049356504191124315471609856 else 17230301916454706335492757622734279696973824) else (if j.val < 75 then 12502948330507299793756755632628790334586880 else 12739527741837652076351150720020136211775488)) else (if j.val < 78 then (if j.val < 77 then 75557863725914323419136 else 151115727451828646838272) else (if j.val < 79 then 14754586709255716636032230469186347029495808 else (if j.val < 80 then 7551517916109320394835701325532924999630848 else 1208925819614629174706176)))) else (if j.val < 85 then (if j.val < 83 then (if j.val < 82 then 2417851639229258349412352 else 4835703278458516698824704) else (if j.val < 84 then 9671406556917033397649408 else 19342813113834066795298816)) else (if j.val < 87 then (if j.val < 86 then 38685626227668133590597632 else 77371252455336267181195264) else (if j.val < 88 then 154742504910672534362390528 else (if j.val < 89 then 309485009821345068724781056 else 618970019642690137449562112))))) else (if j.val < 99 then (if j.val < 94 then (if j.val < 92 then (if j.val < 91 then 1237940039285380274899124224 else 2475880078570760549798248448) else (if j.val < 93 then 4951760157141521099596496896 else 9903520314283042199192993792)) else (if j.val < 96 then (if j.val < 95 then 19807040628566084398385987584 else 39614081257132168796771975168) else (if j.val < 97 then 79228162514264337593543950336 else (if j.val < 98 then 158456325028528675187087900672 else 316912650057057350374175801344)))) else (if j.val < 103 then (if j.val < 101 then (if j.val < 100 then 633825300114114700748351602688 else 1267650600228229401496703205376) else (if j.val < 102 then 2535301200456458802993406410752 else 5070602400912917605986812821504)) else (if j.val < 105 then (if j.val < 104 then 10141204801825835211973625643008 else 20282409603651670423947251286016) else (if j.val < 106 then 40564819207303340847894502572032 else (if j.val < 107 then 81129638414606681695789005144064 else 162259276829213363391578010288128)))))) else (if j.val < 126 then (if j.val < 117 then (if j.val < 112 then (if j.val < 110 then (if j.val < 109 then 324518553658426726783156020576256 else 649037107316853453566312041152512) else (if j.val < 111 then 1298074214633706907132624082305024 else 2596148429267413814265248164610048)) else (if j.val < 114 then (if j.val < 113 then 5192296858534827628530496329220096 else 10384593717069655257060992658440192) else (if j.val < 115 then 20769187434139310514121985316880384 else (if j.val < 116 then 41538374868278621028243970633760768 else 83076749736557242056487941267521536)))) else (if j.val < 121 then (if j.val < 119 then (if j.val < 118 then 166153499473114484112975882535043072 else 332306998946228968225951765070086144) else (if j.val < 120 then 664613997892457936451903530140172288 else 1329227995784915872903807060280344576)) else (if j.val < 123 then (if j.val < 122 then 2658455991569831745807614120560689152 else 5316911983139663491615228241121378304) else (if j.val < 124 then 10633823966279326983230456482242756608 else (if j.val < 125 then 21267647932558653966460912964485513216 else 42535295865117307932921825928971026432))))) else (if j.val < 135 then (if j.val < 130 then (if j.val < 128 then (if j.val < 127 then 85070591730234615865843651857942052864 else 170141183460469231731687303715884105728) else (if j.val < 129 then 340282366920938463463374607431768211456 else 680564733841876926926749214863536422912)) else (if j.val < 132 then (if j.val < 131 then 1361129467683753853853498429727072845824 else 2722258935367507707706996859454145691648) else (if j.val < 133 then 5444517870735015415413993718908291383296 else (if j.val < 134 then 10889035741470030830827987437816582766592 else 21778071482940061661655974875633165533184)))) else (if j.val < 139 then (if j.val < 137 then (if j.val < 136 then 43556142965880123323311949751266331066368 else 87112285931760246646623899502532662132736) else (if j.val < 138 then 174224571863520493293247799005065324265472 else 348449143727040986586495598010130648530944)) else (if j.val < 141 then (if j.val < 140 then 696898287454081973172991196020261297061888 else 1393796574908163946345982392040522594123776) else (if j.val < 142 then 2787593149816327892691964784081045188247552 else (if j.val < 143 then 5575186299632655785383929568162090376495104 else 11150372599265311570767859136324180752990208))))))))
def xD : Matrix (Fin 72) (Fin 144) (ZMod 2) := fun i j => entry (xcoef j) i
def xK : Matrix (Fin 144) (Fin 144) (ZMod 2) := fun i j => entry (xrem j) i
lemma xdecomp_bits : ∀ j, combination zrow (xcoef j) ^^^ xrem j = unit j := by decide +kernel
lemma xdecomp : zH.transpose * xD + xK = 1 := by
  have h := decomposition zrow xcoef xrem xdecomp_bits
  have he : (Matrix.of fun i j => entry (zrow i) j) = zH := by
    apply Matrix.ext; intro i j; exact zrow_entry i j
  rw [he] at h
  exact h
def xneighbors (i : Fin 72) : List (Fin 144) := (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [1, 2, 18, 75, 78, 84] else [2, 3, 19, 76, 79, 85]) else (if i.val < 3 then [3, 4, 20, 77, 80, 86] else [4, 5, 21, 72, 81, 87])) else (if i.val < 6 then (if i.val < 5 then [0, 5, 22, 73, 82, 88] else [0, 1, 23, 74, 83, 89]) else (if i.val < 7 then [7, 8, 24, 81, 84, 90] else (if i.val < 8 then [8, 9, 25, 82, 85, 91] else [9, 10, 26, 83, 86, 92])))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then [10, 11, 27, 78, 87, 93] else [6, 11, 28, 79, 88, 94]) else (if i.val < 12 then [6, 7, 29, 80, 89, 95] else [13, 14, 30, 87, 90, 96])) else (if i.val < 15 then (if i.val < 14 then [14, 15, 31, 88, 91, 97] else [15, 16, 32, 89, 92, 98]) else (if i.val < 16 then [16, 17, 33, 84, 93, 99] else (if i.val < 17 then [12, 17, 34, 85, 94, 100] else [12, 13, 35, 86, 95, 101]))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then [19, 20, 36, 93, 96, 102] else [20, 21, 37, 94, 97, 103]) else (if i.val < 21 then [21, 22, 38, 95, 98, 104] else [22, 23, 39, 90, 99, 105])) else (if i.val < 24 then (if i.val < 23 then [18, 23, 40, 91, 100, 106] else [18, 19, 41, 92, 101, 107]) else (if i.val < 25 then [25, 26, 42, 99, 102, 108] else (if i.val < 26 then [26, 27, 43, 100, 103, 109] else [27, 28, 44, 101, 104, 110])))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then [28, 29, 45, 96, 105, 111] else [24, 29, 46, 97, 106, 112]) else (if i.val < 30 then [24, 25, 47, 98, 107, 113] else [31, 32, 48, 105, 108, 114])) else (if i.val < 33 then (if i.val < 32 then [32, 33, 49, 106, 109, 115] else [33, 34, 50, 107, 110, 116]) else (if i.val < 34 then [34, 35, 51, 102, 111, 117] else (if i.val < 35 then [30, 35, 52, 103, 112, 118] else [30, 31, 53, 104, 113, 119])))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then [37, 38, 54, 111, 114, 120] else [38, 39, 55, 112, 115, 121]) else (if i.val < 39 then [39, 40, 56, 113, 116, 122] else [40, 41, 57, 108, 117, 123])) else (if i.val < 42 then (if i.val < 41 then [36, 41, 58, 109, 118, 124] else [36, 37, 59, 110, 119, 125]) else (if i.val < 43 then [43, 44, 60, 117, 120, 126] else (if i.val < 44 then [44, 45, 61, 118, 121, 127] else [45, 46, 62, 119, 122, 128])))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then [46, 47, 63, 114, 123, 129] else [42, 47, 64, 115, 124, 130]) else (if i.val < 48 then [42, 43, 65, 116, 125, 131] else [49, 50, 66, 123, 126, 132])) else (if i.val < 51 then (if i.val < 50 then [50, 51, 67, 124, 127, 133] else [51, 52, 68, 125, 128, 134]) else (if i.val < 52 then [52, 53, 69, 120, 129, 135] else (if i.val < 53 then [48, 53, 70, 121, 130, 136] else [48, 49, 71, 122, 131, 137]))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then [0, 55, 56, 129, 132, 138] else [1, 56, 57, 130, 133, 139]) else (if i.val < 57 then [2, 57, 58, 131, 134, 140] else [3, 58, 59, 126, 135, 141])) else (if i.val < 60 then (if i.val < 59 then [4, 54, 59, 127, 136, 142] else [5, 54, 55, 128, 137, 143]) else (if i.val < 61 then [6, 61, 62, 72, 135, 138] else (if i.val < 62 then [7, 62, 63, 73, 136, 139] else [8, 63, 64, 74, 137, 140])))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then [9, 64, 65, 75, 132, 141] else [10, 60, 65, 76, 133, 142]) else (if i.val < 66 then [11, 60, 61, 77, 134, 143] else [12, 67, 68, 72, 78, 141])) else (if i.val < 69 then (if i.val < 68 then [13, 68, 69, 73, 79, 142] else [14, 69, 70, 74, 80, 143]) else (if i.val < 70 then [15, 70, 71, 75, 81, 138] else (if i.val < 71 then [16, 66, 71, 76, 82, 139] else [17, 66, 67, 77, 83, 140])))))))
def xnbr (i : Fin 72) (t : Fin 6) : Fin 144 := (xneighbors i).getD t.val 0
end BB144KernelData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB144Cert
namespace BB144Search

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
end BB144Search

set_option maxHeartbeats 0
open BB144Search
namespace BB144Count
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
end BB144Count

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open BB144Search BB144KernelData
namespace BB144KernelData
def xpos (j : Fin 144) : List (Fin 72) := (if j.val < 72 then (if j.val < 36 then (if j.val < 18 then (if j.val < 9 then (if j.val < 4 then (if j.val < 2 then (if j.val < 1 then [4, 5, 54] else [0, 5, 55]) else (if j.val < 3 then [0, 1, 56] else [1, 2, 57])) else (if j.val < 6 then (if j.val < 5 then [2, 3, 58] else [3, 4, 59]) else (if j.val < 7 then [10, 11, 60] else (if j.val < 8 then [6, 11, 61] else [6, 7, 62])))) else (if j.val < 13 then (if j.val < 11 then (if j.val < 10 then [7, 8, 63] else [8, 9, 64]) else (if j.val < 12 then [9, 10, 65] else [16, 17, 66])) else (if j.val < 15 then (if j.val < 14 then [12, 17, 67] else [12, 13, 68]) else (if j.val < 16 then [13, 14, 69] else (if j.val < 17 then [14, 15, 70] else [15, 16, 71]))))) else (if j.val < 27 then (if j.val < 22 then (if j.val < 20 then (if j.val < 19 then [0, 22, 23] else [1, 18, 23]) else (if j.val < 21 then [2, 18, 19] else [3, 19, 20])) else (if j.val < 24 then (if j.val < 23 then [4, 20, 21] else [5, 21, 22]) else (if j.val < 25 then [6, 28, 29] else (if j.val < 26 then [7, 24, 29] else [8, 24, 25])))) else (if j.val < 31 then (if j.val < 29 then (if j.val < 28 then [9, 25, 26] else [10, 26, 27]) else (if j.val < 30 then [11, 27, 28] else [12, 34, 35])) else (if j.val < 33 then (if j.val < 32 then [13, 30, 35] else [14, 30, 31]) else (if j.val < 34 then [15, 31, 32] else (if j.val < 35 then [16, 32, 33] else [17, 33, 34])))))) else (if j.val < 54 then (if j.val < 45 then (if j.val < 40 then (if j.val < 38 then (if j.val < 37 then [18, 40, 41] else [19, 36, 41]) else (if j.val < 39 then [20, 36, 37] else [21, 37, 38])) else (if j.val < 42 then (if j.val < 41 then [22, 38, 39] else [23, 39, 40]) else (if j.val < 43 then [24, 46, 47] else (if j.val < 44 then [25, 42, 47] else [26, 42, 43])))) else (if j.val < 49 then (if j.val < 47 then (if j.val < 46 then [27, 43, 44] else [28, 44, 45]) else (if j.val < 48 then [29, 45, 46] else [30, 52, 53])) else (if j.val < 51 then (if j.val < 50 then [31, 48, 53] else [32, 48, 49]) else (if j.val < 52 then [33, 49, 50] else (if j.val < 53 then [34, 50, 51] else [35, 51, 52]))))) else (if j.val < 63 then (if j.val < 58 then (if j.val < 56 then (if j.val < 55 then [36, 58, 59] else [37, 54, 59]) else (if j.val < 57 then [38, 54, 55] else [39, 55, 56])) else (if j.val < 60 then (if j.val < 59 then [40, 56, 57] else [41, 57, 58]) else (if j.val < 61 then [42, 64, 65] else (if j.val < 62 then [43, 60, 65] else [44, 60, 61])))) else (if j.val < 67 then (if j.val < 65 then (if j.val < 64 then [45, 61, 62] else [46, 62, 63]) else (if j.val < 66 then [47, 63, 64] else [48, 70, 71])) else (if j.val < 69 then (if j.val < 68 then [49, 66, 71] else [50, 66, 67]) else (if j.val < 70 then [51, 67, 68] else (if j.val < 71 then [52, 68, 69] else [53, 69, 70]))))))) else (if j.val < 108 then (if j.val < 90 then (if j.val < 81 then (if j.val < 76 then (if j.val < 74 then (if j.val < 73 then [3, 60, 66] else [4, 61, 67]) else (if j.val < 75 then [5, 62, 68] else [0, 63, 69])) else (if j.val < 78 then (if j.val < 77 then [1, 64, 70] else [2, 65, 71]) else (if j.val < 79 then [0, 9, 66] else (if j.val < 80 then [1, 10, 67] else [2, 11, 68])))) else (if j.val < 85 then (if j.val < 83 then (if j.val < 82 then [3, 6, 69] else [4, 7, 70]) else (if j.val < 84 then [5, 8, 71] else [0, 6, 15])) else (if j.val < 87 then (if j.val < 86 then [1, 7, 16] else [2, 8, 17]) else (if j.val < 88 then [3, 9, 12] else (if j.val < 89 then [4, 10, 13] else [5, 11, 14]))))) else (if j.val < 99 then (if j.val < 94 then (if j.val < 92 then (if j.val < 91 then [6, 12, 21] else [7, 13, 22]) else (if j.val < 93 then [8, 14, 23] else [9, 15, 18])) else (if j.val < 96 then (if j.val < 95 then [10, 16, 19] else [11, 17, 20]) else (if j.val < 97 then [12, 18, 27] else (if j.val < 98 then [13, 19, 28] else [14, 20, 29])))) else (if j.val < 103 then (if j.val < 101 then (if j.val < 100 then [15, 21, 24] else [16, 22, 25]) else (if j.val < 102 then [17, 23, 26] else [18, 24, 33])) else (if j.val < 105 then (if j.val < 104 then [19, 25, 34] else [20, 26, 35]) else (if j.val < 106 then [21, 27, 30] else (if j.val < 107 then [22, 28, 31] else [23, 29, 32])))))) else (if j.val < 126 then (if j.val < 117 then (if j.val < 112 then (if j.val < 110 then (if j.val < 109 then [24, 30, 39] else [25, 31, 40]) else (if j.val < 111 then [26, 32, 41] else [27, 33, 36])) else (if j.val < 114 then (if j.val < 113 then [28, 34, 37] else [29, 35, 38]) else (if j.val < 115 then [30, 36, 45] else (if j.val < 116 then [31, 37, 46] else [32, 38, 47])))) else (if j.val < 121 then (if j.val < 119 then (if j.val < 118 then [33, 39, 42] else [34, 40, 43]) else (if j.val < 120 then [35, 41, 44] else [36, 42, 51])) else (if j.val < 123 then (if j.val < 122 then [37, 43, 52] else [38, 44, 53]) else (if j.val < 124 then [39, 45, 48] else (if j.val < 125 then [40, 46, 49] else [41, 47, 50]))))) else (if j.val < 135 then (if j.val < 130 then (if j.val < 128 then (if j.val < 127 then [42, 48, 57] else [43, 49, 58]) else (if j.val < 129 then [44, 50, 59] else [45, 51, 54])) else (if j.val < 132 then (if j.val < 131 then [46, 52, 55] else [47, 53, 56]) else (if j.val < 133 then [48, 54, 63] else (if j.val < 134 then [49, 55, 64] else [50, 56, 65])))) else (if j.val < 139 then (if j.val < 137 then (if j.val < 136 then [51, 57, 60] else [52, 58, 61]) else (if j.val < 138 then [53, 59, 62] else [54, 60, 69])) else (if j.val < 141 then (if j.val < 140 then [55, 61, 70] else [56, 62, 71]) else (if j.val < 142 then [57, 63, 66] else (if j.val < 143 then [58, 64, 67] else [59, 65, 68]))))))))
lemma xpos_spec : ∀ j, (xpos j).Nodup ∧ (xpos j).toFinset = Finset.univ.filter (fun i => (xmask j).getLsbD i.val) := by decide +kernel
lemma xthree : ∀ j, ones (xmask j) = 3 := by decide +kernel
def xupdate (j : Fin 144) (sy : BitVec 72) (pc : ℕ) : ℕ :=
  pc + 3 - 2 * ((xpos j).map fun i => (sy.getLsbD i.val).toNat).sum
lemma xupdate_spec (j : Fin 144) (sy : BitVec 72) : xupdate j sy (ones sy) = ones (xmask j ^^^ sy) :=
  BB144Count.update_eq (xmask j) sy (xpos j) (xpos_spec j).1 (xpos_spec j).2 (xthree j)
end BB144KernelData

set_option maxHeartbeats 0
open Matrix BBCode
namespace BB144Symmetry

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
    have he := (BB144Cert.rowspace_reindex (HX A B) negG dualQ v)
    rw [HX_dual] at he
    exact hv.2 (he.mp h)
end BB144Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Matrix BBCode BB144Cert BB144Bits BB144Search
namespace BB144KernelData
def polyA : Poly 12 6 := {(3,0),(0,1),(0,2)}
def polyB : Poly 12 6 := {(0,3),(1,0),(2,0)}
def er : Fin 72 ≃ Grp 12 6 where
  toFun i := ((i.val / 6 : ℕ), (i.val % 6 : ℕ))
  invFun g := ⟨g.1.val * 6 + g.2.val, by
    have h1 := ZMod.val_lt g.1
    have h2 := ZMod.val_lt g.2
    omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def eqb : Fin 144 ≃ Qubit 12 6 where
  toFun i := if h : i.val < 72 then Sum.inl (er ⟨i.val,h⟩)
    else Sum.inr (er ⟨i.val-72,by omega⟩)
  invFun q := match q with
    | Sum.inl g => ⟨(er.symm g).val, by have h := (er.symm g).isLt; omega⟩
    | Sum.inr g => ⟨72 + (er.symm g).val, by have h := (er.symm g).isLt; omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

namespace BB144Sparse

lemma col_three (a b c g : Grp 12 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 72) :
    circulant {a,b,c} (er i) g =
      entry (unit (er.symm (g-a)) ^^^ unit (er.symm (g-b)) ^^^ unit (er.symm (g-c))) i := by
  have eqg (t : Grp 12 6) : i = er.symm (g-t) ↔ g-er i = t := by
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

def column (q : Qubit 12 6) : BitVec 72 :=
  match q with
  | Sum.inl g => unit (er.symm (g-(3,0))) ^^^ unit (er.symm (g-(0,1))) ^^^ unit (er.symm (g-(0,2)))
  | Sum.inr g => unit (er.symm (g-(0,3))) ^^^ unit (er.symm (g-(1,0))) ^^^ unit (er.symm (g-(2,0)))

lemma column_entry (i : Fin 72) (q : Qubit 12 6) :
    HX polyA polyB (er i) q = entry (column q) i := by
  cases q with
  | inl g => exact col_three (3,0) (0,1) (0,2) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three (0,3) (1,0) (2,0) g (by decide) (by decide) (by decide) i

lemma xcolumn_bits : ∀ j, xmask j = column (eqb j) := by decide +kernel
lemma xtable_sparse : (HX polyA polyB).submatrix er eqb = xH := by
  ext i j
  change HX polyA polyB (er i) (eqb j) = entry (xmask j) i
  rw [xcolumn_bits,column_entry]
end BB144Sparse

lemma xtable : (HX polyA polyB).submatrix er eqb = xH := BB144Sparse.xtable_sparse
namespace BB144Sparse
lemma col_three_z (a b c g : Grp 12 6) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin 72) :
    circulant {a,b,c} g (er i) =
      entry (unit (er.symm (g+a)) ^^^ unit (er.symm (g+b)) ^^^ unit (er.symm (g+c))) i := by
  have eqg (t : Grp 12 6) : i = er.symm (g+t) ↔ er i-g = t := by
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


def zcolumn (q : Qubit 12 6) : BitVec 72 :=
  match q with
  | Sum.inl g => unit (er.symm (g+(0,3))) ^^^ unit (er.symm (g+(1,0))) ^^^ unit (er.symm (g+(2,0)))
  | Sum.inr g => unit (er.symm (g+(3,0))) ^^^ unit (er.symm (g+(0,1))) ^^^ unit (er.symm (g+(0,2)))

lemma zcolumn_entry (i : Fin 72) (q : Qubit 12 6) :
    HZ polyA polyB (er i) q = entry (zcolumn q) i := by
  cases q with
  | inl g => exact col_three_z (0,3) (1,0) (2,0) g (by decide) (by decide) (by decide) i
  | inr g => exact col_three_z (3,0) (0,1) (0,2) g (by decide) (by decide) (by decide) i

lemma zcolumn_bits : ∀ j, zmask j = zcolumn (eqb j) := by decide +kernel
lemma ztable_sparse : (HZ polyA polyB).submatrix er eqb = zH := by
  ext i j
  change HZ polyA polyB (er i) (eqb j) = entry (zmask j) i
  rw [zcolumn_bits,zcolumn_entry]
end BB144Sparse

lemma ztable : (HZ polyA polyB).submatrix er eqb = zH := BB144Sparse.ztable_sparse
lemma xones (j : Fin 144) : ones (xmask j) ≤ 3 := (xthree j).le
lemma xpos_cover : ∀ j, (xpos j).all (fun i => decide (j ∈ xneighbors i)) = true := by decide +kernel
lemma xcover (i : Fin 72) (j : Fin 144) (h : entry (xmask j) i = 1) : j ∈ xneighbors i := by
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

lemma unindex_kernel (H : Matrix (Grp 12 6) (Qubit 12 6) (ZMod 2))
    (v : Fin 144 → ZMod 2) (hv : H.submatrix er eqb *ᵥ v = 0) :
    H *ᵥ (v ∘ eqb.symm) = 0 := by
  have h := Matrix.submatrix_mulVec_equiv H v er eqb
  rw [hv] at h
  funext i
  have hi := congrFun h (er.symm i)
  simpa using hi.symm

lemma index_kernel (H : Matrix (Grp 12 6) (Qubit 12 6) (ZMod 2))
    (v : Qubit 12 6 → ZMod 2) (hv : H *ᵥ v = 0) :
    H.submatrix er eqb *ᵥ (v ∘ eqb) = 0 := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : (v ∘ eqb) ∘ eqb.symm = v := by funext i; simp
  rw [he,hv]
  rfl

end BB144KernelData

set_option maxHeartbeats 0
namespace BB144High

def seek {r : ℕ} (s : BitVec r) : ℕ → ℕ → ℕ
  | 0, start => start
  | fuel+1, start => if s.getLsbD start then start else seek s fuel (start+1)

lemma seek_spec {r : ℕ} (s : BitVec r) (fuel start : ℕ)
    (hex : ∃ i, start ≤ i ∧ i < start+fuel ∧ s.getLsbD i = true) :
    seek s fuel start < start+fuel ∧ s.getLsbD (seek s fuel start) = true := by
  induction fuel generalizing start with
  | zero => obtain ⟨i,hi,hlt,_⟩ := hex; omega
  | succ f ih =>
    rw [seek]
    cases hb : s.getLsbD start with
    | true => simp only [hb,ite_true]; exact ⟨by omega,True.intro⟩
    | false =>
      simp only [hb,Bool.false_eq_true,ite_false]
      apply (show start + (f+1) = start+1+f by omega) ▸ ih (start+1)
      obtain ⟨i,hi,hlt,hb'⟩ := hex
      refine ⟨i,?_,by omega,hb'⟩
      by_contra hh
      have he : i = start := by omega
      subst i
      rw [hb] at hb'
      contradiction

lemma seek_lt {r : ℕ} (s : BitVec r) (hs : s ≠ 0) :
    seek s r 0 < r ∧ s.getLsbD (seek s r 0) = true := by
  suffices hex : ∃ i, 0 ≤ i ∧ i < 0+r ∧ s.getLsbD i = true by
    simpa only [Nat.zero_add] using seek_spec s r 0 hex
  by_contra h
  apply hs
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : s.getLsbD i ≠ true := by intro he; exact h ⟨i,by omega,by simpa using hi,he⟩
  simpa using hn

def pick {r : ℕ} [NeZero r] (s : BitVec r) : Fin r :=
  if h : s = 0 then 0 else ⟨seek s r 0,(seek_lt s h).1⟩

lemma pick_spec {r : ℕ} [NeZero r] (s : BitVec r) (hs : s ≠ 0) :
    s.getLsbD (pick s).val = true := by
  simpa only [pick,dif_neg hs] using (seek_lt s hs).2
end BB144High

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Matrix BBCode BB144Cert
namespace BB144Grow

open BB144Search

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) : ℕ → List (Fin n) → BitVec r → Bool
  | fuel, used, sy =>
    if 3 * fuel < ones sy then true
    else if sy = 0 then decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => (nbr (BB144High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr fuel (j :: used) (C j ^^^ sy)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) :
    check C K nbr fuel used sy =
      if 3 * fuel < ones sy then true
      else if sy = 0 then decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => (nbr (BB144High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr f (j :: used) (C j ^^^ sy) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r)
    (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (BB144High.pick sy), j ∉ used → check C K nbr fuel (j::used) (C j ^^^ sy) = true) :
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
end BB144Grow

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix BBCode BB144Cert BB144Search
namespace BB144Grow

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
        let i := BB144High.pick (signature C used)
        have hp : entry (signature C used) i = 1 := by
          simp [entry,i,BB144High.pick_spec _ hz]
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
end BB144Grow

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
open Matrix BBCode BB144Cert BB144Search BB144KernelData
namespace BB144Chunk

lemma pair_chunk (anchor j : Fin 144) (hj : j ≠ anchor)
    (hc : BB144Grow.check xmask xrem xneighbors 8 [j,anchor]
      (xmask j ^^^ xmask anchor) = true)
    (v : Qubit 12 6 → ZMod 2) (ha : v (eqb anchor) ≠ 0) (hvj : v (eqb j) ≠ 0)
    (hw : weight v ≤ 10) (hv : HX polyA polyB *ᵥ v = 0) :
    ∃ u : Qubit 12 6 → ZMod 2,
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
  have hc' : BB144Grow.check xmask xrem xneighbors 8 [j,anchor]
      (signature xmask [j,anchor]) = true := by simpa [signature] using hc
  have hweight : T.card ≤ 10 := by
    change weight (v ∘ eqb) ≤ 10
    rwa [weight_equiv]
  obtain ⟨S,hST,hAS,hSC,hSK⟩ := BB144Grow.extract xmask xrem xneighbors xones xcover T hT
    8 [j,anchor] hn hu (by simpa using hweight) hc'
  let z : Fin 144 → ZMod 2 := fun q => if q ∈ S then 1 else 0
  have hzS : (Finset.univ.filter fun q => z q ≠ 0) = S := by ext q; simp [z]
  have hzX : xH *ᵥ z = 0 := by
    ext i
    rw [support_mul,hzS]
    exact hSC i
  have hzK : xK *ᵥ z = 0 := by
    ext i
    rw [support_mul,hzS]
    exact hSK i
  have hdec : zH.transpose * xD + (1 : Matrix (Fin 144) (Fin 144) (ZMod 2)) * xK = 1 := by
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
end BB144Chunk

set_option maxHeartbeats 0
open BB144Cert BB144Search
namespace BB144FastGrow

def check {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ) :
    ℕ → List (Fin n) → BitVec r → ℕ → Bool
  | fuel, used, sy, pc =>
    if sy = 0 then decide (signature K used = 0)
    else match fuel with
      | 0 => true
      | fuel+1 => if 3*(fuel+1) < pc then true else (nbr (BB144High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr upd fuel (j :: used) (C j ^^^ sy) (upd j sy pc)

lemma check_eq {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) (pc : ℕ) :
    check C K nbr upd fuel used sy pc =
      if sy = 0 then decide (signature K used = 0)
      else match fuel with
        | 0 => true
        | f+1 => if 3*(f+1) < pc then true else (nbr (BB144High.pick sy)).all fun j => if j ∈ used then true else
            check C K nbr upd f (j :: used) (C j ^^^ sy) (upd j sy pc) := by
  cases fuel <;> rfl

lemma step {r k n : ℕ} [NeZero r] (C : Fin n → BitVec r) (K : Fin n → BitVec k)
    (nbr : Fin r → List (Fin n)) (upd : Fin n → BitVec r → ℕ → ℕ)
    (fuel : ℕ) (used : List (Fin n)) (sy : BitVec r) (pc : ℕ) (hs : sy ≠ 0)
    (hc : ∀ j ∈ nbr (BB144High.pick sy), j ∉ used →
      check C K nbr upd fuel (j::used) (C j ^^^ sy) (upd j sy pc) = true) :
    check C K nbr upd (fuel+1) used sy pc = true := by
  rw [check_eq,if_neg hs]
  change (if 3*(fuel+1) < pc then true else (nbr (BB144High.pick sy)).all fun j =>
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
    BB144Grow.check C K nbr fuel used sy = true := by
  induction fuel generalizing used sy with
  | zero =>
    rw [BB144Grow.check_eq]
    by_cases hp : 3*0 < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      by_cases hz : sy = 0
      · simpa only [check_eq,if_pos hz] using hc
      · rw [if_neg hz]
  | succ f ih =>
    rw [BB144Grow.check_eq]
    by_cases hp : 3*(f+1) < ones sy
    · rw [if_pos hp]
    · rw [if_neg hp]
      rw [check_eq] at hc
      by_cases hz : sy = 0
      · rwa [if_pos hz] at *
      · rw [if_neg hz]
        rw [if_neg hz] at hc
        change (if 3*(f+1) < ones sy then true else (nbr (BB144High.pick sy)).all fun j =>
          if j ∈ used then true else check C K nbr upd f (j::used) (C j ^^^ sy) (upd j sy (ones sy))) = true at hc
        rw [if_neg hp] at hc
        apply List.all_eq_true.mpr
        intro j hj
        have hh := List.all_eq_true.mp hc j hj
        by_cases hu : j ∈ used
        · simp [hu]
        · rw [if_neg hu,hupd] at hh
          simpa only [if_neg hu] using ih (j::used) (C j ^^^ sy) hh
end BB144FastGrow

open BB144Cert BB144Search BB144KernelData
namespace BB144KernelSearch
lemma anchor72_2_0_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [3, 20, 21, 72] 75084012987522220034 6 = true := by decide +kernel
lemma anchor72_2_0_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [4, 20, 21, 72] 75228128175598075912 6 = true := by decide +kernel
lemma anchor72_2_0_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [77, 20, 21, 72] 2473016627381688074240 6 = true := by decide +kernel
lemma anchor72_2_0_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [80, 20, 21, 72] 370087802978799192064 6 = true := by decide +kernel
lemma anchor72_2_0_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [86, 20, 21, 72] 74939897799446495488 6 = true := by decide +kernel
lemma anchor72_2_2_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [22, 37, 21, 72] 74939900067189882896 6 = true := by decide +kernel
lemma anchor72_2_2_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [38, 37, 21, 72] 74939900135907262464 4 = true := by decide +kernel
lemma anchor72_2_2_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [95, 37, 21, 72] 74939900067187918848 6 = true := by decide +kernel
lemma anchor72_2_2_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [98, 37, 21, 72] 74939900067724673024 6 = true := by decide +kernel
lemma anchor72_2_2_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [104, 37, 21, 72] 74939900101614632960 6 = true := by decide +kernel
lemma anchor72_2_3_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [6, 94, 21, 72] 73786976294839322624 4 = true := by decide +kernel
lemma anchor72_2_3_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [11, 94, 21, 72] 111833385946865271296 6 = true := by decide +kernel
lemma anchor72_2_3_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [28, 94, 21, 72] 74939897799647494144 6 = true := by decide +kernel
lemma anchor72_2_3_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [79, 94, 21, 72] 222513850389122580482 6 = true := by decide +kernel
lemma anchor72_2_3_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [88, 94, 21, 72] 74939897799446175760 6 = true := by decide +kernel
lemma anchor72_2_4_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [14, 97, 21, 72] 370087802979067367424 6 = true := by decide +kernel
lemma anchor72_2_4_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [15, 97, 21, 72] 665235708158420205568 6 = true := by decide +kernel
lemma anchor72_2_4_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [31, 97, 21, 72] 74939897835148017664 6 = true := by decide +kernel
lemma anchor72_2_4_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [88, 97, 21, 72] 74939897799714538512 6 = true := by decide +kernel
lemma anchor72_2_4_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [91, 97, 21, 72] 74939897799718731904 6 = true := by decide +kernel
lemma anchor72_2_5_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [22, 103, 21, 72] 74939897816660574224 6 = true := by decide +kernel
lemma anchor72_2_5_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [38, 103, 21, 72] 74939898022816907264 6 = true := by decide +kernel
lemma anchor72_2_5_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [95, 103, 21, 72] 74939897816658610176 6 = true := by decide +kernel
lemma anchor72_2_5_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [98, 103, 21, 72] 74939897817195364352 6 = true := by decide +kernel
lemma anchor72_2_5_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [104, 103, 21, 72] 74939897851085324288 6 = true := by decide +kernel
lemma anchor72_4_0_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [6, 7, 81, 72] 666388629662757553152 4 = true := by decide +kernel
lemma anchor72_4_0_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [29, 7, 81, 72] 667541551167767052288 6 = true := by decide +kernel
lemma anchor72_4_0_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [80, 7, 81, 72] 962689456346717224964 6 = true := by decide +kernel
lemma anchor72_4_0_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [89, 7, 81, 72] 667541551167364415520 6 = true := by decide +kernel
lemma anchor72_4_0_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [95, 7, 81, 72] 667541551167365578752 6 = true := by decide +kernel
lemma anchor72_4_1_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [9, 8, 81, 72] 679070766213432869120 6 = true := by decide +kernel
lemma anchor72_4_1_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [25, 8, 81, 72] 669847394177131741184 6 = true := by decide +kernel
lemma anchor72_4_1_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [82, 8, 81, 72] 1850439014893989396496 6 = true := by decide +kernel
lemma anchor72_4_1_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [85, 8, 81, 72] 669847394176578158594 6 = true := by decide +kernel
lemma anchor72_4_1_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [91, 8, 81, 72] 669847394176582295552 6 = true := by decide +kernel
lemma anchor72_4_2_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [29, 24, 81, 72] 665235708158821795840 6 = true := by decide +kernel
lemma anchor72_4_2_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [46, 24, 81, 72] 665235760935245709312 6 = true := by decide +kernel
lemma anchor72_4_2_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [97, 24, 81, 72] 665235708158688108544 6 = true := by decide +kernel
lemma anchor72_4_2_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [106, 24, 81, 72] 665235708160839254016 6 = true := by decide +kernel
lemma anchor72_4_2_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [112, 24, 81, 72] 665235708313306398720 6 = true := by decide +kernel
lemma anchor72_4_4_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [1, 84, 81, 72] 665271736955169701920 6 = true := by decide +kernel
lemma anchor72_4_4_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [2, 84, 81, 72] 665307765752188665858 6 = true := by decide +kernel
lemma anchor72_4_4_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [18, 84, 81, 72] 665235708158163320832 6 = true := by decide +kernel
lemma anchor72_4_4_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [75, 84, 81, 72] 84163269836299862016 4 = true := by decide +kernel
lemma anchor72_4_4_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [78, 84, 81, 72] 591448731863312531968 4 = true := by decide +kernel
lemma anchor72_4_5_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [13, 90, 81, 72] 812809660747829346304 6 = true := by decide +kernel
lemma anchor72_4_5_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [14, 90, 81, 72] 960383613337505636352 6 = true := by decide +kernel
lemma anchor72_4_5_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [30, 90, 81, 72] 665235708209692409856 6 = true := by decide +kernel
lemma anchor72_4_5_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [87, 90, 81, 72] 665235708158152802824 6 = true := by decide +kernel
lemma anchor72_4_5_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 6 [96, 90, 81, 72] 665235708158287282176 6 = true := by decide +kernel
lemma anchor72_2_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [20, 21, 72] 74939897799446364164 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (74939897799446364164 : BitVec 72)) = [3, 4, 20, 77, 80, 86] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_2_0_0
    · exact anchor72_2_0_1
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_2_0_3
    · exact anchor72_2_0_4
    · exact anchor72_2_0_5
lemma anchor72_2_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [37, 21, 72] 74939900067188834304 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (74939900067188834304 : BitVec 72)) = [21, 22, 38, 95, 98, 104] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_2_2_1
    · exact anchor72_2_2_2
    · exact anchor72_2_2_3
    · exact anchor72_2_2_4
    · exact anchor72_2_2_5
lemma anchor72_2_3 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [94, 21, 72] 74939897799446168576 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (74939897799446168576 : BitVec 72)) = [6, 11, 28, 79, 88, 94] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_2_3_0
    · exact anchor72_2_3_1
    · exact anchor72_2_3_2
    · exact anchor72_2_3_3
    · exact anchor72_2_3_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor72_2_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [97, 21, 72] 74939897799714545664 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (74939897799714545664 : BitVec 72)) = [14, 15, 31, 88, 91, 97] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_2_4_0
    · exact anchor72_2_4_1
    · exact anchor72_2_4_2
    · exact anchor72_2_4_3
    · exact anchor72_2_4_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor72_2_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [103, 21, 72] 74939897816659525632 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (74939897816659525632 : BitVec 72)) = [21, 22, 38, 95, 98, 104] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_2_5_1
    · exact anchor72_2_5_2
    · exact anchor72_2_5_3
    · exact anchor72_2_5_4
    · exact anchor72_2_5_5
lemma anchor72_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 8 [21, 72] 74939897799446626304 4 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (74939897799446626304 : BitVec 72)) = [20, 21, 37, 94, 97, 103] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_2_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_2_2
    · exact anchor72_2_3
    · exact anchor72_2_4
    · exact anchor72_2_5
lemma anchor72_4_0 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [7, 81, 72] 667541551167364401152 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (667541551167364401152 : BitVec 72)) = [6, 7, 29, 80, 89, 95] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_4_0_0
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_4_0_2
    · exact anchor72_4_0_3
    · exact anchor72_4_0_4
    · exact anchor72_4_0_5
lemma anchor72_4_1 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [8, 81, 72] 669847394176578093184 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (669847394176578093184 : BitVec 72)) = [8, 9, 25, 82, 85, 91] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_4_1_1
    · exact anchor72_4_1_2
    · exact anchor72_4_1_3
    · exact anchor72_4_1_4
    · exact anchor72_4_1_5
lemma anchor72_4_2 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [24, 81, 72] 665235708158956011520 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (665235708158956011520 : BitVec 72)) = [24, 29, 46, 97, 106, 112] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_4_2_1
    · exact anchor72_4_2_2
    · exact anchor72_4_2_3
    · exact anchor72_4_2_4
    · exact anchor72_4_2_5
lemma anchor72_4_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [84, 81, 72] 665235708158150737921 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (665235708158150737921 : BitVec 72)) = [1, 2, 18, 75, 78, 84] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_4_4_0
    · exact anchor72_4_4_1
    · exact anchor72_4_4_2
    · exact anchor72_4_4_3
    · exact anchor72_4_4_4
    · exact False.elim (hju (by decide +kernel))
lemma anchor72_4_5 : BB144FastGrow.check xmask xrem xneighbors xupdate 7 [90, 81, 72] 665235708158152806400 5 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (665235708158152806400 : BitVec 72)) = [13, 14, 30, 87, 90, 96] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_4_5_0
    · exact anchor72_4_5_1
    · exact anchor72_4_5_2
    · exact anchor72_4_5_3
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_4_5_5
lemma anchor72_4 : BB144FastGrow.check xmask xrem xneighbors xupdate 8 [81, 72] 665235708158150705216 4 = true := by
  apply BB144FastGrow.step
  · decide +kernel
  · intro j hj hju
    have hn : xneighbors (BB144High.pick (665235708158150705216 : BitVec 72)) = [7, 8, 24, 81, 84, 90] := by decide +kernel
    rw [hn] at hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact anchor72_4_0
    · exact anchor72_4_1
    · exact anchor72_4_2
    · exact False.elim (hju (by decide +kernel))
    · exact anchor72_4_4
    · exact anchor72_4_5
end BB144KernelSearch
theorem bound (v : BBCode.Qubit 12 6 → ZMod 2)
    (hv : BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (3, 3)) ≠ 0 ∨ v (Sum.inr (1, 3)) ≠ 0) :
    ∃ u : BBCode.Qubit 12 6 → ZMod 2,
      BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)}) ∧
      u (Sum.inr (0, 0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := by
  rcases hb with h0 | h1
  · have hc := BB144FastGrow.sound xmask xrem xneighbors xupdate xupdate_spec
      8 [21,72] (xmask 21 ^^^ xmask 72)
      (by rw [show (xmask 21 ^^^ xmask 72) = (74939897799446626304 : BitVec 72) from by decide +kernel]; simpa only [show BB144Search.ones (74939897799446626304 : BitVec 72) = 4 from by decide +kernel] using BB144KernelSearch.anchor72_2)
    have hh := BB144Chunk.pair_chunk 72 21 (by decide +kernel) hc v
      (by simpa only [show eqb (72 : Fin 144) = (Sum.inr (0, 0)) from by decide +kernel] using ha)
      (by simpa only [show eqb (21 : Fin 144) = (Sum.inl (3, 3)) from by decide +kernel] using h0) hw hv
    simpa only [polyA,polyB,show eqb (72 : Fin 144) = (Sum.inr (0, 0)) from by decide +kernel] using hh
  · have hc := BB144FastGrow.sound xmask xrem xneighbors xupdate xupdate_spec
      8 [81,72] (xmask 81 ^^^ xmask 72)
      (by rw [show (xmask 81 ^^^ xmask 72) = (665235708158150705216 : BitVec 72) from by decide +kernel]; simpa only [show BB144Search.ones (665235708158150705216 : BitVec 72) = 4 from by decide +kernel] using BB144KernelSearch.anchor72_4)
    have hh := BB144Chunk.pair_chunk 72 81 (by decide +kernel) hc v
      (by simpa only [show eqb (72 : Fin 144) = (Sum.inr (0, 0)) from by decide +kernel] using ha)
      (by simpa only [show eqb (81 : Fin 144) = (Sum.inr (1, 3)) from by decide +kernel] using h1) hw hv
    simpa only [polyA,polyB,show eqb (72 : Fin 144) = (Sum.inr (0, 0)) from by decide +kernel] using hh
end BB144Split_right_middle

theorem solution (v : BBCode.Qubit 12 6 → ZMod 2)
    (hv : BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (3, 3)) ≠ 0 ∨ v (Sum.inr (1, 3)) ≠ 0) :
    ∃ u : BBCode.Qubit 12 6 → ZMod 2,
      BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)}) ∧
      u (Sum.inr (0, 0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := BB144Split_right_middle.bound v hv hw ha hb
#print axioms solution
