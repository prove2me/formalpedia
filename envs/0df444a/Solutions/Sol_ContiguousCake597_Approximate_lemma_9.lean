-- Prove2me | solution 1 for ContiguousCake597.Approximate.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T17:05:31.093176+00:00
-- url     : https://prove2.me/submissions/05d20b34-f2be-48bf-9ef9-588eef57717f

import Definitions.Def_ContiguousCake597_Approximate_Analysis

set_option autoImplicit false


section
-- Source module: Solutions/Cake597Blocks.lean

set_option autoImplicit false
open ContiguousCake597.Approximate
namespace Cake597Blocks

variable (G : HZTractability.ThrGraph)

private theorem order_perm (u : ℕ) : (binOrder G u).Perm (List.range' 1 G.n) := by
  unfold binOrder
  split_ifs with h
  · let xs := List.range' 1 G.n
    have hm : u ∈ xs := List.mem_range'_1.mpr (by omega)
    have hd : xs.Nodup := List.nodup_range'
    have hf : xs.filter (· ≠ u) = xs.erase u := by
      rw [hd.erase_eq_filter]
      congr 1
      funext x
      by_cases hx : x = u <;> simp [hx]
    change (xs.filter _ ++ [u]).Perm xs
    rw [hf]
    exact (List.perm_append_comm.trans ((List.perm_cons_erase hm).symm))
  · rfl

private theorem entry_bounds (u v : ℕ) : 0 ≤ entry G u v ∧ entry G u v ≤ 1 := by
  unfold entry
  split_ifs <;> omega

theorem size_pos (u v : ℕ) : 20 ≤ blockSizeZ G u v := by
  unfold blockSizeZ
  have := entry_bounds G u v
  have := entry_bounds G (u-1) v
  omega

private theorem sum_order (u : ℕ) (f : ℕ → ℤ) :
    ((binOrder G u).map f).sum = ∑ v : Fin G.n, f (v.val+1) := by
  rw [((order_perm G u).map f).sum_eq, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp [Nat.add_comm]

private theorem row_sum (hdeg : ∀ v, G.indeg v ≤ 2) (u : ℕ) :
    (∑ v : Fin G.n, entry G u (v.val+1)) ≤ 2 := by
  by_cases hu : 0 < u ∧ u ≤ G.n
  · let i : Fin G.n := ⟨u-1, by omega⟩
    have he (v : Fin G.n) : entry G u (v.val+1) = if G.adj v i then 1 else 0 := by
      simp [entry, hu, Nat.lt_iff_add_one_le.mp v.isLt, i]
    simp_rw [he]
    rw [Finset.sum_boole]
    exact_mod_cast hdeg i
  · simp [entry, hu]

theorem bin_capacity (hdeg : ∀ v, G.indeg v ≤ 2) (u : ℕ) :
    ((binOrder G u).map (blockSizeZ G u)).sum ≤ (R G : ℤ)-8 := by
  rw [sum_order]
  simp only [blockSizeZ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, R, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hp : 0 ≤ ∑ v : Fin G.n, entry G (u-1) (v.val+1) :=
    Finset.sum_nonneg fun v _ => (entry_bounds G _ _).1
  linarith [row_sum G hdeg u]

private theorem drop_sum_mono {α : Type} (xs : List α) (f : α → ℤ)
    (hf : ∀ x, 0 ≤ f x) {i j : ℕ} (h : i ≤ j) :
    ((xs.drop j).map f).sum ≤ ((xs.drop i).map f).sum := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← List.drop_drop]
  generalize xs.drop i = ys
  have he := congrArg (fun ys : List α => (ys.map f).sum) (List.take_append_drop k ys)
  simp only [List.map_append, List.sum_append] at he
  have hp : 0 ≤ ((ys.take k).map f).sum := List.sum_nonneg fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact hf a
  omega

private theorem in_order (u : ℕ) (v : Fin G.n) : v.val+1 ∈ binOrder G u :=
  (order_perm G u).mem_iff.mpr (List.mem_range'_1.mpr (by omega))

private abbrev tail (u k : ℕ) := (((binOrder G u).drop k).map (blockSizeZ G u)).sum

private theorem tail_pos (u k : ℕ) : 0 ≤ tail G u k := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  linarith [size_pos G u v]

private theorem tail_le (u : ℕ) {i j : ℕ} (h : i ≤ j) : tail G u j ≤ tail G u i :=
  drop_sum_mono _ _ (fun x => by linarith [size_pos G u x]) h

private theorem tail_step (u : ℕ) (v : Fin G.n) :
    let i := (binOrder G u).idxOf (v.val+1)
    tail G u i = blockSizeZ G u (v.val+1) + tail G u (i+1) := by
  dsimp only
  have hm := List.idxOf_lt_length_iff.mpr (in_order G u v)
  unfold tail
  rw [List.drop_eq_getElem_cons hm, List.getElem_idxOf hm]
  rfl

private theorem block_interval (hdeg : ∀ v, G.indeg v ≤ 2) {u j : ℕ} (hu : 1 ≤ u)
    (v : Fin G.n) (hj : j ∈ block G u (v.val+1)) :
    let i := (binOrder G u).idxOf (v.val+1)
    (u*R G : ℕ) - tail G u i < (j : ℤ) ∧
      (j : ℤ) ≤ (u*R G : ℕ) - tail G u (i+1) := by
  let i := (binOrder G u).idxOf (v.val+1)
  have hcap : tail G u i ≤ (R G : ℤ)-8 :=
    (tail_le G u (Nat.zero_le i)).trans (by simpa [tail] using bin_capacity G hdeg u)
  have hb : R G ≤ u * R G := by simpa using Nat.mul_le_mul_right (R G) hu
  have hb' : (R G : ℤ) ≤ (u*R G : ℕ) := by exact_mod_cast hb
  have hstep := tail_step G u v
  change tail G u i = blockSizeZ G u (v.val+1) + tail G u (i+1) at hstep
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
  obtain ⟨b, hbmem, hbcast⟩ := List.mem_flatMap.mp hk
  have hkB := List.mem_range.mp hbmem
  have hbk : k = (b : ℤ) := by simpa using hbcast
  subst k
  have hp := size_pos G u (v.val+1)
  have hsize : (b : ℤ) < blockSizeZ G u (v.val+1) := (Int.lt_toNat).mp hkB
  change _ < (Int.toNat ((u*R G : ℕ) - tail G u (i+1) - blockSizeZ G u (v.val+1) + 1 + (b : ℤ)) : ℤ) ∧ _
  rw [Int.toNat_of_nonneg (by omega)]
  change (u*R G : ℕ) - tail G u i < _ ∧ _ ≤ (u*R G : ℕ) - tail G u (i+1)
  omega

private theorem bin_bounds (hdeg : ∀ v, G.indeg v ≤ 2) {u j : ℕ} (hu : 1 ≤ u)
    (v : Fin G.n) (hj : j ∈ block G u (v.val+1)) :
    (u-1)*R G+8 < j ∧ j ≤ u*R G := by
  let i := (binOrder G u).idxOf (v.val+1)
  have h := block_interval G hdeg hu v hj
  have hcap : tail G u i ≤ (R G : ℤ)-8 :=
    (tail_le G u (Nat.zero_le i)).trans (by simpa [tail] using bin_capacity G hdeg u)
  have he : (u-1)*R G + R G = u*R G := by rw [← Nat.succ_mul]; congr 1; omega
  have hp := tail_pos G u (i+1)
  change (u*R G : ℕ) - tail G u i < (j : ℤ) ∧ (j : ℤ) ≤ (u*R G : ℕ) - tail G u (i+1) at h
  omega

private theorem common_bin (hdeg : ∀ v, G.indeg v ≤ 2) {u u' j : ℕ}
    (hu : 1 ≤ u) (hu' : 1 ≤ u') (v w : Fin G.n) (hj : j ∈ block G u (v.val+1))
    (hj' : j ∈ block G u' (w.val+1)) : u = u' := by
  have h := bin_bounds G hdeg hu v hj
  have h' := bin_bounds G hdeg hu' w hj'
  rcases lt_trichotomy u u' with hlt | he | hgt
  · have := Nat.mul_le_mul_right (R G) (show u ≤ u'-1 by omega)
    omega
  · exact he
  · have := Nat.mul_le_mul_right (R G) (show u' ≤ u-1 by omega)
    omega

private theorem S_witness {v : Fin G.n} {j : ℕ} (hj : j ∈ S G v) :
    ∃ u, (1 ≤ u ∧ u ≤ G.n+1) ∧ j ∈ block G u (v.val+1) := by
  simpa only [S, List.mem_toFinset, setList, List.mem_mergeSort, List.mem_flatMap,
    List.mem_range'_1, Nat.add_comm 1 (G.n+1), Nat.lt_succ_iff] using hj

theorem disjoint (hdeg : ∀ v, G.indeg v ≤ 2) (v w : Fin G.n) (hne : v ≠ w) :
    Disjoint (S G v) (S G w) := by
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨u, hu, h⟩ := S_witness G hj
  obtain ⟨u', hu', h'⟩ := S_witness G hj'
  obtain rfl := common_bin G hdeg hu.1 hu'.1 v w h h'
  let i := (binOrder G u).idxOf (v.val+1)
  let k := (binOrder G u).idxOf (w.val+1)
  have hi := List.idxOf_lt_length_iff.mpr (in_order G u v)
  have hk := List.idxOf_lt_length_iff.mpr (in_order G u w)
  have hne' : i ≠ k := by
    intro he
    have he' : (binOrder G u)[i]'hi = (binOrder G u)[k]'hk := by simp [he]
    dsimp [i,k] at he'
    rw [List.getElem_idxOf hi, List.getElem_idxOf hk] at he'
    exact hne (Fin.ext (by omega))
  have a := block_interval G hdeg hu.1 v h
  have b := block_interval G hdeg hu'.1 w h'
  change _ - tail G u i < _ ∧ _ ≤ _ - tail G u (i+1) at a
  change _ - tail G u k < _ ∧ _ ≤ _ - tail G u (k+1) at b
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have := tail_le G u (show i+1 ≤ k by omega)
    omega
  · have := tail_le G u (show k+1 ≤ i by omega)
    omega

theorem S_range (hdeg : ∀ v, G.indeg v ≤ 2) {v : Fin G.n} {j : ℕ} (hj : j ∈ S G v) :
    1 ≤ j ∧ j ≤ N G := by
  obtain ⟨u, hu, hm⟩ := S_witness G hj
  have h := bin_bounds G hdeg hu.1 v hm
  have hb := Nat.mul_le_mul_right (R G) hu.2
  have hN : (G.n+1)*R G = N G := by unfold R N; ring
  omega

theorem following_outside (hdeg : ∀ v, G.indeg v ≤ 2) (v w : Fin G.n) :
    a G v+1 ∉ S G w := by
  intro hj
  obtain ⟨u, hu, hm⟩ := S_witness G hj
  have h := bin_bounds G hdeg hu.1 w hm
  unfold a at h
  by_cases hc : u ≤ v.val+1
  · have := Nat.mul_le_mul_right (R G) hc
    omega
  · have := Nat.mul_le_mul_right (R G) (show v.val+1 ≤ u-1 by omega)
    omega

private theorem block_as_range (hdeg : ∀ v, G.indeg v ≤ 2) {u : ℕ} (hu : 1 ≤ u)
    (v : Fin G.n) :
    let i := (binOrder G u).idxOf (v.val+1)
    block G u (v.val+1) = List.range' (((u*R G : ℕ) - tail G u i + 1 : ℤ).toNat)
      (blockSizeZ G u (v.val+1)).toNat := by
  let i := (binOrder G u).idxOf (v.val+1)
  have hcap : tail G u i ≤ (R G : ℤ)-8 :=
    (tail_le G u (Nat.zero_le i)).trans (by simpa [tail] using bin_capacity G hdeg u)
  have hb : R G ≤ u * R G := by simpa using Nat.mul_le_mul_right (R G) hu
  have hb' : (R G : ℤ) ≤ (u*R G : ℕ) := by exact_mod_cast hb
  have hstep := tail_step G u v
  change tail G u i = blockSizeZ G u (v.val+1) + tail G u (i+1) at hstep
  change (((List.range _).flatMap (fun k : ℕ => [(k : ℤ)])).map
    (fun k : ℤ => ((u*R G : ℕ) - tail G u (i+1) - blockSizeZ G u (v.val+1) + 1 + k).toNat)) =
    List.range' (((u*R G : ℕ) - tail G u i + 1 : ℤ).toNat) _
  simp only [← List.map_eq_flatMap, List.map_map]
  rw [List.range'_eq_map_range]
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp_apply]
  omega

theorem setList_nodup (hdeg : ∀ v, G.indeg v ≤ 2) (v : Fin G.n) : (setList G v).Nodup := by
  unfold setList
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  apply List.nodup_flatMap.mpr
  constructor
  · intro u hu
    rw [block_as_range G hdeg (List.mem_range'_1.mp hu).1 v]
    exact List.nodup_range'
  · have hnd : (List.range' 1 (G.n+1)).Nodup := List.nodup_range'
    apply hnd.imp_of_mem
    intro a b ha hb hab j hja hjb
    exact hab (common_bin G hdeg (List.mem_range'_1.mp ha).1 (List.mem_range'_1.mp hb).1 v v hja hjb)

private theorem own_tail (v : Fin G.n) :
    tail G (v.val+1) ((binOrder G (v.val+1)).idxOf (v.val+1) + 1) = 0 := by
  let u := v.val+1
  let xs := (List.range' 1 G.n).filter (· ≠ u)
  have ho : binOrder G u = xs ++ [u] := if_pos (by dsimp [u]; omega)
  have hm : u ∉ xs := by simp [xs]
  change (((binOrder G u).drop ((binOrder G u).idxOf u + 1)).map (blockSizeZ G u)).sum = 0
  rw [ho, List.idxOf_append, if_neg hm]
  simp

theorem own_members (hdeg : ∀ v, G.indeg v ≤ 2) (v : Fin G.n) :
    a G v ∈ S G v ∧ a G v-1 ∈ S G v := by
  let u := v.val+1
  let i := (binOrder G u).idxOf u
  have hu : 1 ≤ u := by omega
  have hstep := tail_step G u v
  have ht := own_tail G v
  change tail G u (i+1) = 0 at ht
  change tail G u i = blockSizeZ G u u + tail G u (i+1) at hstep
  have hp := size_pos G u u
  have hcap : tail G u i ≤ (R G : ℤ)-8 :=
    (tail_le G u (Nat.zero_le i)).trans (by simpa [tail] using bin_capacity G hdeg u)
  have hb : R G ≤ u * R G := by simpa using Nat.mul_le_mul_right (R G) hu
  have hb' : (R G : ℤ) ≤ (u*R G : ℕ) := by exact_mod_cast hb
  have memb (j : ℕ) (hlo : u*R G-1 ≤ j) (hhi : j ≤ u*R G) : j ∈ S G v := by
    simp only [S, List.mem_toFinset, setList, List.mem_mergeSort, List.mem_flatMap]
    refine ⟨u, List.mem_range'_1.mpr (by dsimp [u]; omega), ?_⟩
    rw [block_as_range G hdeg hu v, List.mem_range'_1]
    change ((u*R G : ℕ) - tail G u i + 1 : ℤ).toNat ≤ j ∧ j < ((u*R G : ℕ) - tail G u i + 1 : ℤ).toNat + (blockSizeZ G u u).toNat
    omega
  exact ⟨memb _ (by dsimp [u,a]; omega) (by rfl),memb _ (by rfl) (by dsimp [u,a]; omega)⟩

theorem one_outside (hdeg : ∀ v, G.indeg v ≤ 2) (v : Fin G.n) : 1 ∉ S G v := by
  intro hj
  obtain ⟨u, hu, hm⟩ := S_witness G hj
  have h := bin_bounds G hdeg hu.1 v hm
  omega

private def prefixList (v : Fin G.n) (k : ℕ) :=
  (List.range' 1 k).flatMap (fun u => block G u (v.val+1))

private theorem length_prefix (hdeg : ∀ w, G.indeg w ≤ 2) (v : Fin G.n) (k : ℕ) :
    ((prefixList G v k).length : ℤ) = 32*k + 12*entry G k (v.val+1) := by
  induction k with
  | zero => simp [prefixList,entry]
  | succ k ih =>
    unfold prefixList at ih ⊢
    rw [List.range'_1_concat, List.flatMap_append, List.length_append, Nat.cast_add, ih]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [block_as_range G hdeg (by omega) v,List.length_range',Int.toNat_of_nonneg (by linarith [size_pos G (1+k) (v.val+1)])]
    simp only [blockSizeZ, Nat.add_sub_cancel_left, Nat.add_comm 1 k, Nat.add_one_sub_one, Nat.cast_succ]
    ring

private theorem prefix_filter (hdeg : ∀ w, G.indeg w ≤ 2) (v : Fin G.n) (k t : ℕ) :
    (prefixList G v k).filter (fun j => j ≤ t*R G) = prefixList G v (min k t) := by
  induction k with
  | zero => simp [prefixList]
  | succ k ih =>
    have he (a : ℕ) : prefixList G v (a+1) = prefixList G v a ++ block G (a+1) (v.val+1) := by
      simp [prefixList,List.range'_1_concat,List.flatMap_append,Nat.add_comm]
    rw [he,List.filter_append,ih]
    by_cases hc : k+1 ≤ t
    · rw [min_eq_left hc,he,min_eq_left (by omega : k ≤ t)]
      have hb : (block G (k+1) (v.val+1)).filter (fun j => j ≤ t*R G) = _ :=
        List.filter_eq_self.mpr (by
          intro j hj
          simp only [decide_eq_true_eq]
          exact (bin_bounds G hdeg (by omega) v hj).2.trans (Nat.mul_le_mul_right (R G) hc))
      rw [hb]
    · rw [min_eq_right (by omega : t ≤ k+1),min_eq_right (by omega : t ≤ k)]
      have hb : (block G (k+1) (v.val+1)).filter (fun j => j ≤ t*R G) = [] :=
        List.filter_eq_nil_iff.mpr (by
          intro j hj
          have hh := (bin_bounds G hdeg (by omega) v hj).1
          simp only [Nat.add_one_sub_one] at hh
          have ht := Nat.mul_le_mul_right (R G) (show t ≤ k by omega)
          simp only [decide_eq_true_eq]
          omega)
      rw [hb,List.append_nil]

theorem S_card (hdeg : ∀ w, G.indeg w ≤ 2) (v : Fin G.n) : (S G v).card = R G := by
  rw [S,List.toFinset_card_of_nodup (setList_nodup G hdeg v), setList, List.length_mergeSort]
  have h := length_prefix G hdeg v (G.n+1)
  have hz : entry G (G.n+1) (v.val+1) = 0 := by simp [entry]
  rw [hz, mul_zero,add_zero] at h
  change (prefixList G v (G.n+1)).length = 32*(G.n+1)
  exact_mod_cast h

theorem S_prefix_count (hdeg : ∀ w, G.indeg w ≤ 2) (u v : Fin G.n) :
    ((S G v).filter (fun j => j ≤ a G u)).card =
      32*(u.val+1)+12*(entry G (u.val+1) (v.val+1)).toNat := by
  rw [S,List.filter_toFinset,List.toFinset_card_of_nodup ((setList_nodup G hdeg v).filter _)]
  let P := fun j : ℕ => decide (j ≤ a G u)
  have he : ((setList G v).filter P).Perm ((prefixList G v (G.n+1)).filter P) :=
    (List.mergeSort_perm _ _).filter P
  change ((setList G v).filter P).length = _
  rw [he.length_eq]
  change ((prefixList G v (G.n+1)).filter (fun j => decide (j ≤ (u.val+1)*R G))).length = _
  rw [prefix_filter G hdeg v (G.n+1) (u.val+1), min_eq_right (by omega : u.val+1 ≤ G.n+1)]
  have h := length_prefix G hdeg v (u.val+1)
  have hp := (entry_bounds G (u.val+1) (v.val+1)).1
  omega

end Cake597Blocks
end


section
-- Source module: Solutions/Cake597PriceRange.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.PriceRangeProof

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem positive_variation_bound (p : α → α) (sigma : Equiv.Perm α)
    (e : ℝ) (q : α → ℝ)
    (hq : ∀ i, max (q i) (q (p i)) - e ≤ q (sigma i)) :
    (∑ i, max (q (p i) - q i) 0) ≤ (Fintype.card α : ℝ) * e := by
  have hlocal (i : α) : max (q (p i) - q i) 0 ≤ q (sigma i) - q i + e := by
    apply max_le
    · have hi := le_max_right (q i) (q (p i))
      linarith [hq i]
    · have hi := le_max_left (q i) (q (p i))
      linarith [hq i]
  calc
    (∑ i, max (q (p i) - q i) 0) ≤ ∑ i, (q (sigma i) - q i + e) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (Fintype.card α : ℝ) * e := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]
      simp

theorem variation_controls_reachable (p : α → α) (q : α → ℝ) (i j : α)
    (hreach : ∃ k : ℕ, (p^[k]) i = j) :
    q j - q i ≤ ∑ x, max (q (p x) - q x) 0 := by
  classical
  let k := Nat.find hreach
  have hk : (p^[k]) i = j := Nat.find_spec hreach
  have hminimal {t : ℕ} (ht : (p^[t]) i = j) : k ≤ t := Nat.find_min' hreach ht
  have hdistinct (a b : ℕ) (hb : b < k) (hab : a < b) :
      (p^[a]) i ≠ (p^[b]) i := by
    intro heq
    have htarget : (p^[k - b + a]) i = j := by
      rw [Function.iterate_add_apply, heq, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hb.le]
      exact hk
    have := hminimal htarget
    omega
  have hinj : Set.InjOn (fun t => (p^[t]) i) (↑(Finset.range k) : Set ℕ) := by
    intro a ha b hb heq
    have hak := Finset.mem_range.mp ha
    have hbk := Finset.mem_range.mp hb
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hdistinct a b hbk hab heq).elim
    · exact hab
    · exact (hdistinct b a hak hab heq.symm).elim
  calc
    q j - q i = ∑ t ∈ Finset.range k,
        (q ((p^[t + 1]) i) - q ((p^[t]) i)) := by
      rw [Finset.sum_range_sub (fun t => q ((p^[t]) i)) k, hk]
      rfl
    _ ≤ ∑ t ∈ Finset.range k, max (q (p ((p^[t]) i)) - q ((p^[t]) i)) 0 := by
      apply Finset.sum_le_sum
      intro t _
      rw [Function.iterate_succ_apply']
      exact le_max_left _ _
    _ = ∑ x ∈ (Finset.range k).image (fun t => (p^[t]) i),
        max (q (p x) - q x) 0 :=
      (Finset.sum_image (f := fun x => max (q (p x) - q x) 0) hinj).symm
    _ ≤ ∑ x, max (q (p x) - q x) 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro x _ _
      exact le_max_right _ _

end ContiguousCake597.Approximate.PriceRangeProof

namespace ContiguousCake597.Approximate

theorem lemma_7_proof (n : ℕ) (hn : 1 ≤ n) (p sigma : Equiv.Perm (Fin n))
    (hp : SingleCycle p) (e : ℝ) (he : 0 ≤ e) (q : Fin n → ℝ)
    (hq : ∀ i, max (q i) (q (p i)) - e ≤ q (sigma i)) :
    ∀ i j : Fin n, q j - q i ≤ (n : ℝ) * e := by
  intro i j
  exact (PriceRangeProof.variation_controls_reachable p q i j (hp i j)).trans
    (by simpa using PriceRangeProof.positive_variation_bound p sigma e q hq)

end ContiguousCake597.Approximate

end


section
-- Source module: Solutions/Cake597Localization.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.LocalizationProof

theorem overlap_nonneg (x y c d : ℝ) : 0 ≤ overlap x y c d := le_max_left _ _

theorem overlap_le_interval (x y c d : ℝ) (hcd : c ≤ d) :
    overlap x y c d ≤ d - c := by
  apply max_le (sub_nonneg.mpr hcd)
  exact sub_le_sub (min_le_right _ _) (le_max_right _ _)

theorem R_ge (G : HZTractability.ThrGraph) : 32 ≤ R G := by
  unfold R
  omega

theorem a_separated (G : HZTractability.ThrGraph) (u v : Fin G.n) (huv : u ≠ v) :
    a G u + 1 < a G v ∨ a G v + 1 < a G u := by
  have hR := R_ge G
  have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := Nat.mul_le_mul_right (R G) (show u.val + 1 + 1 ≤ v.val + 1 by omega)
    have hgap : a G u + R G ≤ a G v := by
      simpa only [a, Nat.add_mul, Nat.one_mul] using hmul
    exact Or.inl (by omega)
  · have hmul := Nat.mul_le_mul_right (R G) (show v.val + 1 + 1 ≤ u.val + 1 by omega)
    have hgap : a G v + R G ≤ a G u := by
      simpa only [a, Nat.add_mul, Nat.one_mul] using hmul
    exact Or.inr (by omega)

theorem boundary_unique (G : HZTractability.ThrGraph) (i : Fin (N G))
    (u v : Fin G.n)
    (hu : i.val + 1 = a G u ∨ i.val + 1 = a G u + 1)
    (hv : i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) : u = v := by
  by_contra hne
  rcases a_separated G u v hne with h | h <;> rcases hu with hu | hu <;>
    rcases hv with hv | hv <;> omega

theorem sum_filter_map {α : Type*} (xs : List α) (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    ((xs.filter (fun x => decide (P x))).map f).sum =
      (xs.map (fun x => if P x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : P x <;> simp [hx, ih]

theorem boundary_sum_le (G : HZTractability.ThrGraph) (i : Fin (N G)) (x y : ℝ) :
    (((List.finRange G.n).filter
      (fun v => i.val + 1 = a G v ∨ i.val + 1 = a G v + 1)).map
      (fun v => overlap x y ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ))).sum ≤ 1 := by
  rw [sum_filter_map, ← List.ofFn_eq_map, List.sum_ofFn]
  have hcount : (∑ v : Fin G.n,
      if i.val + 1 = a G v ∨ i.val + 1 = a G v + 1 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hex : ∃ v : Fin G.n, i.val + 1 = a G v ∨ i.val + 1 = a G v + 1
    · obtain ⟨v, hv⟩ := hex
      have hp (u : Fin G.n) :
          (i.val + 1 = a G u ∨ i.val + 1 = a G u + 1) ↔ u = v := by
        exact ⟨fun hu => boundary_unique G i u v hu hv, fun h => h ▸ hv⟩
      simp only [hp]
      simp
    · have hp (v : Fin G.n) : ¬ (i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) :=
        fun hv => hex ⟨v, hv⟩
      rw [Finset.sum_eq_zero (fun v _ => if_neg (hp v))]
      norm_num
  apply le_trans (Finset.sum_le_sum ?_) hcount
  intro v _
  split_ifs
  · have hlen : ((boundary G v).2 : ℝ) - ((boundary G v).1 : ℝ) = 1 := by
      simp only [boundary]
      push_cast
      ring
    have hvalid : ((boundary G v).1 : ℝ) ≤ ((boundary G v).2 : ℝ) := by linarith
    simpa only [hlen] using overlap_le_interval x y _ _ hvalid
  · exact le_rfl

theorem centered_overlap_le (G : HZTractability.ThrGraph) (j : ℕ) (r : ℚ)
    (hr : 0 ≤ r) (x y : ℝ) :
    overlap x y ((centered G j r).1 : ℝ) ((centered G j r).2 : ℝ) ≤ (r : ℝ) := by
  have hlen : ((centered G j r).2 : ℝ) - ((centered G j r).1 : ℝ) = r := by
    simp only [centered]
    push_cast
    ring
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hvalid : ((centered G j r).1 : ℝ) ≤ ((centered G j r).2 : ℝ) := by linarith
  simpa only [hlen] using overlap_le_interval x y _ _ hvalid

theorem ownBonus_bounds (G : HZTractability.ThrGraph) (i : Fin (N G)) :
    0 ≤ ownBonus G i ∧ ownBonus G i ≤ 3 := by
  unfold ownBonus
  split_ifs <;> norm_num

theorem nextBonus_bounds (G : HZTractability.ThrGraph) (i : Fin (N G)) :
    0 ≤ nextBonus G i ∧ nextBonus G i ≤ 3 := by
  unfold nextBonus
  split_ifs <;> norm_num

theorem bonus_bound (G : HZTractability.ThrGraph) (i : Fin (N G)) (x y : ℝ) :
    0 ≤ U G i x y - (y - x) ∧ U G i x y - (y - x) ≤ 6 := by
  have hnonneg : 0 ≤ ((bonuses G i).map
      (fun ab => overlap x y (ab.1 : ℝ) (ab.2 : ℝ))).sum := by
    apply List.sum_nonneg
    intro r hr
    obtain ⟨ab, _, rfl⟩ := List.mem_map.mp hr
    exact overlap_nonneg _ _ _ _
  refine ⟨by simpa only [U, add_sub_cancel_left] using hnonneg, ?_⟩
  have hown := centered_overlap_le G (i.val + 1) (ownBonus G i) (ownBonus_bounds G i).1 x y
  have hnext := centered_overlap_le G ((pi G i).val + 1) (nextBonus G i)
    (nextBonus_bounds G i).1 x y
  have hboundary := boundary_sum_le G i x y
  simp only [U, bonuses, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def] at *
  by_cases hfollowing : ∃ v : Fin G.n, i.val + 1 = a G v + 1
  · have hownval : ownBonus G i = 2 := by rw [ownBonus, if_pos hfollowing]
    have hnextval : (nextBonus G i : ℝ) ≤ 3 := by exact_mod_cast (nextBonus_bounds G i).2
    have howncast : (ownBonus G i : ℝ) = 2 := by exact_mod_cast hownval
    linarith only [hown, howncast, hnext, hnextval, hboundary]
  · by_cases hspecial : ∃ v : Fin G.n, i.val + 1 = a G v
    · have hownval : ownBonus G i = 5/2 := by
        rw [ownBonus, if_neg hfollowing, if_pos hspecial]
      have hnextval : nextBonus G i = 5/2 := by rw [nextBonus, if_pos hspecial]
      have howncast : (ownBonus G i : ℝ) = 5/2 := by rw [hownval]; norm_num
      have hnextcast : (nextBonus G i : ℝ) = 5/2 := by rw [hnextval]; norm_num
      linarith only [hown, howncast, hnext, hnextcast, hboundary]
    · have hp (v : Fin G.n) : ¬ (i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) := by
        rintro (h | h)
        · exact hspecial ⟨v, h⟩
        · exact hfollowing ⟨v, h⟩
      have hboundary0 : (List.finRange G.n).filter
          (fun v => i.val + 1 = a G v ∨ i.val + 1 = a G v + 1) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro v _
        simpa using hp v
      rw [hboundary0]
      simp only [List.map_nil, List.sum_nil, add_zero]
      have hownval : (ownBonus G i : ℝ) ≤ 3 := by exact_mod_cast (ownBonus_bounds G i).2
      have hnextval : (nextBonus G i : ℝ) ≤ 3 := by exact_mod_cast (nextBonus_bounds G i).2
      linarith

theorem N_pos (G : HZTractability.ThrGraph) : 0 < N G := by
  unfold N
  positivity

theorem eta_lt_one (G : HZTractability.ThrGraph) : eta G < 1 := by
  have hN : (1 : ℝ) ≤ N G := by exact_mod_cast N_pos G
  unfold eta
  apply (div_lt_one (by positivity : 0 < 100 * (N G : ℝ)^2)).mpr
  nlinarith

theorem sum_lengths {n : ℕ} (T : Allocation ℝ n) :
    ∑ j, T.length j = T.cuts (Fin.last n) - T.cuts 0 := by
  unfold Allocation.length
  rw [Finset.sum_sub_distrib]
  have hleft := Fin.sum_univ_succ T.cuts
  have hright := Fin.sum_univ_castSucc T.cuts
  linarith

theorem piece_length_bounds (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (j : Fin (N G)) :
    (B G : ℝ) - 7 < T.length j ∧ T.length j < (B G : ℝ) + 7 := by
  have hN : 0 < (N G : ℝ) := by exact_mod_cast N_pos G
  have hsum : ∑ r, T.length r = (N G : ℝ) * (B G : ℝ) := by
    have hend : T.cuts (Fin.last (N G)) = (L G : ℝ) := hT.1.2.1
    rw [sum_lengths, hT.1.1, hend]
    simp only [L, Nat.cast_mul, sub_zero]
  have hpair (r s : Fin (N G)) : T.length s ≤ T.length r + (6 + eta G) := by
    let i := T.assign.symm r
    have hi : T.assign i = r := T.assign.apply_symm_apply r
    have henv := hT.2 i s
    rw [hi] at henv
    have hbr := bonus_bound G i (T.cuts r.castSucc) (T.cuts r.succ)
    have hbs := bonus_bound G i (T.cuts s.castSucc) (T.cuts s.succ)
    unfold Allocation.length
    linarith
  have hu : (N G : ℝ) * T.length j ≤
      (N G : ℝ) * B G + (N G : ℝ) * (6 + eta G) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hpair r j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_add_distrib, hsum] using h
  have hl : (N G : ℝ) * B G ≤
      (N G : ℝ) * T.length j + (N G : ℝ) * (6 + eta G) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hpair j r)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_add_distrib, hsum, mul_add] using h
  have he := eta_lt_one G
  have hupper : T.length j ≤ (B G : ℝ) + (6 + eta G) := by nlinarith
  have hlower : (B G : ℝ) - (6 + eta G) ≤ T.length j := by nlinarith
  constructor <;> linarith

theorem cut_localization (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    ∀ j : Fin (N G + 1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G := by
  have hstep (j : Fin (N G)) : |T.length j - (B G : ℝ)| < 7 := by
    obtain ⟨hl, hu⟩ := piece_length_bounds G T hT j
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hprefix : ∀ j : Fin (N G + 1),
      |T.cuts j - (j.val : ℝ) * B G| ≤ 7 * j.val ∧
      (0 < j.val → |T.cuts j - (j.val : ℝ) * B G| < 7 * j.val) := by
    apply Fin.induction
    · simp [hT.1.1]
    · intro j ih
      have heq : T.cuts j.succ - (j.succ.val : ℝ) * B G =
          (T.cuts j.castSucc - (j.val : ℝ) * B G) + (T.length j - B G) := by
        simp only [Allocation.length, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        ring
      have hlt : |T.cuts j.succ - (j.succ.val : ℝ) * B G| < 7 * j.succ.val := by
        rw [heq]
        calc
          _ ≤ |T.cuts j.castSucc - (j.val : ℝ) * B G| + |T.length j - B G| :=
            abs_add_le _ _
          _ < 7 * (j.val : ℝ) + 7 := add_lt_add_of_le_of_lt ih.1 (hstep j)
          _ = 7 * (j.succ.val : ℝ) := by
            simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
            ring
      exact ⟨hlt.le, fun _ => hlt⟩
  intro j
  by_cases hj : j.val = 0
  · have hj0 : j = 0 := Fin.ext hj
    rw [hj0, hT.1.1]
    have hN : (0 : ℝ) < N G := by exact_mod_cast N_pos G
    simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero, abs_zero] using
      (mul_pos (by norm_num : (0 : ℝ) < 7) hN)
  · exact (hprefix j).2 (Nat.pos_of_ne_zero hj) |>.trans_le
      (mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.le_of_lt_succ j.isLt : (j.val : ℝ) ≤ N G)
        (by norm_num))

theorem core_localization (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcuts : ∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) :
    ∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅ := by
  have hN : 0 < (N G : ℝ) := by exact_mod_cast N_pos G
  have hB : 0 ≤ (B G : ℝ) := Nat.cast_nonneg _
  intro j
  have hjleft := abs_lt.mp (hcuts j.castSucc)
  have hjright := abs_lt.mp (hcuts j.succ)
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hjleft hjright
  constructor
  · intro x hx
    obtain ⟨hxl, hxr⟩ := hx
    change T.cuts j.castSucc ≤ x ∧ x ≤ T.cuts j.succ
    change (j.val : ℝ) * B G + 10 * N G ≤ x at hxl
    change x ≤ ((j.val + 1 : ℕ) : ℝ) * B G - 10 * N G at hxr
    push_cast at hxr
    constructor <;> linarith
  · intro k hkj
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨⟨hxjl, hxjr⟩, hxkl, hxkr⟩ := hx
    change T.cuts j.castSucc ≤ x at hxjl
    change x ≤ T.cuts j.succ at hxjr
    change (k.val : ℝ) * B G + 10 * N G ≤ x at hxkl
    change x ≤ ((k.val + 1 : ℕ) : ℝ) * B G - 10 * N G at hxkr
    push_cast at hxkr
    have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hkidx : (k.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
      have hmul := mul_le_mul_of_nonneg_right hkidx hB
      linarith
    · have hkidx : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast hgt
      have hmul := mul_le_mul_of_nonneg_right hkidx hB
      linarith

theorem overlap_unit (x b c : ℝ) (hx : x ≤ c) :
    overlap x b c (c+1) = clip (b-c) := by
  unfold overlap clip
  rw [max_eq_right hx]
  by_cases hbc : b ≤ c
  · rw [min_eq_left (by linarith : b ≤ c+1), max_eq_left (by linarith : b-c ≤ 0),
      min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  · by_cases hcb : c + 1 ≤ b
    · rw [min_eq_right hcb]
      have hdiff : c+1-c = 1 := by ring
      rw [hdiff, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by linarith : 0 ≤ b-c), min_eq_left (by linarith : 1 ≤ b-c)]
    · rw [min_eq_left (le_of_not_ge hcb), max_eq_right (by linarith : 0 ≤ b-c),
        min_eq_right (by linarith : b-c ≤ 1)]

theorem a_pos (G : HZTractability.ThrGraph) (v : Fin G.n) : 0 < a G v := by
  have hR := R_ge G
  unfold a
  positivity

theorem consecutive_special (G : HZTractability.ThrGraph) (v : Fin G.n) :
    (specialPiece G v).succ = (followingPiece G v).castSucc := by
  apply Fin.ext
  have ha := a_pos G v
  simp only [Fin.val_succ, Fin.val_castSucc, specialPiece, followingPiece]
  omega

theorem boundary_outer_bounds (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcuts : ∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G)
    (v : Fin G.n) :
    T.cuts (specialPiece G v).castSucc ≤ ((boundary G v).1 : ℝ) ∧
      ((boundary G v).2 : ℝ) ≤ T.cuts (followingPiece G v).succ := by
  have hN : (1 : ℝ) ≤ N G := by exact_mod_cast N_pos G
  have hB : (B G : ℝ) = 40 * N G := by simp [B]
  have ha := a_pos G v
  have hspecial : ((specialPiece G v).val : ℝ) = (a G v : ℝ) - 1 := by
    have hnat : (specialPiece G v).val + 1 = a G v := by
      simp only [specialPiece]
      omega
    have hreal : ((specialPiece G v).val : ℝ) + 1 = (a G v : ℝ) := by exact_mod_cast hnat
    linarith
  have hleft := (abs_lt.mp (hcuts (specialPiece G v).castSucc)).2
  have hright := (abs_lt.mp (hcuts (followingPiece G v).succ)).1
  simp only [Fin.val_castSucc, hspecial] at hleft
  have hfollowing : (followingPiece G v).val = a G v := rfl
  simp only [Fin.val_succ, hfollowing, Nat.cast_add, Nat.cast_one] at hright
  simp only [boundary]
  push_cast
  constructor <;> nlinarith only [hleft, hright, hN, hB]

theorem boundary_localization (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcuts : ∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) :
    ∀ v : Fin G.n,
      boundarySet G v ⊆ T.piece (specialPiece G v) ∪ T.piece (followingPiece G v) ∧
      overlap (T.cuts (specialPiece G v).castSucc) (T.cuts (specialPiece G v).succ)
        ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) = z G T v := by
  intro v
  have houter := boundary_outer_bounds G T hcuts v
  constructor
  · intro x hx
    change ((boundary G v).1 : ℝ) ≤ x ∧ x ≤ ((boundary G v).2 : ℝ) at hx
    by_cases hmid : x ≤ T.cuts (specialPiece G v).succ
    · exact Or.inl ⟨houter.1.trans hx.1, hmid⟩
    · apply Or.inr
      constructor
      · rw [← consecutive_special G v]
        exact le_of_not_ge hmid
      · exact hx.2.trans houter.2
  · have hlength : ((boundary G v).2 : ℝ) = ((boundary G v).1 : ℝ) + 1 := by
      simp only [boundary]
      push_cast
      ring
    rw [hlength, overlap_unit _ _ _ houter.1]
    unfold z
    congr 1
    simp only [boundary]
    push_cast
    ring

end ContiguousCake597.Approximate.LocalizationProof

namespace ContiguousCake597.Approximate

theorem lemma_6_proof (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    (∀ j : Fin (N G+1), |T.cuts j - (j.val : ℝ) * B G| < 7 * N G) ∧
    (∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅) ∧
    (∀ v : Fin G.n,
      boundarySet G v ⊆ T.piece (specialPiece G v) ∪ T.piece (followingPiece G v) ∧
      overlap (T.cuts (specialPiece G v).castSucc) (T.cuts (specialPiece G v).succ)
        ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) = z G T v) := by
  have hcuts := LocalizationProof.cut_localization G T hT
  exact ⟨hcuts, LocalizationProof.core_localization G T hcuts,
    LocalizationProof.boundary_localization G T hcuts⟩

end ContiguousCake597.Approximate

end


section
-- Source module: Solutions/Cake597Prices.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.PriceProof

noncomputable def correction (G : HZTractability.ThrGraph) (t : Fin G.n → ℝ)
    (j : Fin (N G)) : ℝ :=
  ∑ v : Fin G.n, if j.val + 1 ∈ S G v then t v else 0

noncomputable def boundaryOwn (G : HZTractability.ThrGraph) (t : Fin G.n → ℝ)
    (i : Fin (N G)) : ℝ :=
  ∑ v : Fin G.n, if i.val + 1 = a G v then t v else
    if i.val + 1 = a G v + 1 then 1 - t v else 0

theorem clip_bounds (r : ℝ) : 0 ≤ clip r ∧ clip r ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem correction_price (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (j : Fin (N G)) : price G T j = T.length j + correction G (z G T) j := rfl

theorem overlap_zero_of_inter_empty (x y c d : ℝ)
    (h : Set.Icc x y ∩ Set.Icc c d = ∅) : overlap x y c d = 0 := by
  rw [Set.Icc_inter_Icc] at h
  have hlt := Set.Icc_eq_empty_iff.mp h
  exact max_eq_left (sub_nonpos.mpr (le_of_not_ge hlt))

theorem overlap_zero_of_before (x y c d : ℝ) (hy : y ≤ c) :
    overlap x y c d = 0 := by
  exact max_eq_left (sub_nonpos.mpr
    ((min_le_left _ _).trans (hy.trans (le_max_right _ _))))

theorem overlap_zero_of_after (x y c d : ℝ) (hx : d ≤ x) :
    overlap x y c d = 0 := by
  exact max_eq_left (sub_nonpos.mpr
    ((min_le_right _ _).trans (hx.trans (le_max_left _ _))))

theorem centered_length (G : HZTractability.ThrGraph) (j : ℕ) (r : ℚ) :
    ((centered G j r).2 : ℝ) - ((centered G j r).1 : ℝ) = r := by
  simp only [centered]
  push_cast
  ring

theorem centered_endpoints_core (G : HZTractability.ThrGraph) (j : Fin (N G))
    (r : ℚ) (hr : 0 ≤ r) (hr3 : r ≤ 3) :
    ((centered G (j.val+1) r).1 : ℝ) ∈ core G j ∧
      ((centered G (j.val+1) r).2 : ℝ) ∈ core G j := by
  have hN : (1 : ℝ) ≤ N G := by exact_mod_cast LocalizationProof.N_pos G
  have hB : (B G : ℝ) = 40 * N G := by simp [B]
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hr3' : (r : ℝ) ≤ 3 := by exact_mod_cast hr3
  simp only [core, Set.mem_Icc, centered]
  push_cast
  constructor <;> constructor <;> nlinarith only [hN, hB, hr', hr3']

theorem centered_overlap (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hcore : ∀ j : Fin (N G), core G j ⊆ T.piece j ∧
      ∀ k : Fin (N G), k ≠ j → T.piece j ∩ core G k = ∅)
    (j k : Fin (N G)) (r : ℚ) (hr : 0 ≤ r) (hr3 : r ≤ 3) :
    overlap (T.cuts j.castSucc) (T.cuts j.succ)
      ((centered G (k.val+1) r).1 : ℝ) ((centered G (k.val+1) r).2 : ℝ) =
        if j = k then (r : ℝ) else 0 := by
  have hend := centered_endpoints_core G k r hr hr3
  by_cases hjk : j = k
  · subst k
    have hc := (hcore j).1 hend.1
    have hd := (hcore j).1 hend.2
    have hlen := centered_length G (j.val+1) r
    have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
    have hcd : ((centered G (j.val+1) r).1 : ℝ) ≤
        ((centered G (j.val+1) r).2 : ℝ) := by linarith
    rw [if_pos rfl]
    unfold overlap
    rw [min_eq_right hd.2, max_eq_right hc.1, hlen, max_eq_right hr']
  · rw [if_neg hjk]
    apply overlap_zero_of_inter_empty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxcore : x ∈ core G k := ⟨hend.1.1.trans hx.2.1, hx.2.2.trans hend.2.2⟩
    have hempty := (hcore j).2 k (Ne.symm hjk)
    exact Set.notMem_empty x (hempty ▸ ⟨hx.1, hxcore⟩)

theorem overlap_unit_right (b y c : ℝ) (hy : c+1 ≤ y) :
    overlap b y c (c+1) = 1 - clip (b-c) := by
  unfold overlap clip
  rw [min_eq_right hy]
  by_cases hbc : b ≤ c
  · rw [max_eq_right hbc, max_eq_left (by linarith : b-c ≤ 0),
      min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  · by_cases hcb : c+1 ≤ b
    · rw [max_eq_left (by linarith : c ≤ b), max_eq_left (by linarith : c+1-b ≤ 0),
        max_eq_right (by linarith : 0 ≤ b-c), min_eq_left (by linarith : 1 ≤ b-c)]
      norm_num
    · rw [max_eq_left (by linarith : c ≤ b),
        max_eq_right (by linarith : 0 ≤ c+1-b),
        max_eq_right (by linarith : 0 ≤ b-c), min_eq_right (by linarith : b-c ≤ 1)]
      ring

theorem boundary_overlap (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (v : Fin G.n) (j : Fin (N G)) :
    overlap (T.cuts j.castSucc) (T.cuts j.succ)
      ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) =
        if j = specialPiece G v then z G T v else
          if j = followingPiece G v then 1-z G T v else 0 := by
  have hcuts := LocalizationProof.cut_localization G T hT
  have houter := LocalizationProof.boundary_outer_bounds G T hcuts v
  by_cases hspecial : j = specialPiece G v
  · subst j
    rw [if_pos rfl]
    exact (LocalizationProof.boundary_localization G T hcuts v).2
  · rw [if_neg hspecial]
    by_cases hfollowing : j = followingPiece G v
    · subst j
      rw [if_pos rfl]
      have hlen : ((boundary G v).2 : ℝ) = ((boundary G v).1 : ℝ)+1 := by
        simp only [boundary]
        push_cast
        ring
      rw [hlen, overlap_unit_right _ _ _ (hlen ▸ houter.2)]
      rw [← LocalizationProof.consecutive_special G v]
      unfold z
      congr 2
      simp only [boundary]
      push_cast
      ring
    · rw [if_neg hfollowing]
      have ha := LocalizationProof.a_pos G v
      have hjsp : j.val ≠ (specialPiece G v).val := fun h => hspecial (Fin.ext h)
      have hjfo : j.val ≠ (followingPiece G v).val := fun h => hfollowing (Fin.ext h)
      have hsp : (specialPiece G v).val = a G v - 1 := rfl
      have hfo : (followingPiece G v).val = a G v := rfl
      have hcases : j.val + 1 ≤ (specialPiece G v).val ∨
          (followingPiece G v).val + 1 ≤ j.val := by omega
      rcases hcases with hbefore | hafter
      · apply overlap_zero_of_before
        have hfin : j.succ ≤ (specialPiece G v).castSucc := hbefore
        exact (hT.1.2.2 hfin).trans houter.1
      · apply overlap_zero_of_after
        have hfin : (followingPiece G v).succ ≤ j.castSucc := hafter
        exact houter.2.trans (hT.1.2.2 hfin)

theorem eq_special_iff (G : HZTractability.ThrGraph) (v : Fin G.n) (j : Fin (N G)) :
    j = specialPiece G v ↔ j.val + 1 = a G v := by
  have ha := LocalizationProof.a_pos G v
  have hsp : (specialPiece G v).val = a G v - 1 := rfl
  constructor
  · intro h
    rw [h, hsp]
    omega
  · intro h
    apply Fin.ext
    omega

theorem eq_following_iff (G : HZTractability.ThrGraph) (v : Fin G.n) (j : Fin (N G)) :
    j = followingPiece G v ↔ j.val + 1 = a G v + 1 := by
  have hfo : (followingPiece G v).val = a G v := rfl
  constructor
  · intro h
    rw [h, hfo]
  · intro h
    apply Fin.ext
    omega

theorem boundary_overlap_nat (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (v : Fin G.n) (j : Fin (N G)) :
    overlap (T.cuts j.castSucc) (T.cuts j.succ)
      ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ) =
        if j.val+1 = a G v then z G T v else
          if j.val+1 = a G v+1 then 1-z G T v else 0 := by
  simpa only [eq_special_iff, eq_following_iff] using boundary_overlap G T hT v j

noncomputable def boundarySum (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (i j : Fin (N G)) : ℝ :=
  (((List.finRange G.n).filter
    (fun v => i.val+1 = a G v ∨ i.val+1 = a G v+1)).map
    (fun v => overlap (T.cuts j.castSucc) (T.cuts j.succ)
      ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ))).sum

theorem boundarySum_bounds (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (i j : Fin (N G)) : 0 ≤ boundarySum G T i j ∧ boundarySum G T i j ≤ 1 := by
  refine ⟨?_, LocalizationProof.boundary_sum_le G i _ _⟩
  apply List.sum_nonneg
  intro r hr
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
  exact LocalizationProof.overlap_nonneg _ _ _ _

theorem boundarySum_own (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (i : Fin (N G)) :
    boundarySum G T i i = boundaryOwn G (z G T) i := by
  unfold boundarySum boundaryOwn
  rw [LocalizationProof.sum_filter_map, ← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  rw [boundary_overlap_nat G T hT]
  by_cases hsp : i.val+1 = a G v <;> by_cases hfo : i.val+1 = a G v+1 <;>
    simp only [hsp, hfo, or_self, or_true, true_or, or_false, false_or,
      if_true, if_false]

theorem boundarySum_next (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (i : Fin (N G))
    (havoid : ∀ v : Fin G.n, (i.val+1 = a G v ∨ i.val+1 = a G v+1) →
      (pi G i).val+1 ≠ a G v ∧ (pi G i).val+1 ≠ a G v+1) :
    boundarySum G T i (pi G i) = 0 := by
  unfold boundarySum
  rw [LocalizationProof.sum_filter_map, ← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : i.val+1 = a G v ∨ i.val+1 = a G v+1
  · rw [if_pos hv, boundary_overlap_nat G T hT,
      if_neg (havoid v hv).1, if_neg (havoid v hv).2]
  · exact if_neg hv

theorem pieceValue_formula (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (i j : Fin (N G)) :
    pieceValue G T i j = T.length j +
      (if j = i then (ownBonus G i : ℝ) else 0) +
      (if j = pi G i then (nextBonus G i : ℝ) else 0) + boundarySum G T i j := by
  have hcore := LocalizationProof.core_localization G T
    (LocalizationProof.cut_localization G T hT)
  have hown := centered_overlap G T hcore j i (ownBonus G i)
    (LocalizationProof.ownBonus_bounds G i).1 (LocalizationProof.ownBonus_bounds G i).2
  have hnext := centered_overlap G T hcore j (pi G i) (nextBonus G i)
    (LocalizationProof.nextBonus_bounds G i).1 (LocalizationProof.nextBonus_bounds G i).2
  simp only [pieceValue, U, bonuses, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def]
  rw [hown, hnext]
  simp only [Allocation.length, boundarySum]
  ring

theorem ownBonus_ge_two (G : HZTractability.ThrGraph) (i : Fin (N G)) :
    (2 : ℝ) ≤ ownBonus G i := by
  unfold ownBonus
  split_ifs <;> norm_num

theorem own_value_lower (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (i : Fin (N G)) :
    T.length i + 2 ≤ pieceValue G T i i := by
  rw [pieceValue_formula G T hT, if_pos rfl]
  have ho := ownBonus_ge_two G i
  have hb := (boundarySum_bounds G T i i).1
  have hn : (0 : ℝ) ≤ if i = pi G i then (nextBonus G i : ℝ) else 0 := by
    split_ifs
    · exact_mod_cast (LocalizationProof.nextBonus_bounds G i).1
    · exact le_rfl
  linarith

theorem other_value_upper (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (i j : Fin (N G)) (hji : j ≠ i) (hjnext : j ≠ pi G i) :
    pieceValue G T i j ≤ T.length j + 1 := by
  rw [pieceValue_formula G T hT, if_neg hji, if_neg hjnext]
  have hb := (boundarySum_bounds G T i j).2
  linarith

theorem lemma8_of_combinatorics (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T)
    (hnonfixed : ∀ i : Fin (N G), pi G i ≠ i)
    (havoid : ∀ i : Fin (N G), ∀ v : Fin G.n,
      (i.val+1 = a G v ∨ i.val+1 = a G v+1) →
      (pi G i).val+1 ≠ a G v ∧ (pi G i).val+1 ≠ a G v+1)
    (hc : ∀ j : Fin (N G), 0 ≤ correction G (z G T) j ∧ correction G (z G T) j ≤ 1)
    (hdiff : ∀ i : Fin (N G),
      correction G (z G T) (pi G i) - correction G (z G T) i =
        ((nextBonus G i : ℝ) - ownBonus G i) - boundaryOwn G (z G T) i) :
    (∀ i j : Fin (N G),
      pieceValue G T i j - pieceValue G T i i ≤ price G T j - price G T i) ∧
    (∀ i : Fin (N G),
      pieceValue G T i (pi G i) - pieceValue G T i i =
        price G T (pi G i) - price G T i) := by
  have heq (i : Fin (N G)) :
      pieceValue G T i (pi G i) - pieceValue G T i i =
        price G T (pi G i) - price G T i := by
    rw [pieceValue_formula G T hT, pieceValue_formula G T hT,
      if_neg (hnonfixed i), if_pos rfl, if_pos rfl,
      if_neg (Ne.symm (hnonfixed i)), boundarySum_next G T hT i (havoid i),
      boundarySum_own G T hT, correction_price, correction_price]
    have h := hdiff i
    linarith
  refine ⟨?_, heq⟩
  intro i j
  by_cases hji : j = i
  · subst j
    simp only [sub_self, le_refl]
  · by_cases hjnext : j = pi G i
    · subst j
      exact (heq i).le
    · have hu := other_value_upper G T hT i j hji hjnext
      have hl := own_value_lower G T hT i
      rw [correction_price, correction_price]
      have hcj := (hc j).1
      have hci := (hc i).2
      linarith

end ContiguousCake597.Approximate.PriceProof

end


section
-- Source module: Solutions/Cake597Cycle.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.CycleProof

variable {α : Type*} [DecidableEq α]

theorem formPerm_delta (l : List α) (hnd : l.Nodup) (F D : α → ℝ)
    (hchain : l.IsChain (fun x y => F y - F x = D x))
    (hwrap : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, F y - F x = D x)
    (hout : ∀ x ∉ l, D x = 0) :
    ∀ x, F (l.formPerm x) - F x = D x := by
  intro x
  by_cases hx : x ∈ l
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.formPerm_apply_getElem l hnd k hk]
    by_cases hknext : k+1 < l.length
    · simpa only [Nat.mod_eq_of_lt hknext] using
        (List.isChain_iff_getElem.mp hchain k hknext)
    · have hklen : k+1 = l.length := by omega
      have hne : l ≠ [] := by intro he; simp only [he, List.length_nil] at hk; omega
      have hklast : k = l.length - 1 := by omega
      have hlast : l[k] ∈ l.getLast? := by
        simp only [List.getLast?_eq_getLast hne, List.getLast_eq_getElem hne,
          Option.mem_some_iff, hklast]
      have hhead : l[0] ∈ l.head? := by
        rw [List.head?_eq_head hne, List.getElem_zero (by omega : 0 < l.length)]
        rfl
      simpa only [hklen, Nat.mod_self] using hwrap l[k] hlast l[0] hhead
  · rw [List.formPerm_apply_of_notMem hx, hout x hx]
    ring

theorem pairwise_of_mem {l : List α} {R : α → α → Prop}
    (h : ∀ x ∈ l, ∀ y ∈ l, R x y) : l.Pairwise R := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj _
  exact h l[i] (List.getElem_mem hi) l[j] (List.getElem_mem hj)

theorem block_delta (entry exit : α) (body rest : List α)
    (hnd : ((entry :: body ++ [exit]) ++ rest).Nodup) (F D : α → ℝ) (t : ℝ)
    (hentryF : F entry = 0) (hentryD : D entry = t)
    (hexitF : F exit = t) (hexitD : D exit = -t)
    (hbody : ∀ x ∈ body, F x = t ∧ D x = 0)
    (hrest : ∀ x ∈ rest, F x = 0 ∧ D x = 0)
    (hout : ∀ x ∉ ((entry :: body ++ [exit]) ++ rest), D x = 0) :
    ∀ x, F (((entry :: body ++ [exit]) ++ rest).formPerm x) - F x = D x := by
  let R : α → α → Prop := fun x y => F y - F x = D x
  have hbodyPair : body.Pairwise R := pairwise_of_mem (by
    intro x hx y hy
    dsimp only [R]
    rw [(hbody y hy).1, (hbody x hx).1, (hbody x hx).2]
    ring)
  have hentryBody : (entry :: body).Pairwise R := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, hbodyPair⟩
    intro y hy
    dsimp only [R]
    rw [(hbody y hy).1, hentryF, hentryD]
    ring
  have hprefix : (entry :: body ++ [exit]).IsChain R := by
    apply List.Pairwise.isChain
    apply List.pairwise_append.mpr
    refine ⟨hentryBody, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = exit := List.mem_singleton.mp hy
    subst y
    dsimp only [R]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hexitF, hentryF, hentryD]
      ring
    · rw [hexitF, (hbody x hx).1, (hbody x hx).2]
      ring
  have hrestChain : rest.IsChain R := by
    apply List.Pairwise.isChain
    apply pairwise_of_mem
    intro x hx y hy
    dsimp only [R]
    rw [(hrest y hy).1, (hrest x hx).1, (hrest x hx).2]
    ring
  apply formPerm_delta _ hnd F D (hprefix.append hrestChain ?_) ?_ hout
  · intro x hx y hy
    have hx' : x = exit := by
      change x ∈ ((entry :: body) ++ [exit]).getLast? at hx
      simpa only [List.getLast?_append_of_ne_nil _ (by simp : [exit] ≠ []),
        List.getLast?_singleton, Option.mem_some_iff, eq_comm] using hx
    subst x
    have hyrest := List.mem_of_mem_head? hy
    dsimp only [R]
    rw [(hrest y hyrest).1, hexitF, hexitD]
    ring
  · intro x hx y hy
    change y ∈ (entry :: ((body ++ [exit]) ++ rest)).head? at hy
    have hy' : y = entry := by simpa only [List.head?_cons, Option.mem_some_iff, eq_comm] using hy
    subst y
    cases rest with
    | nil =>
      have hx' : x = exit := by
        change x ∈ (((entry :: body) ++ [exit]) ++ []).getLast? at hx
        simpa only [List.append_nil,
          List.getLast?_append_of_ne_nil _ (by simp : [exit] ≠ []),
          List.getLast?_singleton, Option.mem_some_iff, eq_comm] using hx
      subst x
      rw [hentryF, hexitF, hexitD]
      ring
    | cons r rs =>
      have hxlast : x ∈ (r :: rs).getLast? := by
        change x ∈ ((entry :: body ++ [exit]) ++ (r :: rs)).getLast? at hx
        simpa only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] using hx
      have hxrest := List.mem_of_mem_getLast? hxlast
      rw [hentryF, (hrest x hxrest).1, (hrest x hxrest).2]
      ring

theorem block_indicator_delta (entry exit : α) (body rest : List α)
    (hnd : ((entry :: body ++ [exit]) ++ rest).Nodup)
    (P : α → Prop) [DecidablePred P] (t : ℝ)
    (hentry : ¬ P entry) (hexit : P exit)
    (hbody : ∀ x ∈ body, P x) (hrest : ∀ x ∈ rest, ¬ P x) :
    ∀ x,
      (if P (((entry :: body ++ [exit]) ++ rest).formPerm x) then t else 0) -
        (if P x then t else 0) =
          if x = entry then t else if x = exit then -t else 0 := by
  have hndP := (List.nodup_append.mp hnd).1
  have hentrynot := (List.nodup_cons.mp hndP).1
  have hee : entry ≠ exit := by
    intro he
    exact hentrynot (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr he)))
  have hcross := (List.nodup_append.mp (List.nodup_cons.mp hndP).2).2.2
  have hexitnot : exit ∉ body := by
    intro hx
    exact hcross exit hx exit (by simp) rfl
  have hrestcross := (List.nodup_append.mp hnd).2.2
  apply block_delta entry exit body rest hnd
    (fun x => if P x then t else 0)
    (fun x => if x = entry then t else if x = exit then -t else 0) t
  · exact if_neg hentry
  · simp
  · exact if_pos hexit
  · simp only [if_neg (Ne.symm hee), ite_true, eq_self]
  · intro x hx
    have hxe : x ≠ entry := fun h => hentrynot (by simp [← h, hx])
    have hxx : x ≠ exit := fun h => hexitnot (h ▸ hx)
    exact ⟨if_pos (hbody x hx), by simp only [if_neg hxe, if_neg hxx]⟩
  · intro x hx
    have hxe : x ≠ entry := fun h =>
      hrestcross entry (by simp) x hx h.symm
    have hxx : x ≠ exit := fun h =>
      hrestcross exit (by simp) x hx h.symm
    exact ⟨if_neg (hrest x hx), by simp only [if_neg hxe, if_neg hxx]⟩
  · intro x hx
    have hxe : x ≠ entry := fun h => hx (h ▸ (by simp))
    have hxx : x ≠ exit := fun h => hx (h ▸ (by simp))
    simp only [if_neg hxe, if_neg hxx]

theorem infix_indicator_delta (before body after : List α) (entry exit : α)
    (hnd : (before ++ (entry :: body ++ [exit]) ++ after).Nodup)
    (P : α → Prop) [DecidablePred P] (t : ℝ)
    (hentry : ¬ P entry) (hexit : P exit)
    (hbody : ∀ x ∈ body, P x)
    (hother : ∀ x ∈ before ++ after, ¬ P x) :
    ∀ x,
      (if P ((before ++ (entry :: body ++ [exit]) ++ after).formPerm x) then t else 0) -
        (if P x then t else 0) =
          if x = entry then t else if x = exit then -t else 0 := by
  have hnd' : ((entry :: body ++ [exit]) ++ (after ++ before)).Nodup := by
    have h := (List.nodup_rotate (n := before.length)).mpr hnd
    simpa only [List.append_assoc, List.rotate_append_length_eq] using h
  have hperm : (before ++ (entry :: body ++ [exit]) ++ after).formPerm =
      ((entry :: body ++ [exit]) ++ (after ++ before)).formPerm := by
    have h := List.formPerm_rotate _ hnd before.length
    simpa only [List.append_assoc, List.rotate_append_length_eq] using h.symm
  rw [hperm]
  apply block_indicator_delta entry exit body (after ++ before) hnd' P t hentry hexit hbody
  intro x hx
  apply hother
  simpa only [List.mem_append, or_comm] using hx

theorem block_cross_avoid (entry exit : α) (body rest : List α)
    (hnd : ((entry :: body ++ [exit]) ++ rest).Nodup)
    (hbody : body ≠ []) (hrest : rest ≠ []) :
    ((entry :: body ++ [exit]) ++ rest).formPerm entry ≠ exit ∧
      ((entry :: body ++ [exit]) ++ rest).formPerm exit ≠ entry := by
  have hcross := (List.nodup_append.mp hnd).2.2
  constructor
  · cases body with
    | nil => exact (hbody rfl).elim
    | cons b bs =>
      have hnd' : (entry :: b :: ((bs ++ [exit]) ++ rest)).Nodup := hnd
      have hnext := List.formPerm_apply_head entry b ((bs ++ [exit]) ++ rest) hnd'
      change (entry :: b :: ((bs ++ [exit]) ++ rest)).formPerm entry ≠ exit
      rw [hnext]
      have htail := (List.nodup_cons.mp (List.nodup_cons.mp hnd').2).1
      intro he
      exact htail (by simp [he])
  · intro he
    change (entry :: ((body ++ [exit]) ++ rest)).formPerm exit = entry at he
    have hlast := (List.formPerm_eq_head_iff_eq_getLast _ exit entry).mp he
    have hlastmem : ((entry :: body ++ [exit]) ++ rest).getLast (by simp) ∈ rest := by
      have hlast? : ((entry :: body ++ [exit]) ++ rest).getLast (by simp) ∈
          (((entry :: body ++ [exit]) ++ rest).getLast?) := by
        rw [List.getLast?_eq_getLast (by simp)]
        rfl
      rw [List.getLast?_append_of_ne_nil _ hrest] at hlast?
      exact List.mem_of_mem_getLast? hlast?
    have hexitrest : exit ∈ rest := hlast.symm ▸ hlastmem
    exact hcross exit (by simp) exit hexitrest rfl

theorem infix_cross_avoid (before body after : List α) (entry exit : α)
    (hnd : (before ++ (entry :: body ++ [exit]) ++ after).Nodup)
    (hbody : body ≠ []) (hrest : after ++ before ≠ []) :
    (before ++ (entry :: body ++ [exit]) ++ after).formPerm entry ≠ exit ∧
      (before ++ (entry :: body ++ [exit]) ++ after).formPerm exit ≠ entry := by
  have hnd' : ((entry :: body ++ [exit]) ++ (after ++ before)).Nodup := by
    have h := (List.nodup_rotate (n := before.length)).mpr hnd
    simpa only [List.append_assoc, List.rotate_append_length_eq] using h
  have hperm : (before ++ (entry :: body ++ [exit]) ++ after).formPerm =
      ((entry :: body ++ [exit]) ++ (after ++ before)).formPerm := by
    have h := List.formPerm_rotate _ hnd before.length
    simpa only [List.append_assoc, List.rotate_append_length_eq] using h.symm
  rw [hperm]
  exact block_cross_avoid entry exit body (after ++ before) hnd' hbody hrest

end ContiguousCake597.Approximate.CycleProof

end


section
-- Source module: Solutions/Cake597CycleConstruction.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.CycleConstruction

def segment (G : HZTractability.ThrGraph) (v : Fin G.n) : List ℕ :=
  [a G v+1] ++ (setList G v).filter (· ≠ a G v) ++ [a G v]

theorem mem_segment (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) (x : ℕ) :
    x ∈ segment G v ↔ x = a G v+1 ∨ x ∈ S G v := by
  have hav := (Cake597Blocks.own_members G hdeg v).1
  simp only [segment, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_filter, decide_eq_true_eq, ne_eq]
  constructor
  · rintro ((hx | ⟨hx, _⟩) | hx)
    · exact Or.inl hx
    · exact Or.inr (by simpa only [S, List.mem_toFinset] using hx)
    · exact Or.inr (hx ▸ hav)
  · rintro (hx | hx)
    · exact Or.inl (Or.inl hx)
    · by_cases hxa : x = a G v
      · exact Or.inr hxa
      · exact Or.inl (Or.inr ⟨by simpa only [S, List.mem_toFinset] using hx, hxa⟩)

theorem segment_nodup (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) : (segment G v).Nodup := by
  have hbody := (Cake597Blocks.setList_nodup G hdeg v).filter (fun x => x ≠ a G v)
  change ((a G v+1) :: ((setList G v).filter (· ≠ a G v) ++ [a G v])).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro hx
    rcases List.mem_append.mp hx with hx | hx
    · have hS : a G v+1 ∈ S G v := by
        simpa only [S, List.mem_toFinset] using (List.mem_filter.mp hx).1
      exact Cake597Blocks.following_outside G hdeg v v hS
    · have he := List.mem_singleton.mp hx
      omega
  · apply List.nodup_append.mpr
    refine ⟨hbody, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = a G v := List.mem_singleton.mp hy
    subst y
    exact of_decide_eq_true (List.mem_filter.mp hx).2

theorem segment_disjoint (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v w : Fin G.n) (hne : v ≠ w) : (segment G v).Disjoint (segment G w) := by
  apply List.disjoint_left.mpr
  intro x hx hx'
  rw [mem_segment G hdeg] at hx hx'
  rcases hx with rfl | hx
  · rcases hx' with he | hs
    · rcases LocalizationProof.a_separated G v w hne with h | h <;> omega
    · exact Cake597Blocks.following_outside G hdeg v w hs
  · rcases hx' with rfl | hx'
    · exact Cake597Blocks.following_outside G hdeg w v hx
    · exact Finset.disjoint_left.mp (Cake597Blocks.disjoint G hdeg v w hne) hx hx'

theorem prefix_nodup (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2) :
    (cyclePrefix G).Nodup := by
  change ((List.finRange G.n).flatMap (segment G)).Nodup
  apply List.nodup_flatMap.mpr
  refine ⟨fun v _ => segment_nodup G hdeg v, ?_⟩
  apply List.pairwise_iff_forall_sublist.mpr
  intro v w hsub
  have hne : v ≠ w := by simpa using (List.nodup_finRange G.n).sublist hsub
  exact segment_disjoint G hdeg v w hne

theorem cycleList_nodup (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2) :
    (cycleList G).Nodup := by
  unfold cycleList
  apply List.nodup_append.mpr
  refine ⟨prefix_nodup G hdeg, (List.nodup_range' (s := 1) (n := N G)).filter _, ?_⟩
  intro x hx y hy hxy
  have hy' := of_decide_eq_true (List.mem_filter.mp hy).2
  exact hy' (hxy ▸ hx)

theorem cycleList_range (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    {x : ℕ} (hx : x ∈ cycleList G) : 1 ≤ x ∧ x ≤ N G := by
  rcases List.mem_append.mp hx with hx | hx
  · change x ∈ (List.finRange G.n).flatMap (segment G) at hx
    obtain ⟨v, _, hx⟩ := List.mem_flatMap.mp hx
    rcases (mem_segment G hdeg v x).mp hx with rfl | hx
    · have ha : a G v < N G := (followingPiece G v).isLt
      omega
    · exact Cake597Blocks.S_range G hdeg hx
  · have h := List.mem_range'_1.mp (List.mem_filter.mp hx).1
    omega

theorem mem_cycleList (G : HZTractability.ThrGraph) {x : ℕ} (hx : 1 ≤ x ∧ x ≤ N G) :
    x ∈ cycleList G := by
  by_cases hp : x ∈ cyclePrefix G
  · exact List.mem_append_left _ hp
  · apply List.mem_append_right
    apply List.mem_filter.mpr
    exact ⟨List.mem_range'_1.mpr (by omega), decide_eq_true hp⟩

def index (G : HZTractability.ThrGraph) (x : ℕ) : Fin (N G) :=
  ⟨(x-1) % N G, Nat.mod_lt _ (LocalizationProof.N_pos G)⟩

theorem index_val (G : HZTractability.ThrGraph) {x : ℕ} (hx : 1 ≤ x ∧ x ≤ N G) :
    (index G x).val + 1 = x := by
  simp only [index, Nat.mod_eq_of_lt (by omega : x-1 < N G)]
  omega

theorem index_injective (G : HZTractability.ThrGraph) {x y : ℕ}
    (hx : 1 ≤ x ∧ x ≤ N G) (hy : 1 ≤ y ∧ y ≤ N G) (he : index G x = index G y) : x = y := by
  have h := congrArg Fin.val he
  have hx' := index_val G hx
  have hy' := index_val G hy
  omega

theorem indices_eq_map (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2) :
    cycleIndices G = (cycleList G).map (index G) := by
  unfold cycleIndices
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro x hx
  have hv := cycleList_range G hdeg hx
  rw [dif_pos (show 0 < x ∧ x ≤ N G by omega)]
  congr 1
  apply Fin.ext
  simp only [index, Nat.mod_eq_of_lt (by omega : x-1 < N G)]

theorem indices_nodup (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2) :
    (cycleIndices G).Nodup := by
  rw [indices_eq_map G hdeg]
  apply (cycleList_nodup G hdeg).map_on
  intro x hx y hy he
  exact index_injective G (cycleList_range G hdeg hx) (cycleList_range G hdeg hy) he

theorem mem_indices (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (i : Fin (N G)) : i ∈ cycleIndices G := by
  rw [indices_eq_map G hdeg]
  have hi : 1 ≤ i.val+1 ∧ i.val+1 ≤ N G := by omega
  refine List.mem_map.mpr ⟨i.val+1, mem_cycleList G hi, ?_⟩
  apply Fin.ext
  have hval := index_val G hi
  omega

theorem pi_nonfixed (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (i : Fin (N G)) : pi G i ≠ i := by
  have hnd := indices_nodup G hdeg
  have hall : (cycleIndices G).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact mem_indices G hdeg i
  have hlen : (cycleIndices G).length = N G := by
    rw [← List.toFinset_card_of_nodup hnd, hall]
    simp
  apply (List.formPerm_apply_mem_ne_self_iff _ hnd i (mem_indices G hdeg i)).mpr
  rw [hlen]
  unfold N
  have hsq : 1 ≤ (G.n+1)^2 := Nat.one_le_pow 2 _ (by omega)
  omega

end ContiguousCake597.Approximate.CycleConstruction

end


section
-- Source module: Solutions/Cake597SingleCycle.lean
namespace ContiguousCake597.Approximate

theorem cyclic_orbit (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2) :
    SingleCycle (pi G) := by
  intro i j
  let xs := cycleIndices G
  have hi : i ∈ xs := CycleConstruction.mem_indices G hdeg _
  have hj : j ∈ xs := CycleConstruction.mem_indices G hdeg _
  let a := xs.idxOf i
  let b := xs.idxOf j
  have ha : a < xs.length := List.idxOf_lt_length_iff.mpr hi
  have hb : b < xs.length := List.idxOf_lt_length_iff.mpr hj
  let k := xs.length - a + b
  refine ⟨k, ?_⟩
  have h := List.formPerm_pow_apply_getElem xs (CycleConstruction.indices_nodup G hdeg) k a ha
  have hk : (a+k) % xs.length = b := by
    rw [show a+k = b+xs.length by dsimp [k]; omega,Nat.add_mod_right,Nat.mod_eq_of_lt hb]
  have hi' : xs[a] = i := List.getElem_idxOf ha
  have hj' : xs[b] = j := List.getElem_idxOf hb
  rw [hi'] at h
  have hx : xs[(a+k) % xs.length] = xs[b] := by simp [hk]
  rw [hx,hj'] at h
  simpa [pi,Equiv.Perm.coe_pow] using h
end ContiguousCake597.Approximate
end


section
-- Source module: Solutions/Cake597CycleBlocks.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.CycleConstruction

theorem source_block (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) :
    ∃ before after : List ℕ,
      cycleList G = before ++ segment G v ++ after ∧
      (∀ x ∈ before ++ after, x ∉ S G v) := by
  obtain ⟨us, ws, hsplit⟩ := List.mem_iff_append.mp (List.mem_finRange v)
  let before := us.flatMap (segment G)
  let after := ws.flatMap (segment G) ++
    (List.range' 1 (N G)).filter (fun j => j ∉ cyclePrefix G)
  have heq : cycleList G = before ++ segment G v ++ after := by
    change (List.finRange G.n).flatMap (segment G) ++
      (List.range' 1 (N G)).filter (fun j => j ∉ cyclePrefix G) = _
    rw [hsplit, List.flatMap_append, List.flatMap_cons]
    simp only [before, after, List.append_assoc]
  refine ⟨before, after, heq, ?_⟩
  have hnd : (us ++ v :: ws).Nodup := hsplit ▸ List.nodup_finRange G.n
  have hnot (u : Fin G.n) (hu : u ∈ us ++ ws) : u ≠ v := by
    intro huv
    subst u
    rcases List.mem_append.mp hu with hu | hu
    · exact (List.nodup_append.mp hnd).2.2 v hu v (by simp) rfl
    · exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hu
  have hseg (u : Fin G.n) (hu : u ∈ us ++ ws) (x : ℕ) (hx : x ∈ segment G u) :
      x ∉ S G v := by
    rcases (mem_segment G hdeg u x).mp hx with rfl | hx
    · exact Cake597Blocks.following_outside G hdeg u v
    · exact fun hv => Finset.disjoint_left.mp
        (Cake597Blocks.disjoint G hdeg u v (hnot u hu)) hx hv
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hx
    exact hseg u (List.mem_append_left _ hu) x hx
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hx
      exact hseg u (List.mem_append_right _ hu) x hx
    · have hpnot := of_decide_eq_true (List.mem_filter.mp hx).2
      intro hxS
      apply hpnot
      change x ∈ (List.finRange G.n).flatMap (segment G)
      exact List.mem_flatMap.mpr ⟨v, List.mem_finRange v,
        (mem_segment G hdeg v x).mpr (Or.inr hxS)⟩

def bodyIndices (G : HZTractability.ThrGraph) (v : Fin G.n) : List (Fin (N G)) :=
  ((setList G v).filter (· ≠ a G v)).map (index G)

theorem index_following (G : HZTractability.ThrGraph) (v : Fin G.n) :
    index G (a G v+1) = followingPiece G v := by
  apply (PriceProof.eq_following_iff G v _).mpr
  apply index_val
  have hlt : a G v < N G := (followingPiece G v).isLt
  omega

theorem index_special (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) : index G (a G v) = specialPiece G v := by
  apply (PriceProof.eq_special_iff G v _).mpr
  exact index_val G (Cake597Blocks.S_range G hdeg (Cake597Blocks.own_members G hdeg v).1)

theorem body_inside (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) : ∀ x ∈ bodyIndices G v, x.val+1 ∈ S G v := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have hjS : j ∈ S G v := by
    simpa only [S, List.mem_toFinset] using (List.mem_filter.mp hj).1
  rw [index_val G (Cake597Blocks.S_range G hdeg hjS)]
  exact hjS

theorem body_nonempty (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) : bodyIndices G v ≠ [] := by
  have ha := LocalizationProof.a_pos G v
  have hj := (Cake597Blocks.own_members G hdeg v).2
  have hm : index G (a G v-1) ∈ bodyIndices G v := by
    apply List.mem_map.mpr
    refine ⟨a G v-1, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · simpa only [S, List.mem_toFinset] using hj
    · apply decide_eq_true
      omega
  intro he
  simpa only [he, List.not_mem_nil] using hm

theorem typed_block (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (v : Fin G.n) :
    ∃ before after : List (Fin (N G)),
      cycleIndices G = before ++
        (followingPiece G v :: bodyIndices G v ++ [specialPiece G v]) ++ after ∧
      (∀ x ∈ before ++ after, x.val+1 ∉ S G v) ∧ after ++ before ≠ [] := by
  obtain ⟨bs, cs, heq, hother⟩ := source_block G hdeg v
  let before := bs.map (index G)
  let after := cs.map (index G)
  have hfactor : cycleIndices G = before ++
      (followingPiece G v :: bodyIndices G v ++ [specialPiece G v]) ++ after := by
    rw [indices_eq_map G hdeg, heq]
    simp only [segment, List.map_append, List.map_cons, List.map_nil,
      index_following G v, index_special G hdeg v, List.singleton_append,
      before, after, bodyIndices]
  have hzero : ∀ x ∈ before ++ after, x.val+1 ∉ S G v := by
    intro x hx
    rw [← List.map_append] at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hjfull : j ∈ cycleList G := by
      rw [heq]
      rcases List.mem_append.mp hj with hj | hj
      · exact List.mem_append_left _ (List.mem_append_left _ hj)
      · exact List.mem_append_right _ hj
    rw [index_val G (cycleList_range G hdeg hjfull)]
    exact hother j hj
  refine ⟨before, after, hfactor, hzero, ?_⟩
  have hN : 1 ≤ N G := by have := LocalizationProof.N_pos G; omega
  let one := index G 1
  have honeval : one.val+1 = 1 := index_val G ⟨le_rfl, hN⟩
  have honeSin : one.val+1 ∉ S G v := by
    rw [honeval]
    exact Cake597Blocks.one_outside G hdeg v
  have ha32 : 32 ≤ a G v := by
    have hmul := Nat.mul_le_mul_right (R G) (show 1 ≤ v.val+1 by omega)
    have hR := LocalizationProof.R_ge G
    have hRa : R G ≤ a G v := by simpa only [Nat.one_mul, a] using hmul
    exact hR.trans hRa
  have honeentry : one ≠ followingPiece G v := by
    intro h
    have h' := (PriceProof.eq_following_iff G v one).mp h
    omega
  have honeexit : one ≠ specialPiece G v := by
    intro h
    have h' := (PriceProof.eq_special_iff G v one).mp h
    omega
  have honebody : one ∉ bodyIndices G v := fun hm => honeSin (body_inside G hdeg v one hm)
  have hm := mem_indices G hdeg one
  rw [hfactor] at hm
  have hoth : one ∈ before ++ after := by
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ hm
      · rcases List.mem_cons.mp hm with hm | hm
        · exact (honeentry hm).elim
        · rcases List.mem_append.mp hm with hm | hm
          · exact (honebody hm).elim
          · exact (honeexit (List.mem_singleton.mp hm)).elim
    · exact List.mem_append_right _ hm
  have hoth' : one ∈ after ++ before := by simpa only [List.mem_append, or_comm] using hoth
  intro hn
  simpa only [hn, List.not_mem_nil] using hoth'

theorem correction_bounds (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (t : Fin G.n → ℝ) (ht : ∀ v, 0 ≤ t v ∧ t v ≤ 1) (j : Fin (N G)) :
    0 ≤ PriceProof.correction G t j ∧ PriceProof.correction G t j ≤ 1 := by
  classical
  by_cases hex : ∃ v : Fin G.n, j.val+1 ∈ S G v
  · obtain ⟨v, hv⟩ := hex
    have heq : PriceProof.correction G t j = t v := by
      unfold PriceProof.correction
      rw [Finset.sum_eq_single v]
      · exact if_pos hv
      · intro w _ hwv
        apply if_neg
        intro hw
        exact Finset.disjoint_left.mp (Cake597Blocks.disjoint G hdeg w v hwv) hw hv
      · simp
    rw [heq]
    exact ht v
  · have heq : PriceProof.correction G t j = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      exact if_neg (fun hv => hex ⟨v, hv⟩)
    rw [heq]
    norm_num

end ContiguousCake597.Approximate.CycleConstruction

end


section
-- Source module: Solutions/Cake597PriceConstruction.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.CycleConstruction

theorem set_indicator_difference (G : HZTractability.ThrGraph)
    (hdeg : ∀ v, G.indeg v ≤ 2) (v : Fin G.n) (t : ℝ) (i : Fin (N G)) :
    (if (pi G i).val+1 ∈ S G v then t else 0) -
      (if i.val+1 ∈ S G v then t else 0) =
        if i.val+1 = a G v+1 then t else if i.val+1 = a G v then -t else 0 := by
  obtain ⟨before, after, hfactor, hother, _⟩ := typed_block G hdeg v
  have hnd : (before ++
      (followingPiece G v :: bodyIndices G v ++ [specialPiece G v]) ++ after).Nodup := by
    rw [← hfactor]
    exact indices_nodup G hdeg
  have hentry : (followingPiece G v).val+1 ∉ S G v :=
    Cake597Blocks.following_outside G hdeg v v
  have hexit : (specialPiece G v).val+1 ∈ S G v := by
    rw [(PriceProof.eq_special_iff G v _).mp rfl]
    exact (Cake597Blocks.own_members G hdeg v).1
  have h := CycleProof.infix_indicator_delta before (bodyIndices G v) after
    (followingPiece G v) (specialPiece G v) hnd
    (fun x : Fin (N G) => x.val+1 ∈ S G v) t hentry hexit (body_inside G hdeg v) hother i
  rw [← hfactor] at h
  convert! h using 1 <;>
    simp only [pi, PriceProof.eq_following_iff, PriceProof.eq_special_iff]

theorem pi_boundary_avoid (G : HZTractability.ThrGraph)
    (hdeg : ∀ v, G.indeg v ≤ 2) (i : Fin (N G)) (v : Fin G.n)
    (hi : i.val+1 = a G v ∨ i.val+1 = a G v+1) :
    (pi G i).val+1 ≠ a G v ∧ (pi G i).val+1 ≠ a G v+1 := by
  obtain ⟨before, after, hfactor, _, hrest⟩ := typed_block G hdeg v
  have hnd : (before ++
      (followingPiece G v :: bodyIndices G v ++ [specialPiece G v]) ++ after).Nodup := by
    rw [← hfactor]
    exact indices_nodup G hdeg
  have hcross := CycleProof.infix_cross_avoid before (bodyIndices G v) after
    (followingPiece G v) (specialPiece G v) hnd (body_nonempty G hdeg v) hrest
  rw [← hfactor] at hcross
  change pi G (followingPiece G v) ≠ specialPiece G v ∧
    pi G (specialPiece G v) ≠ followingPiece G v at hcross
  rcases hi with hi | hi
  · have hii := (PriceProof.eq_special_iff G v i).mpr hi
    subst i
    constructor
    · intro he
      exact pi_nonfixed G hdeg _ ((PriceProof.eq_special_iff G v _).mpr he)
    · intro he
      exact hcross.2 ((PriceProof.eq_following_iff G v _).mpr he)
  · have hii := (PriceProof.eq_following_iff G v i).mpr hi
    subst i
    constructor
    · intro he
      exact hcross.1 ((PriceProof.eq_special_iff G v _).mpr he)
    · intro he
      exact pi_nonfixed G hdeg _ ((PriceProof.eq_following_iff G v _).mpr he)

theorem following_count (G : HZTractability.ThrGraph) (i : Fin (N G)) :
    (∑ v : Fin G.n, if i.val+1 = a G v+1 then (1 : ℝ) else 0) =
      if ∃ v : Fin G.n, i.val+1 = a G v+1 then 1 else 0 := by
  classical
  by_cases hex : ∃ v : Fin G.n, i.val+1 = a G v+1
  · obtain ⟨v, hv⟩ := hex
    rw [if_pos ⟨v, hv⟩, Finset.sum_eq_single v]
    · rw [if_pos hv]
    · intro w _ hwv
      apply if_neg
      intro hw
      rcases LocalizationProof.a_separated G w v hwv with h | h <;> omega
    · simp
  · rw [if_neg hex]
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (fun hv => hex ⟨v, hv⟩)

theorem bonus_difference (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (i : Fin (N G)) :
    (nextBonus G i : ℝ) - ownBonus G i =
      if ∃ v : Fin G.n, i.val+1 = a G v+1 then 1 else 0 := by
  by_cases hex : ∃ v : Fin G.n, i.val+1 = a G v+1
  · obtain ⟨v, hv⟩ := hex
    have hspecial : ¬ ∃ u : Fin G.n, i.val+1 = a G u := by
      rintro ⟨u, hu⟩
      have hm := (Cake597Blocks.own_members G hdeg u).1
      have he : a G u = a G v+1 := hu.symm.trans hv
      rw [he] at hm
      exact Cake597Blocks.following_outside G hdeg v u hm
    have ho : ownBonus G i = 2 := by rw [ownBonus, if_pos ⟨v, hv⟩]
    have hn : nextBonus G i = 3 := by rw [nextBonus, if_neg hspecial]
    rw [if_pos ⟨v, hv⟩, ho, hn]
    norm_num
  · rw [if_neg hex, ownBonus, if_neg hex, nextBonus]
    exact sub_self _

theorem correction_difference (G : HZTractability.ThrGraph)
    (hdeg : ∀ v, G.indeg v ≤ 2) (t : Fin G.n → ℝ) (i : Fin (N G)) :
    PriceProof.correction G t (pi G i) - PriceProof.correction G t i =
      ((nextBonus G i : ℝ) - ownBonus G i) - PriceProof.boundaryOwn G t i := by
  have hterm (v : Fin G.n) :
      ((if i.val+1 = a G v+1 then t v else if i.val+1 = a G v then -t v else 0) +
        (if i.val+1 = a G v then t v else if i.val+1 = a G v+1 then 1-t v else 0)) =
          if i.val+1 = a G v+1 then 1 else 0 := by
    by_cases hfo : i.val+1 = a G v+1
    · have hsp : i.val+1 ≠ a G v := by omega
      simp only [if_pos hfo, if_neg hsp]
      ring
    · by_cases hsp : i.val+1 = a G v
      · simp only [if_neg hfo, if_pos hsp]
        ring
      · simp only [if_neg hfo, if_neg hsp]
        ring
  have hsum : (PriceProof.correction G t (pi G i) - PriceProof.correction G t i) +
      PriceProof.boundaryOwn G t i =
        ∑ v : Fin G.n, if i.val+1 = a G v+1 then (1 : ℝ) else 0 := by
    unfold PriceProof.correction PriceProof.boundaryOwn
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [set_indicator_difference G hdeg v (t v) i]
    exact hterm v
  rw [following_count, ← bonus_difference G hdeg] at hsum
  linarith

end ContiguousCake597.Approximate.CycleConstruction

namespace ContiguousCake597.Approximate

theorem lemma_8_proof (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    (∀ i j : Fin (N G),
      pieceValue G T i j - pieceValue G T i i ≤ price G T j - price G T i) ∧
    (∀ i : Fin (N G),
      pieceValue G T i (pi G i) - pieceValue G T i i =
        price G T (pi G i) - price G T i) := by
  apply PriceProof.lemma8_of_combinatorics G T hT
  · exact CycleConstruction.pi_nonfixed G hdeg
  · exact CycleConstruction.pi_boundary_avoid G hdeg
  · apply CycleConstruction.correction_bounds G hdeg
    intro v
    exact PriceProof.clip_bounds _
  · exact CycleConstruction.correction_difference G hdeg (z G T)

end ContiguousCake597.Approximate

end


section
-- Source module: Solutions/Cake597Lemma9.lean

set_option autoImplicit false

namespace ContiguousCake597.Approximate.DecodingProof

open scoped BigOperators
noncomputable section

def firstIndices (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k)

theorem prefix_sum {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ∑ j ∈ firstIndices n k, f j = ∑ j : Fin k, f (Fin.castLE hk j) := by
  apply Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin k))
  · intro j hj
    exact Finset.mem_univ _
  · intro j hj l hl he
    exact Fin.ext (congrArg (fun x : Fin k => x.val) he)
  · intro j hj
    refine ⟨Fin.castLE hk j, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
    · rfl
  · intro j hj
    rfl

theorem prefix_card {n k : ℕ} (hk : k ≤ n) : (firstIndices n k).card = k := by
  have h := prefix_sum hk (fun _ => (1 : ℝ))
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_fin, Nat.cast_inj] using h

theorem prefix_lengths {n k : ℕ} (hk : k ≤ n) (T : Allocation ℝ n) :
    ∑ j ∈ firstIndices n k, T.length j = T.cuts ⟨k, by omega⟩ - T.cuts 0 := by
  rw [prefix_sum hk]
  let Q : Allocation ℝ k :=
    ⟨fun j => T.cuts (Fin.castLE (Nat.succ_le_succ hk) j), Equiv.refl _⟩
  exact LocalizationProof.sum_lengths Q

theorem sum_labels (G : HZTractability.ThrGraph) (X : Finset ℕ)
    (hX : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N G) (w : ℝ) :
    (∑ j : Fin (N G), if j.val+1 ∈ X then w else 0) = (X.card : ℝ) * w := by
  classical
  calc
    (∑ j : Fin (N G), if j.val+1 ∈ X then w else 0) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin (N G) => j.val+1 ∈ X), w := by
      rw [Finset.sum_filter]
    _ = ∑ x ∈ X, w := by
      apply Finset.sum_bij (fun j _ => j.val+1)
      · intro j hj
        exact (Finset.mem_filter.mp hj).2
      · intro j hj l hl he
        exact Fin.ext (by omega)
      · intro x hx
        have hb := hX x hx
        refine ⟨⟨x-1, by omega⟩, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, by simpa only [Nat.sub_add_cancel hb.1] using hx⟩
        · exact Nat.sub_add_cancel hb.1
      · intro j hj
        rfl
    _ = (X.card : ℝ) * w := by simp

theorem prefix_sum_labels (G : HZTractability.ThrGraph) (X : Finset ℕ)
    (hX : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N G) (k : ℕ) (w : ℝ) :
    (∑ j ∈ firstIndices (N G) k, if j.val+1 ∈ X then w else 0) =
      ((X.filter (fun x => x ≤ k)).card : ℝ) * w := by
  classical
  rw [← sum_labels G (X.filter (fun x => x ≤ k))
    (fun x hx => hX x (Finset.mem_filter.mp hx).1) w]
  rw [firstIndices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val+1 ≤ k <;> by_cases hx : j.val+1 ∈ X <;>
    simp [Finset.mem_filter, Nat.lt_iff_add_one_le, hj, hx]

theorem sum_correction (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (t : Fin G.n → ℝ) :
    (∑ j : Fin (N G), ∑ v : Fin G.n, if j.val+1 ∈ S G v then t v else 0) =
      (R G : ℝ) * ∑ v, t v := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [sum_labels G (S G v) (fun _ hx => Cake597Blocks.S_range G hdeg hx),
    Cake597Blocks.S_card G hdeg v]

theorem entry_nat (G : HZTractability.ThrGraph) (u v : Fin G.n) :
    (entry G (u.val+1) (v.val+1)).toNat = if G.adj v u then 1 else 0 := by
  by_cases h : G.adj v u <;>
    simp [entry, Nat.lt_iff_add_one_le.mp u.isLt, Nat.lt_iff_add_one_le.mp v.isLt, h]

theorem prefix_correction (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (t : Fin G.n → ℝ) (u : Fin G.n) :
    (∑ j ∈ firstIndices (N G) (a G u),
      ∑ v : Fin G.n, if j.val+1 ∈ S G v then t v else 0) =
      32 * (u.val+1 : ℕ) * (∑ v, t v) +
        12 * ∑ v, if G.adj v u then t v else 0 := by
  rw [Finset.sum_comm]
  simp_rw [prefix_sum_labels G _ (fun _ hx => Cake597Blocks.S_range G hdeg hx),
    Cake597Blocks.S_prefix_count G hdeg u]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, entry_nat]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> push_cast <;> ring

theorem price_condition (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T)
    (hprice : ∀ i j : Fin (N G),
      pieceValue G T i j - pieceValue G T i i ≤ price G T j - price G T i)
    (hnext : ∀ i : Fin (N G),
      pieceValue G T i (pi G i) - pieceValue G T i i = price G T (pi G i) - price G T i) :
    ∀ i, max (price G T i) (price G T (pi G i)) - eta G ≤ price G T (T.assign i) := by
  intro i
  have hown := hT.2 i i
  have hnxt := hT.2 i (pi G i)
  have hval := hprice i (T.assign i)
  have heq := hnext i
  change pieceValue G T i (T.assign i) ≥ pieceValue G T i i - eta G at hown
  change pieceValue G T i (T.assign i) ≥ pieceValue G T i (pi G i) - eta G at hnxt
  apply sub_le_iff_le_add.mpr
  apply max_le <;> linarith

theorem mean_bound {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (d : ℝ)
    (hpair : ∀ i j, p j - p i ≤ d) (j : Fin n) :
    |p j - (∑ i, p i) / n| ≤ d := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmean : (n : ℝ) * ((∑ i, p i) / n) = ∑ i, p i :=
    mul_div_cancel₀ _ (ne_of_gt hn')
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpair i j)
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpair j i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hu hl
  apply abs_le.mpr
  constructor <;> nlinarith

theorem sum_prices (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (T : Allocation ℝ (N G)) (hT : AnalyticAnswer G T) :
    (∑ j, price G T j) = (N G : ℝ) * B G + (R G : ℝ) * ∑ v, z G T v := by
  have hend : T.cuts (Fin.last (N G)) = (L G : ℝ) := hT.1.2.1
  simp only [price, Finset.sum_add_distrib]
  rw [sum_correction G hdeg, LocalizationProof.sum_lengths, hT.1.1, hend]
  simp [L]

theorem mean_formula (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (T : Allocation ℝ (N G)) (hT : AnalyticAnswer G T) :
    (∑ j, price G T j) / N G = (B G : ℝ) +
      (R G : ℝ) / N G * ∑ v, z G T v := by
  rw [sum_prices G hdeg T hT]
  have hN : (N G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (LocalizationProof.N_pos G)
  field_simp

theorem prefix_mean_factor (G : HZTractability.ThrGraph) (u : Fin G.n) :
    (a G u : ℝ) * ((R G : ℝ) / N G) = 32 * (u.val+1 : ℕ) := by
  have hN : (N G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (LocalizationProof.N_pos G)
  rw [← mul_div_assoc, div_eq_iff hN]
  simp only [a, R, N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
  ring

theorem prefix_price_identity (G : HZTractability.ThrGraph) (hdeg : ∀ v, G.indeg v ≤ 2)
    (T : Allocation ℝ (N G)) (hT : AnalyticAnswer G T) (u : Fin G.n) :
    (∑ j ∈ firstIndices (N G) (a G u), (price G T j - (∑ i, price G T i) / N G)) =
      T.cuts (specialPiece G u).succ - (a G u : ℝ) * B G + 12 * incoming G T u := by
  have ha : a G u ≤ N G := (followingPiece G u).isLt.le
  have hcut : (⟨a G u, by omega⟩ : Fin (N G+1)) = (specialPiece G u).succ := by
    apply Fin.ext
    simp only [Fin.val_succ, specialPiece]
    have := LocalizationProof.a_pos G u
    omega
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, prefix_card ha]
  conv_lhs => arg 1; simp only [price, Finset.sum_add_distrib]
  rw [prefix_lengths ha T, hcut, hT.1.1, prefix_correction G hdeg,
    mean_formula G hdeg T hT, mul_add, ← mul_assoc, prefix_mean_factor]
  simp only [incoming]
  ring

theorem lemma9_of_prices (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) (hcycle : SingleCycle (pi G))
    (hprice : ∀ i j : Fin (N G),
      pieceValue G T i j - pieceValue G T i i ≤ price G T j - price G T i)
    (hnext : ∀ i : Fin (N G),
      pieceValue G T i (pi G i) - pieceValue G T i i = price G T (pi G i) - price G T i) :
    ∀ u : Fin G.n,
      |T.cuts (specialPiece G u).succ - (a G u : ℝ) * B G +
        12 * incoming G T u| ≤ 1/100 := by
  have hN : 0 < N G := LocalizationProof.N_pos G
  have hN' : 0 < (N G : ℝ) := by exact_mod_cast hN
  have he : 0 ≤ eta G := by unfold eta; positivity
  have hpair := lemma_7_proof (N G) hN (pi G) T.assign hcycle (eta G) he (price G T)
    (price_condition G T hT hprice hnext)
  have hmean : ∀ j, |price G T j - (∑ i, price G T i) / N G| ≤ (N G : ℝ) * eta G :=
    mean_bound hN (price G T) _ hpair
  intro u
  have ha : a G u ≤ N G := (followingPiece G u).isLt.le
  rw [← prefix_price_identity G hdeg T hT u]
  calc
    |∑ j ∈ firstIndices (N G) (a G u), (price G T j - (∑ i, price G T i) / N G)| ≤
        ∑ j ∈ firstIndices (N G) (a G u), |price G T j - (∑ i, price G T i) / N G| :=
      Finset.abs_sum_le_sum_abs
        (fun j : Fin (N G) => price G T j - (∑ i, price G T i) / N G)
        (firstIndices (N G) (a G u))
    _ ≤ ∑ _j ∈ firstIndices (N G) (a G u), (N G : ℝ) * eta G :=
      Finset.sum_le_sum fun j _ => hmean j
    _ = (a G u : ℝ) * ((N G : ℝ) * eta G) := by
      rw [Finset.sum_const, nsmul_eq_mul, prefix_card ha]
    _ ≤ (N G : ℝ) * ((N G : ℝ) * eta G) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (mul_nonneg hN'.le he)
    _ = 1/100 := by
      unfold eta
      field_simp [ne_of_gt hN']
      <;> ring

end
end ContiguousCake597.Approximate.DecodingProof


namespace ContiguousCake597.Approximate

theorem lemma_9_proof (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    ∀ u : Fin G.n,
      |T.cuts (specialPiece G u).succ - (a G u : ℝ) * B G +
        12 * incoming G T u| ≤ 1/100 := by
  obtain ⟨hprice, hnext⟩ := lemma_8_proof G hn hdeg T hT
  exact DecodingProof.lemma9_of_prices G hn hdeg T hT (cyclic_orbit G hdeg) hprice hnext

end ContiguousCake597.Approximate

end


open ContiguousCake597.Approximate

theorem solution (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) (T : Allocation ℝ (N G))
    (hT : AnalyticAnswer G T) :
    ∀ u : Fin G.n,
      |T.cuts (specialPiece G u).succ - (a G u : ℝ) * B G +
        12 * incoming G T u| ≤ 1/100 :=
  ContiguousCake597.Approximate.lemma_9_proof G hn hdeg T hT

#print axioms solution
