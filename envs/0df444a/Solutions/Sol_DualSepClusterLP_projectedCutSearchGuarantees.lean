-- Prove2me | solution 1 for DualSepClusterLP.projectedCutSearchGuarantees
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T14:08:26.540613+00:00
-- url     : https://prove2.me/submissions/35beb5d2-4684-4e33-8bd3-b1b88be036ee

import Definitions.Def_DualSepClusterLP_CutSearch

namespace DualSepClusterLP.Master

open Finset

noncomputable abbrev opt {n : ℕ} (G : Graph n) : ℝ :=
  sInf {v : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = v}

theorem cost_nonneg {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : 0 ≤ subsetCost G S := by
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  split_ifs <;> norm_num

theorem value_nonneg {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ}
    (hz : PrimalFeasible z) : 0 ≤ primalValue G z :=
  Finset.sum_nonneg (fun S _ => mul_nonneg (cost_nonneg G S) (hz.1 S))

theorem opt_le {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ} (hz : PrimalFeasible z) :
    opt G ≤ primalValue G z :=
  csInf_le ⟨0,fun _ ⟨_,hf,e⟩ => e ▸ value_nonneg G hf⟩ ⟨z,hz,rfl⟩

theorem singleton_feasible (n : ℕ) :
    PrimalFeasible (fun S : Finset (Fin n) => if S.card=1 then 1 else 0) := by
  constructor
  · intro S; dsimp only; split <;> norm_num
  · intro i
    have he (S : Finset (Fin n)) :
        (if i∈S then (if S.card=1 then (1:ℝ) else 0) else 0) =
          if S={i} then 1 else 0 := by
      by_cases h : S.card=1
      · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp h
        simp [eq_comm]
      · by_cases hs : S={i}; · subst S; simp at h
        simp [h,hs]
    simp_rw [he]
    simp

theorem weak_duality {n : ℕ} (G : Graph n) {q : Fin n → ℝ} {z : Finset (Fin n) → ℝ}
    (hq : DualFeasible G q) (hz : PrimalFeasible z) : (∑ i, q i) ≤ primalValue G z := by
  calc
    (∑ i, q i) = ∑ i, ∑ S : Finset (Fin n), if i∈S then q i*z S else 0 := by
      apply Finset.sum_congr rfl; intro i hi
      have h := congrArg (q i * ·) (hz.2 i)
      simpa [Finset.mul_sum,mul_ite] using h.symm
    _ = ∑ S : Finset (Fin n), (∑ i ∈ S, q i) * z S := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      rw [Finset.sum_mul]; simp
    _ ≤ primalValue G z := Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_right (hq S) (hz.1 S))

theorem dual_le_opt {n : ℕ} (G : Graph n) {q : Fin n → ℝ} (hq : DualFeasible G q) :
    (∑ i, q i) ≤ opt G :=
  le_csInf ⟨_,_, singleton_feasible n,rfl⟩ (fun _ ⟨z,hz,e⟩ => e ▸ weak_duality G hq hz)

noncomputable def sparseOn {n : ℕ} (F : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℚ) : SparseWeights n :=
  (F.toList.filter (fun S => 0 < w S)).map (fun S => (S,w S))

theorem sparse_length {n : ℕ} (F : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℚ) :
    (sparseOn F w).length ≤ F.card := by
  simpa [sparseOn] using List.length_filter_le (fun S => decide (0 < w S)) F.toList

theorem sparse_weight {n : ℕ} {F : Finset (Finset (Fin n))} {w : Finset (Fin n) → ℚ}
    (hw : ∀ S∈F, 0 ≤ w S) (S : Finset (Fin n)) :
    weightAt (sparseOn F w) S = if S∈F then w S else 0 := by
  let K := F.filter (fun T => 0 < w T)
  have hp : (F.toList.filter (fun T => decide (0 < w T))).Nodup := F.nodup_toList.filter _
  unfold weightAt sparseOn
  rw [List.map_map]
  change ((F.toList.filter _).map (fun T => if T=S then w T else 0)).sum = _
  rw [← List.sum_toFinset _ hp]
  have hset : (F.toList.filter (fun T => decide (0 < w T))).toFinset = K := by
    ext; simp [K]
  rw [hset]
  simp only [Finset.sum_ite_eq',Finset.mem_filter,K]
  by_cases h : S ∈ F
  · by_cases hw' : 0 < w S
    · simp [h,hw']
    · simp [h,le_antisymm (le_of_not_gt hw') (hw S h)]
  · simp [h]

theorem sparse_valid {n : ℕ} {F : Finset (Finset (Fin n))} {w : Finset (Fin n) → ℚ}
    (hw : ∀ S∈F, 0 ≤ w S) (hcov : ∀ i : Fin n, (∑ S ∈ F, if i ∈ S then w S else 0) = 1) :
    ValidSupport (sparseOn F w) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [sparseOn,List.map_map,Function.comp_def] using F.nodup_toList.filter (fun S => decide (0<w S))
  · intro e he
    obtain ⟨S,hm,rfl⟩ := List.mem_map.mp he
    simpa using (List.mem_filter.mp hm).2
  · intro S; dsimp only; rw [sparse_weight hw]; split_ifs with h
    · exact_mod_cast hw S h
    · norm_num
  · intro i
    have hh := congrArg (fun x : ℚ => (x:ℝ)) (hcov i)
    push_cast at hh
    convert hh using 1
    simp_rw [sparse_weight hw]
    calc
      _ = ∑ S : Finset (Fin n), if S∈F then ((if i∈S then w S else 0 : ℚ):ℝ) else 0 := by
        apply sum_congr rfl; intro S hS
        by_cases a : i ∈ S <;> by_cases b : S∈F <;> simp [a,b]
      _ = _ := by simp

theorem sparse_objective {n : ℕ} (G : Graph n) {F : Finset (Finset (Fin n))}
    {w : Finset (Fin n) → ℚ} (hw : ∀ S∈F, 0 ≤ w S) :
    primalValue G (fun S => (weightAt (sparseOn F w) S : ℝ)) = ∑ S∈F, subsetCost G S * w S := by
  unfold primalValue; simp_rw [sparse_weight hw]
  calc
    _ = ∑ S : Finset (Fin n), if S∈F then subsetCost G S * (w S : ℝ) else 0 := by
      apply sum_congr rfl; intro S hS; by_cases h : S∈F <;> simp [h]
    _ = _ := by simp

theorem sandwich {n : ℕ} (G : Graph n) {z : Finset (Fin n) → ℝ} {q : Fin n → ℝ} {k : ℝ}
    (hz : PrimalFeasible z) (hq : DualFeasible G q) (hk : 0 ≤ k)
    (h : primalValue G z ≤ k * ∑ i, q i) :
    opt G ≤ k * ∑ i, q i ∧ primalValue G z ≤ k * opt G :=
  ⟨(opt_le G hz).trans h,h.trans (mul_le_mul_of_nonneg_left (dual_le_opt G hq) hk)⟩

end DualSepClusterLP.Master

namespace DualSepClusterLP.CutRecovery

noncomputable def cost {n : ℕ} (G : Graph n) (Cs : List (Finset (Fin n))) : ℝ :=
  (Cs.map (subsetCost G)).sum

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

open Finset

theorem visits_nonneg {n : ℕ} (Cs : List (Finset (Fin n))) (i : Fin n) : 0 ≤ visits Cs i := by
  apply List.sum_nonneg; intro q h; obtain ⟨S,_,rfl⟩ := List.mem_map.mp h
  split <;> norm_num

private theorem foldmax_nonneg (xs : List ℚ) : 0 ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp
  | cons a xs h => exact h.trans (le_max_right _ _)

private theorem le_fold {q : ℚ} {xs : List ℚ} (h : q ∈ xs) : q ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem fold_mem {xs : List ℚ} (h : 0 < xs.foldr max 0) : xs.foldr max 0 ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    change max a (xs.foldr max 0) ∈ a::xs
    by_cases he : xs.foldr max 0 ≤ a
    · simp [max_eq_left he]
    · have he' := le_of_not_ge he
      rw [show (a :: xs).foldr max 0 = xs.foldr max 0 by exact max_eq_right he'] at h
      rw [max_eq_right he']; exact List.mem_cons_of_mem a (ih h)

theorem visits_le_peak {n : ℕ} (Cs : List (Finset (Fin n))) (i : Fin n) :
    visits Cs i ≤ peak Cs := le_fold (List.mem_map.mpr ⟨i,by simp,rfl⟩)

theorem peak_index {n : ℕ} (Cs : List (Finset (Fin n))) (h : 0 < peak Cs) :
    ∃ i, visits Cs i = peak Cs := by
  obtain ⟨i,_,hi⟩ := List.mem_map.mp (fold_mem h)
  exact ⟨i,hi⟩

theorem sum_visits {n : ℕ} (Cs : List (Finset (Fin n))) :
    (∑ i,visits Cs i) = ((Cs.map (fun S => (S.card:ℚ))).sum) := by
  induction Cs with
  | nil => simp [visits]
  | cons S Cs ih =>
    simp only [visits,List.map_cons,List.sum_cons] at *
    rw [Finset.sum_add_distrib,ih]
    simp

theorem visits_lower {n : ℕ} (Cs : List (Finset (Fin n))) (h : ∀ S∈Cs, S.Nonempty) :
    (Cs.length:ℚ) ≤ ∑ i,visits Cs i := by
  rw [sum_visits]
  induction Cs with
  | nil => simp
  | cons S Cs ih =>
    have hp := Finset.card_pos.mpr (h S List.mem_cons_self)
    have h1 : (1:ℚ) ≤ S.card := by exact_mod_cast hp
    have h2 := ih (fun S' h' => h S' (List.mem_cons_of_mem _ h'))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one] at *
    linarith

theorem peak_pos {n : ℕ} (Cs : List (Finset (Fin n))) (ht : Cs ≠ [])
    (h : ∀ S∈Cs, S.Nonempty) : 0 < peak Cs := by
  have hs : 0 < (Cs.length:ℚ) := by exact_mod_cast List.length_pos_iff.mpr ht
  by_contra! hg
  have hz (i : Fin n) : visits Cs i = 0 := le_antisymm ((visits_le_peak Cs i).trans hg) (visits_nonneg Cs i)
  have hh := visits_lower Cs h
  rw [show (∑ i,visits Cs i) = 0 by simp [hz]] at hh
  exact hs.not_ge hh

theorem clean_length {n : ℕ} (L : SparseWeights n) : (clean L).length ≤ L.length := by
  simp only [clean,List.length_map]
  exact (List.length_filter_le _ _).trans (by simpa using (List.dedup_sublist (L.map Prod.fst)).length_le)

theorem clean_wt {n : ℕ} (L : SparseWeights n) (S : Finset (Fin n))
    (hn : ∀ e∈L, 0≤e.2) : weightAt (clean L) S = weightAt L S := by
  let xs := (L.map Prod.fst).dedup.filter (fun T => decide (0 < weightAt L T))
  have hnd : xs.Nodup := (List.nodup_dedup _).filter _
  have hz : 0 ≤ weightAt L S := by
    apply List.sum_nonneg; intro q h; obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
    split
    · exact hn e he
    · rfl
  have hm : 0 < weightAt L S → S ∈ L.map Prod.fst := by
    intro h
    by_contra h'
    have h0 : weightAt L S = 0 := by
      apply List.sum_eq_zero; intro q hq; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
      split_ifs with e'
      · exact (h' (e' ▸ List.mem_map_of_mem he)).elim
      · rfl
    linarith
  unfold clean weightAt
  rw [List.map_map]
  change (xs.map (fun T => if T=S then weightAt L T else 0)).sum = weightAt L S
  rw [←List.sum_toFinset _ hnd,Finset.sum_ite_eq']
  by_cases hp : 0 < weightAt L S
  · simp [xs,hp,hm hp]
  · simp [xs,le_antisymm (le_of_not_gt hp) hz]

theorem clean_valid {n : ℕ} (L : SparseWeights n) (hn : ∀ e∈L, 0≤e.2)
    (hc : PrimalFeasible (fun S => (weightAt L S : ℝ))) : ValidSupport (clean L) := by
  refine ⟨?_,?_,?_⟩
  · simpa [clean,List.map_map,Function.comp_def] using
      (List.nodup_dedup (L.map Prod.fst)).filter (fun T => decide (0 < weightAt L T))
  · intro e he; obtain ⟨S,hm,rfl⟩ := List.mem_map.mp he
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · simpa only [clean_wt L _ hn] using hc

theorem raw_nonneg {n : ℕ} (Cs : List (Finset (Fin n))) (hM : 0<peak Cs) :
    ∀ e ∈ raw Cs, 0≤e.2 := by
  intro e h
  rcases List.mem_append.mp h with h|h <;> obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
  · exact div_nonneg zero_le_one hM.le
  · exact div_nonneg (sub_nonneg.mpr (visits_le_peak Cs v)) hM.le

theorem eval {n : ℕ} (L : SparseWeights n) (f : Finset (Fin n) → ℝ) :
    (∑ S, f S * (weightAt L S : ℝ)) = (L.map (fun e => f e.1 * (e.2 : ℝ))).sum := by
  induction L with
  | nil => simp [weightAt]
  | cons e L ih =>
    simp only [weightAt,List.map_cons,List.sum_cons,Rat.cast_add,mul_add,Finset.sum_add_distrib] at *
    rw [ih]
    congr 1
    calc
      _ = ∑ S : Finset (Fin n), if S=e.1 then f S*(e.2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl; intro S _
        by_cases h : S=e.1 <;> simp [h,Ne.symm]
      _ = _ := by simp

private theorem list_sum_mul {α : Type*} (xs : List α) (f : α → ℝ) (a : ℝ) :
    (xs.map (fun x => f x * a)).sum = (xs.map f).sum * a := by
  induction xs <;> simp_all [add_mul]

theorem raw_cover {n : ℕ} (Cs : List (Finset (Fin n))) (hM : 0<peak Cs) :
    PrimalFeasible (fun S => (weightAt (raw Cs) S : ℝ)) := by
  have hp : (peak Cs:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  constructor
  · intro S; apply Rat.cast_nonneg.mpr; apply List.sum_nonneg; intro q h
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp h; split
    · exact raw_nonneg Cs hM e he
    · rfl
  · intro i
    have hh := eval (raw Cs) (fun S => if i∈S then 1 else 0)
    simp [ite_mul] at hh
    rw [hh]
    simp only [raw,List.map_append,List.sum_append,List.map_map,Function.comp_def,Finset.mem_singleton]
    have h₁ : (Cs.map (fun S => if i∈S then ((1/peak Cs:ℚ):ℝ) else 0)).sum =
        (visits Cs i : ℝ)/(peak Cs:ℝ) := by
      have hh : (visits Cs i:ℝ) = (Cs.map (fun S => if i∈S then (1:ℝ) else 0)).sum := by
        simp only [visits,Rat.cast_list_sum,List.map_map,Function.comp_def,apply_ite (fun x : ℚ => (x:ℝ)),Rat.cast_one,Rat.cast_zero]
      rw [hh,show ((Cs.map (fun S => if i∈S then (1:ℝ) else 0)).sum / (peak Cs:ℝ)) =
          _ * (peak Cs:ℝ)⁻¹ by rw [div_eq_mul_inv],←list_sum_mul]
      congr 1; apply List.map_congr_left; intro S _; by_cases h : i∈S <;> simp [h]
    have h₂ : ((List.finRange n).map (fun j => if i=j then (((peak Cs-visits Cs j)/peak Cs : ℚ):ℝ) else 0)).sum =
        (((peak Cs-visits Cs i)/peak Cs : ℚ):ℝ) := by
      rw [←List.ofFn_eq_map,List.sum_ofFn]; simp
    rw [h₁,h₂]
    push_cast
    field_simp
    ring

theorem valid_make {n : ℕ} (Cs : List (Finset (Fin n))) (hM : 0 < peak Cs) : ValidSupport (make Cs) :=
  clean_valid _ (raw_nonneg Cs hM) (raw_cover Cs hM)

theorem length_make {n : ℕ} (Cs : List (Finset (Fin n))) : (make Cs).length ≤ Cs.length + n :=
  (clean_length _).trans (by simp [raw])

theorem singleton_cost {n : ℕ} (G : Graph n) (i : Fin n) : subsetCost G {i} ≤ n := by
  let f (a b : Fin n) : ℝ := (if a=i then 1/2 else 0)+(if b=i then 1/2 else 0)
  have h : subsetCost G {i} ≤ ∑ a : Fin n, ∑ b : Fin n, f a b := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    unfold f; simp only [Finset.mem_singleton]
    split_ifs <;> simp_all <;> norm_num
  exact h.trans (by simp [f,Finset.sum_add_distrib]; ring_nf; norm_num)

theorem numerator {n : ℕ} (G : Graph n) (Cs : List (Finset (Fin n))) (hM : 0 < peak Cs) :
    primalValue G (fun S => (weightAt (make Cs) S : ℝ)) * (peak Cs:ℝ)
      = cost G Cs + ∑ i, subsetCost G {i}*((peak Cs:ℝ)-(visits Cs i:ℝ)) := by
  have hn := raw_nonneg Cs hM
  have hp : (peak Cs:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold make primalValue
  simp only [clean_wt (raw Cs) _ hn]
  rw [eval]
  simp only [raw,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  rw [add_mul,←list_sum_mul,←List.ofFn_eq_map,List.sum_ofFn,Finset.sum_mul]
  congr 1
  · unfold cost; congr 1; apply List.map_congr_left
    intro S _; push_cast; field_simp
  · apply Finset.sum_congr rfl; intro i _
    push_cast; field_simp

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.Master

open Finset

theorem adj_refl {n : ℕ} (G : Graph n) (i : Fin n) : adj G i i := Or.inl rfl

theorem adj_symm {n : ℕ} (G : Graph n) {i j : Fin n} : adj G i j ↔ adj G j i := by
  simp only [adj,min_comm i j,max_comm i j,eq_comm (a:=i)]

theorem adj_of_lt {n : ℕ} (G : Graph n) {i j : Fin n} (h : i<j) :
    adj G i j ↔ G i j = true := by simp [adj,h.ne,min_eq_left h.le,max_eq_right h.le]

theorem block_eq {n : ℕ} {G : Graph n} (hG : EquivalenceGraph G) {i j : Fin n}
    (h : adj G i j) : block G i = block G j := by
  ext k; simp only [block,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hG j i k ((adj_symm G).mp h), hG i j k h⟩

theorem block_cost {n : ℕ} {G : Graph n} (hG : EquivalenceGraph G) (v : Fin n) :
    subsetCost G (block G v)=0 := by
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  by_cases hij : i<j
  · cases h : G i j
    · have hh : ¬(i∈block G v ∧ j∈block G v) := by
        simp only [block,Finset.mem_filter,Finset.mem_univ,true_and]
        rintro ⟨hi,hj⟩
        have := (adj_of_lt G hij).mp (hG i v j ((adj_symm G).mp hi) hj)
        simp [h] at this
      simp [hij,h,hh]
    · have h' := (adj_of_lt G hij).mpr h
      have he : i∈block G v ↔ j∈block G v := by
        simp only [block,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨fun hi => hG v i j hi h', fun hj => hG v j i hj ((adj_symm G).mp h')⟩
      simp [hij,h,he]
  · simp [hij]

def family {n : ℕ} (G : Graph n) := Finset.univ.image (block G)

theorem zero_sparse {n : ℕ} {G : Graph n} (hG : EquivalenceGraph G) :
    ∃ L : SparseWeights n, ValidSupport L ∧ L.length ≤ n ∧
      primalValue G (fun S => (weightAt L S : ℝ)) = 0 := by
  let F := family G
  let w (_ : Finset (Fin n)) : ℚ := 1
  have hw : ∀ S∈F,0 ≤ w S := fun _ _ => by norm_num [w]
  have hf (i : Fin n) : block G i ∈ F := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have extcol (i : Fin n) (S : Finset (Fin n)) (hs : S ∈ F) : i∈S ↔ S=block G i := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨fun h => block_eq hG (by simpa [block] using h),?_⟩
    intro e; rw [e]; simp [block,adj_refl]
  have cov (i : Fin n) : (∑ S ∈ F, if i∈S then w S else 0)=1 := by
    calc
      _ = ∑ S∈F, if S=block G i then (1:ℚ) else 0 := Finset.sum_congr rfl
        (fun S h => by simp [extcol i S h,w])
      _ = _ := by simp [hf]
  refine ⟨sparseOn F w,sparse_valid hw cov,(sparse_length F w).trans ?_,?_⟩
  · exact le_trans Finset.card_image_le (by simp)
  · rw [sparse_objective G hw]
    apply Finset.sum_eq_zero
    intro S h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    simp [block_cost hG i]

private noncomputable def edge {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if i<j then if G i j then (if decide (i∈S) != decide (j∈S) then 1/2 else 0)
    else (if i∈S ∧ j∈S then 1 else 0) else 0

private theorem edge_le {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) :
    edge G S i j ≤ subsetCost G S := by
  have h (a b : Fin n) : 0 ≤ edge G S a b := by unfold edge; split_ifs <;> norm_num
  exact (Finset.single_le_sum (fun b (_ : b∈(Finset.univ : Finset (Fin n))) => h i b) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin n))) => Finset.sum_nonneg (fun b _ => h a b)) (Finset.mem_univ i))

private theorem positive_cross {n : ℕ} (G : Graph n) (S : Finset (Fin n)) {i j : Fin n}
    (hp : adj G i j) (hc : ¬(i∈S ↔ j∈S)) : 1/2 ≤ subsetCost G S := by
  have hn : i≠j := fun h => hc (h ▸ Iff.rfl)
  rcases lt_or_gt_of_ne hn with h|h
  · have he := edge_le G S i j
    have hh := (adj_of_lt G h).mp hp
    by_cases a : i∈S <;> by_cases b : j∈S <;> simp [edge,h,hh,a,b] at he hc ⊢ <;> assumption
  · have he := edge_le G S j i
    have hh := (adj_of_lt G h).mp ((adj_symm G).mp hp)
    by_cases a : i∈S <;> by_cases b : j∈S <;> simp [edge,h,hh,a,b] at he hc ⊢ <;> assumption

private theorem negative_inside {n : ℕ} (G : Graph n) (S : Finset (Fin n)) {i j : Fin n}
    (hp : ¬adj G i j) (hi : i∈S) (hj : j∈S) : 1 ≤ subsetCost G S := by
  have hn : i≠j := fun h => hp (.inl h)
  rcases lt_or_gt_of_ne hn with h|h
  · have hh : G i j=false := Bool.eq_false_iff.mpr (fun he => hp ((adj_of_lt G h).mpr he))
    simpa [edge,h,hh,hi,hj] using edge_le G S i j
  · have hh : G j i=false := Bool.eq_false_iff.mpr (fun he => hp ((adj_symm G).mpr ((adj_of_lt G h).mpr he)))
    simpa [edge,h,hh,hi,hj] using edge_le G S j i

def badPrices {n : ℕ} (i k : Fin n) (j : Fin n) : ℚ :=
  (if j=i then 1/2 else 0) + (if j=k then 1/2 else 0)

theorem bad_feasible {n : ℕ} (G : Graph n) {i j k : Fin n}
    (h₁ : adj G i j) (h₂ : adj G j k) (h₃ : ¬adj G i k) :
    DualFeasible G (fun v => (badPrices i k v : ℝ)) := by
  intro S
  have hc : (∑ v∈S, (badPrices i k v : ℝ)) =
      (if i∈S then 1/2 else 0) + (if k∈S then 1/2 else 0) := by
    simp only [badPrices,Rat.cast_add,apply_ite (fun x : ℚ => (x:ℝ)),Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,
      Rat.cast_zero,Finset.sum_add_distrib,Finset.sum_ite_eq']
  rw [hc]
  by_cases hi : i∈S <;> by_cases hk : k∈S <;> simp only [hi,hk,if_false,if_true,add_zero,zero_add]
  · convert negative_inside G S h₃ hi hk using 1 <;> norm_num
  · by_cases hj : j∈S
    · exact positive_cross G S h₂ (by simp [hj,hk])
    · exact positive_cross G S h₁ (by simp [hi,hj])
  · by_cases hj : j∈S
    · exact positive_cross G S h₁ (by simp [hi,hj])
    · exact positive_cross G S h₂ (by simp [hj,hk])
  · exact cost_nonneg G S

theorem bad_total {n : ℕ} (i k : Fin n) : (∑ v, (badPrices i k v : ℝ))=1 := by
  simp only [badPrices,Rat.cast_add,apply_ite (fun x : ℚ => (x:ℝ)),Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,
    Rat.cast_zero,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  norm_num

theorem zero_or_unit {n : ℕ} (G : Graph n) :
    (∃ L : SparseWeights n, ValidSupport L ∧ L.length ≤ n ∧
      primalValue G (fun S => (weightAt L S : ℝ)) = 0) ∨
    (∃ q : Fin n → ℚ, DualFeasible G (fun v => (q v : ℝ)) ∧ (∑ v, (q v : ℝ))=1) := by
  classical
  by_cases h : EquivalenceGraph G
  · exact Or.inl (zero_sparse h)
  · unfold EquivalenceGraph at h
    push Not at h
    obtain ⟨i,j,k,hi,hj,hk⟩ := h
    exact Or.inr ⟨badPrices i k,bad_feasible G hi hj hk,bad_total i k⟩

end DualSepClusterLP.Master

namespace DualSepClusterLP.Master

open Finset

theorem mem_blockList {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    S∈blockList G ↔ S∈family G := by simp [blockList,family]

theorem zeroList_weights {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    weightAt (zeroList G) S = if S∈family G then 1 else 0 := by
  have hnd : (blockList G).Nodup := List.nodup_dedup _
  unfold weightAt zeroList
  rw [List.map_map]
  change ((blockList G).map (fun T => if T=S then (1:ℚ) else 0)).sum = _
  rw [←List.sum_toFinset _ hnd,Finset.sum_ite_eq']
  simp [mem_blockList]

theorem zeroList_ok {n : ℕ} {G : Graph n} (hG : EquivalenceGraph G) :
    ValidSupport (zeroList G) ∧ (zeroList G).length ≤ n ∧
      primalValue G (fun S => (weightAt (zeroList G) S : ℝ))=0 := by
  have hf (i : Fin n) : block G i ∈ family G := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have extcol (i : Fin n) (S : Finset (Fin n)) (hs : S ∈ family G) : i∈S ↔ S=block G i := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨fun h => block_eq hG (by simpa [block] using h),?_⟩
    intro e; rw [e]; simp [block,adj_refl]
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
  · simpa [zeroList,List.map_map,Function.comp_def,blockList] using
      List.nodup_dedup ((List.finRange n).map (block G))
  · intro e h
    obtain ⟨S,_,rfl⟩ := List.mem_map.mp h
    norm_num
  · intro S; dsimp only; rw [zeroList_weights]; split <;> norm_num
  · intro i
    calc
      _ = ∑ S : Finset (Fin n), if S=block G i then (1:ℝ) else 0 := by
        apply Finset.sum_congr rfl; intro S _
        by_cases h : S∈family G
        · simp [zeroList_weights,h,extcol i S h]
        · have ne : S ≠ block G i := fun he => h (he ▸ hf i)
          simp [zeroList_weights,h,ne]
      _ = _ := by simp
  · simpa [zeroList,blockList] using
      (List.dedup_sublist ((List.finRange n).map (block G))).length_le
  · unfold primalValue; apply Finset.sum_eq_zero; intro S _
    by_cases h : S∈family G
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h; simp [block_cost hG]
    · simp [zeroList_weights,h]

theorem unit_le_opt {n : ℕ} {G : Graph n} (hG : ¬EquivalenceGraph G) : 1 ≤ opt G := by
  classical
  unfold EquivalenceGraph at hG; push Not at hG
  obtain ⟨i,j,k,hi,hj,hk⟩ := hG
  have h := dual_le_opt G (bad_feasible G hi hj hk)
  rw [bad_total] at h
  exact h

theorem perfect_opt {n : ℕ} {G : Graph n} (hG : EquivalenceGraph G) : opt G=0 := by
  have hz := zeroList_ok hG
  have lb := opt_le G hz.1.2.2
  rw [hz.2.2] at lb
  exact le_antisymm lb (le_csInf ⟨_,_,singleton_feasible n,rfl⟩ (fun _ ⟨_,hf,he⟩ => he ▸ value_nonneg G hf))

end DualSepClusterLP.Master

namespace DualSepClusterLP.CutRecovery

open Finset

theorem opt_upper {n : ℕ} (G : Graph n) : Master.opt G ≤ (n:ℝ)^2 := by
  apply (Master.opt_le G (Master.singleton_feasible n)).trans
  unfold primalValue
  have hs (S : Finset (Fin n)) :
      subsetCost G S * (if S.card=1 then (1:ℝ) else 0) =
        ∑ i : Fin n, if S={i} then subsetCost G {i} else 0 := by
    by_cases h : S.card=1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
      simp
    · have hh (i : Fin n) : S ≠ {i} := fun he => h (he ▸ Finset.card_singleton _)
      simp [h,hh]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => singleton_cost G i)).trans_eq
    (by simp [pow_two])

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.Compression

theorem bounded_collision (d D : ℕ) (A : Fin d → Fin (d+1) → ℕ)
    (hA : ∀ r j, A r j ≤ D) :
    let B := ((d+1)*D+1)^d
    ∃ s t : Fin (d+1) → Fin (B+1),
      (∃ j, t j < s j) ∧ ∀ r, (∑ j, (s j).val * A r j) = ∑ j, (t j).val * A r j := by
  dsimp only
  let C := (d+1)*D+1
  let B := C^d
  let y (s : Fin (d+1) → Fin (B+1)) (r : Fin d) := ∑ j, (s j).val * A r j
  have hy (s : Fin (d+1) → Fin (B+1)) (r : Fin d) : y s r < C*(B+1) := by
    have hh : y s r ≤ ∑ j : Fin (d+1), B*D := by
      apply Finset.sum_le_sum
      intro j hj; exact Nat.mul_le_mul (Nat.le_of_lt_succ (s j).isLt) (hA r j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    dsimp only [C]; nlinarith
  let f (s : Fin (d+1) → Fin (B+1)) (r : Fin d) : Fin (C*(B+1)) := ⟨y s r,hy s r⟩
  have hcard : Fintype.card (Fin d → Fin (C*(B+1))) < Fintype.card (Fin (d+1) → Fin (B+1)) := by
    simp only [Fintype.card_fun,Fintype.card_fin,mul_pow,pow_succ]
    change B * (B+1)^d < (B+1)^d * (B+1)
    rw [Nat.mul_comm B]
    apply Nat.mul_lt_mul_of_pos_left (by omega)
    positivity
  obtain ⟨s,t,hst,hneq⟩ := Function.not_injective_iff.mp (Fintype.not_injective_of_card_lt f hcard)
  have eq (r : Fin d) : y s r=y t r := congrArg Fin.val (congrFun hst r)
  by_cases h : ∃ j, t j < s j
  · exact ⟨s,t,h,eq⟩
  · refine ⟨t,s,?_,fun r => (eq r).symm⟩
    by_contra! h'
    apply hneq
    funext j
    apply le_antisymm (le_of_not_gt (fun hj => h ⟨j,hj⟩)) (h' j)

theorem prune {ι : Type} [Fintype ι] [DecidableEq ι] (w v : ι → ℚ)
    (hw : ∀ i, 0 < w i) (hp : ∃ i, 0<v i) :
    ∃ scale : ℚ, 0<scale ∧ (∀ i, 0 ≤ w i-scale*v i) ∧ ∃ j, w j-scale*v j=0 := by
  classical
  let P := Finset.univ.filter (fun i => 0 < v i)
  have ne : P.Nonempty := by simpa [P,Finset.Nonempty] using hp
  obtain ⟨j,hj,hm⟩ := P.exists_min_image (fun i => w i/v i) ne
  have hjv : 0 < v j := (Finset.mem_filter.mp hj).2
  refine ⟨w j/v j,div_pos (hw j) hjv,?_,j,?_⟩
  · intro i
    by_cases hi : 0 < v i
    · exact sub_nonneg.mpr ((le_div_iff₀ hi).mp (hm i (by simp [P,hi])))
    · have hz := div_pos (hw j) hjv
      exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hz.le (le_of_not_gt hi)).trans (hw i).le)
  · field_simp <;> ring

theorem addDir_at {N k : ℕ} (idx : Fin k → Fin N) (hi : Function.Injective idx)
    (v : Fin k → ℚ) (j : Fin k) : addDir idx v (idx j) = v j := by
  simp [addDir,hi.eq_iff]

private theorem addDir_other {N k : ℕ} (idx : Fin k → Fin N) (v : Fin k → ℚ)
    (i : Fin N) (h : ∀ j, idx j ≠ i) : addDir idx v i = 0 := by simp [addDir,h]

theorem addDir_moment {N d k : ℕ} (A : Fin d → Fin N → ℕ) (idx : Fin k → Fin N)
    (v : Fin k → ℚ) (r : Fin d) :
    moment A (addDir idx v) r = ∑ j, v j*A r (idx j) := by
  simp only [moment,addDir,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  simp [ite_mul]

theorem witness {d D N : ℕ} (A : Fin d → Fin N → ℕ) (hA : ∀ r i, A r i≤D)
    (w : Fin N → ℚ) (hw : ∀ i, 0≤w i) (hc : d<(active w).card) :
    ∃ (idx : Fin (d+1) → Fin N) (s t : Fin (d+1) → Fin (digits (d:=d) D)) (j : Fin (d+1)),
      improves A w (changed w idx s t j) := by
  let idx (j : Fin (d+1)) : Fin N := (active w).orderEmbOfFin rfl ⟨j.val,by have := j.isLt; omega⟩
  have idxmem (j) : idx j∈active w := (active w).orderEmbOfFin_mem rfl _
  have hi : Function.Injective idx := by
    intro i j h
    have e := ((active w).orderEmbOfFin rfl).injective h
    exact Fin.ext (congrArg (fun a : Fin (active w).card => a.val) e)
  obtain ⟨s,t,hp,he⟩ := bounded_collision d D (fun r j => A r (idx j)) (fun r j => hA r (idx j))
  let v := difference s t
  obtain ⟨a,ha⟩ := hp
  have hv : 0 < v a := by
    dsimp [v,difference]; exact sub_pos.mpr (by exact_mod_cast ha)
  let pos := Finset.univ.filter (fun j => 0 < v j)
  obtain ⟨j,hj,hm⟩ := pos.exists_min_image (fun j => w (idx j)/v j)
    ⟨a,by simp [pos,hv]⟩
  have hjv : 0 < v j := (Finset.mem_filter.mp hj).2
  let k := w (idx j)/v j
  have hk : 0 < k := div_pos (Finset.mem_filter.mp (idxmem j)).2 hjv
  let z := changed w idx s t j
  have hz (i) : z i = w i - k*addDir idx v i := rfl
  have hij (a) : 0 ≤ z (idx a) := by
    rw [hz,addDir_at idx hi]
    by_cases ha : 0 < v a
    · exact sub_nonneg.mpr ((le_div_iff₀ ha).mp (hm a (by simp [pos,ha])))
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hk.le (le_of_not_gt ha)).trans (hw _))
  have same (i) (h : ∀ j, idx j ≠ i) : z i=w i := by simp [hz,addDir_other idx v i h]
  have hnon (i) : 0 ≤ z i := by
    by_cases h : ∃ a, idx a=i
    · obtain ⟨a,rfl⟩ := h; exact hij a
    · rw [same i (by simpa using h)]; exact hw i
  have hz0 : z (idx j)=0 := by rw [hz,addDir_at idx hi]; dsimp [k]; field_simp <;> ring
  have hsub : active z ⊆ (active w).erase (idx j) := by
    intro i h
    have hp := (Finset.mem_filter.mp h).2
    apply Finset.mem_erase.mpr
    refine ⟨fun eq => by rw [eq,hz0] at hp; exact (lt_irrefl _ hp),?_⟩
    by_cases hh : ∃ a, idx a=i
    · obtain ⟨a,rfl⟩ := hh; exact idxmem a
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [same i (by simpa using hh)] at hp⟩
  have hnull (r) : moment A (addDir idx v) r=0 := by
    rw [addDir_moment]
    simp only [v,difference,sub_mul,Finset.sum_sub_distrib,sub_eq_zero]
    exact_mod_cast he r
  refine ⟨idx,s,t,j,hnon,(Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem (idxmem j)),?_⟩
  intro r
  have hm : moment A z r = moment A w r-k*moment A (addDir idx v) r := by
    simp only [moment,hz,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  change moment A z r = _
  rw [hm,hnull, mul_zero, sub_zero]

theorem tuples_mem {k m : ℕ} (f : Fin k → Fin m) : f∈tuples k m := by
  apply List.mem_map.mpr; exact ⟨finFunctionFinEquiv f, by simp, Equiv.symm_apply_apply _ _⟩

theorem candidates_mem {d N : ℕ} (D : ℕ) (w : Fin N → ℚ) (idx : Fin (d+1) → Fin N)
    (s t : Fin (d+1) → Fin (digits (d:=d) D)) (j : Fin (d+1)) :
    changed w idx s t j ∈ candidates (d:=d) D w := by
  exact List.mem_flatMap.mpr ⟨idx,tuples_mem _,List.mem_flatMap.mpr ⟨s,tuples_mem _,
    List.mem_flatMap.mpr ⟨t,tuples_mem _,List.mem_map.mpr ⟨j,by simp,rfl⟩⟩⟩⟩

theorem step_spec {d D N : ℕ} (A : Fin d → Fin N → ℕ) (hA : ∀ r i, A r i≤D)
    (w : Fin N → ℚ) (hw : ∀ i, 0≤w i) (hc : d<(active w).card) :
    improves A w (compressStep A D w) := by
  obtain ⟨idx,s,t,j,h⟩ := witness A hA w hw hc
  unfold compressStep
  rw [if_neg (not_le_of_gt hc)]
  let test (z : Fin N → ℚ) := decide (improves A w z)
  change improves A w (((candidates (d:=d) D w).find? test).getD w)
  cases hh : (candidates (d:=d) D w).find? test with
  | some z => exact of_decide_eq_true (List.find?_some hh : test z = true)
  | none => exact False.elim ((List.find?_eq_none.mp hh _ (candidates_mem D w idx s t j)) (decide_eq_true h))

theorem run_spec {d D N : ℕ} (A : Fin d → Fin N → ℕ) (hA : ∀ r i, A r i≤D)
    (k : ℕ) (w : Fin N → ℚ) (hw : ∀ i, 0≤w i) :
    let z := run A D k w
    (∀ i, 0 ≤ z i) ∧ (active z).card ≤ max d ((active w).card-k) ∧
      ∀ r, moment A z r = moment A w r := by
  induction k generalizing w with
  | zero => exact ⟨hw,by simp [run],fun _ => rfl⟩
  | succ k ih =>
    by_cases h : (active w).card ≤ d
    · have hs : compressStep A D w=w := by simp [compressStep,h]
      simp only [run,hs]
      obtain ⟨hp,hc,hm⟩ := ih w hw
      exact ⟨hp,by omega,hm⟩
    · obtain ⟨hp,hc,hm⟩ := step_spec A hA w hw (by omega)
      obtain ⟨hp',hc',hm'⟩ := ih _ hp
      exact ⟨hp',by simp only [run]; omega,fun r => (hm' r).trans (hm r)⟩

theorem compress_correct {d D N : ℕ} (A : Fin d → Fin N → ℕ) (hA : ∀ r i, A r i≤D)
    (w : Fin N → ℚ) (hw : ∀ i, 0≤w i) :
    let z := run A D N w
    (∀ i, 0 ≤ z i) ∧ (active z).card ≤ d ∧ ∀ r, moment A z r = moment A w r := by
  have hc := @Finset.card_le_univ (Fin N) _ (active w)
  simpa [Nat.sub_eq_zero_of_le (by simpa using hc : (active w).card ≤ N)] using run_spec A hA N w hw

end DualSepClusterLP.Compression

namespace DualSepClusterLP.Compression

theorem twiceCost_eq {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    (twiceCost G S : ℝ) = 2 * subsetCost G S := by
  simp only [twiceCost,subsetCost,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  unfold twiceEntry
  split_ifs <;> norm_num

theorem twiceCost_le {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    twiceCost G S ≤ 2*n*n := by
  have h : twiceCost G S ≤ ∑ _ : Fin n, ∑ _ : Fin n, (2:ℕ) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    unfold twiceEntry; split_ifs <;> decide
  simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h

theorem coeff_le {n : ℕ} (G : Graph n) (L : SparseWeights n) (r : Fin (n+1)) (i : Fin L.length) :
    coeff G L r i ≤ 2*n*n+1 := by
  refine Fin.cases ?_ (fun j => ?_) r
  · exact (twiceCost_le _ _).trans (by omega)
  · simp [coeff,column]; split_ifs <;> omega

theorem emit_len {n : ℕ} (L : SparseWeights n) (w : Fin L.length → ℚ) :
    (emit L w).length = (active w).card := by
  let ix := (List.finRange L.length).filter (fun i => decide (0<w i))
  have h : ix.toFinset = active w := by ext i; simp [ix,active]
  have hdup : ix.Nodup := (List.nodup_finRange _).filter _
  simpa only [emit,List.length_map,←h] using (List.toFinset_card_of_nodup hdup).symm

theorem emit_shape {n : ℕ} (L : SparseWeights n) (hL : ValidSupport L) (w : Fin L.length → ℚ) :
    ((emit L w).map Prod.fst).Nodup ∧ ∀ e∈emit L w, 0 < e.2 := by
  constructor
  · have h := ((List.filter_sublist (p:=fun i : Fin L.length => decide (0<w i)) (l:=List.finRange L.length))).map (fun i => (L.get i).1)
    have hs : ((List.finRange L.length).map (fun i => (L.get i).1)).Nodup := by
      have hmap := congrArg (List.map Prod.fst) (List.map_get_finRange L)
      simp only [List.map_map,Function.comp_def] at hmap
      rw [hmap]; exact hL.1
    simpa only [emit,List.map_map,Function.comp_def] using h.nodup hs
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    simpa using (List.mem_filter.mp hi).2

private theorem sums_weightAt {n : ℕ} (L : SparseWeights n) (f : Finset (Fin n) → ℝ) :
    (∑ S, f S * (weightAt L S : ℝ)) = (L.map (fun e => f e.1 * e.2)).sum := by
  induction L with
  | nil => simp [weightAt]
  | cons e l ih =>
    have hS (S : Finset (Fin n)) : weightAt (e::l) S = (if e.1=S then e.2 else 0)+weightAt l S := rfl
    simp only [hS,Rat.cast_add,mul_add,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons]
    congr 1
    simp only [apply_ite (fun x : ℚ => (x : ℝ)),Rat.cast_zero,mul_ite,mul_zero,Finset.sum_ite_eq,
      Finset.mem_univ,if_true]

theorem list_total {n : ℕ} (L : SparseWeights n) (f : Finset (Fin n) → ℝ) :
    (∑ S, f S * (weightAt L S : ℝ)) =
      ∑ i : Fin L.length, f (L.get i).1 * ((L.get i).2 : ℝ) := by
  rw [sums_weightAt,←List.sum_ofFn]
  change (L.map _).sum = _
  congr 1
  have h := congrArg (List.map (fun e => f e.1 * (e.2 : ℝ))) (List.map_get_finRange L)
  simpa only [List.map_map,Function.comp_def,List.ofFn_eq_map] using h.symm

theorem emit_total {n : ℕ} (L : SparseWeights n) (w : Fin L.length → ℚ) (hw : ∀ i, 0≤w i)
    (f : Finset (Fin n) → ℝ) :
    (∑ S, f S * (weightAt (emit L w) S : ℝ)) =
      ∑ i : Fin L.length, f (L.get i).1 * (w i : ℝ) := by
  rw [sums_weightAt]
  simp only [emit,List.map_map,Function.comp_def]
  rw [←List.sum_ofFn,List.ofFn_eq_map]
  generalize List.finRange L.length = xs
  induction xs with
  | nil => simp
  | cons i xs ih =>
    by_cases h : 0<w i
    · simpa [h] using ih
    · have h0 := le_antisymm (le_of_not_gt h) (hw i)
      simpa [h,h0] using ih

theorem compress_primal {n : ℕ} (G : Graph n) (L : SparseWeights n) (hL : ValidSupport L) :
    ValidSupport (compress G L) ∧ (compress G L).length ≤ n+1 ∧
    primalValue G (fun S => (weightAt (compress G L) S : ℝ)) =
      primalValue G (fun S => (weightAt L S : ℝ)) := by
  let f := indexWeights L
  have hf (i : Fin L.length) : 0 ≤ f i := (hL.2.1 _ (List.get_mem L i)).le
  let z := run (coeff G L) (2*n*n+1) L.length f
  obtain ⟨hz,hcard,hm⟩ := compress_correct (coeff G L) (coeff_le G L) f hf
  obtain ⟨hn,hp⟩ := emit_shape L hL z
  have hnon (S) : 0 ≤ (weightAt (emit L z) S : ℝ) := by
    apply Rat.cast_nonneg.mpr
    unfold weightAt
    apply List.sum_nonneg
    intro a ha; obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    split <;> first | exact (hp _ he).le | exact le_rfl
  have hlin (r : Fin (n+1)) :
      (∑ S, (column G S r : ℝ) * (weightAt (emit L z) S : ℝ)) =
        ∑ S, (column G S r : ℝ) * (weightAt L S : ℝ) := by
    rw [emit_total L z hz,list_total]
    have eq : moment (coeff G L) z r = moment (coeff G L) f r := hm r
    have hh := congrArg (fun a : ℚ => (a:ℝ)) eq
    simp only [moment,coeff,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast] at hh
    calc
      _ = ∑ i : Fin L.length, (z i : ℝ) * ↑(column G (L.get i).1 r) := by apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _
      _ = _ := hh.trans (by apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _)
  refine ⟨⟨hn,hp,hnon,?_⟩,?_,?_⟩
  · intro i
    have h := hlin i.succ
    simp only [column,Fin.cases_succ,apply_ite (fun a : ℕ => (a:ℝ)),
      Nat.cast_one,Nat.cast_zero,ite_mul,one_mul,zero_mul] at h
    exact h.trans (hL.2.2.2 i)
  · exact (emit_len L z).le.trans hcard
  · have h := hlin 0
    simp only [column,Fin.cases_zero,twiceCost_eq,mul_assoc,←Finset.mul_sum] at h
    change (∑ S, subsetCost G S * (weightAt (emit L z) S:ℝ)) = ∑ S, subsetCost G S * (weightAt L S:ℝ)
    linarith

end DualSepClusterLP.Compression

namespace DualSepClusterLP.CutRecovery

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

open Finset

def query {n : ℕ} (V η : ℚ) (Cs : List (Finset (Fin n))) (i : Fin n) : ℚ :=
  V / n - η * (visits Cs i - mean Cs)

def Cuts {n : ℕ} (G : Graph n) (V η : ℚ) : List (Finset (Fin n)) → Prop
  | [] => True
  | S::Cs => Cuts G V η Cs ∧ subsetCost G S < ∑ i ∈ S, (query V η Cs i : ℝ)

private def bit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ S then 1 else 0

private theorem bit_sum {n : ℕ} (S : Finset (Fin n)) : (∑ i, bit S i) = S.card := by
  simp [bit]

private theorem bit_time {n : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n)) :
    (∑ i, f i * bit S i) = ∑ i ∈ S, f i := by
  simp [bit,mul_ite]

private theorem visits_consR {n : ℕ} (Cs : List (Finset (Fin n))) (S : Finset (Fin n)) (i : Fin n) :
    (visits (S::Cs) i : ℝ) = (visits Cs i : ℝ) + bit S i := by
  by_cases h : i∈S <;> simp [visits,bit,h,add_comm]

private theorem mean_sum {n : ℕ} (Cs : List (Finset (Fin n))) :
    (mean Cs : ℝ) = (∑ i, (visits Cs i : ℝ))/n := by simp [mean]

private theorem mean_consR {n : ℕ} (Cs : List (Finset (Fin n))) (S : Finset (Fin n)) :
    (mean (S::Cs) : ℝ) = (mean Cs : ℝ) + S.card/(n:ℝ) := by
  simp only [mean_sum,visits_consR,Finset.sum_add_distrib,bit_sum,add_div]

private def delta {n : ℕ} (Cs : List (Finset (Fin n))) (i : Fin n) : ℝ :=
  (visits Cs i : ℝ) - (mean Cs : ℝ)

private theorem centered {n : ℕ} (hn : 0<n) (Cs : List (Finset (Fin n))) :
    ∑ i, delta Cs i = 0 := by
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simp [delta,Finset.sum_sub_distrib,mean_sum,nsmul_eq_mul,hn',mul_div_cancel₀,
    mul_div_cancel_left₀]

private theorem cross {n : ℕ} (hn : 0<n) (Cs : List (Finset (Fin n))) (S : Finset (Fin n)) :
    (∑ i, delta Cs i * (bit S i - S.card/(n:ℝ))) = ∑ i ∈ S, delta Cs i := by
  simp only [mul_sub,sum_sub_distrib,←sum_mul,bit_time,centered hn,zero_mul,sub_zero]

private theorem squareBound {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) :
    (∑ i, (bit S i-S.card/(n:ℝ))^2) ≤ n := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  let a := (S.card:ℝ)/n
  have hbits (i : Fin n) : (bit S i-a)^2 = bit S i - bit S i*(2*a) + a^2 := by
    by_cases h : i∈S <;> simp [bit,h] <;> ring
  change (∑ i, (bit S i-a)^2) ≤ _
  simp_rw [hbits]
  simp only [sum_add_distrib,sum_sub_distrib,←sum_mul,bit_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hid : (n:ℝ)*a = S.card := by dsimp [a]; field_simp
  have hs : (S.card:ℝ)≤n := by exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
  have hpos : 0≤(n:ℝ)*a^2 := mul_nonneg hn'.le (sq_nonneg a)
  nlinarith [congrArg (fun t : ℝ => t*a) hid]

private theorem energyChange {n : ℕ} (hn : 0<n) (Cs : List (Finset (Fin n))) (S : Finset (Fin n)) :
    (∑ i, (delta (S::Cs) i)^2) ≤ (∑ i, (delta Cs i)^2) + 2*(∑ i∈S, delta Cs i) + n := by
  have hi (i : Fin n) : (delta (S::Cs) i)^2 = (delta Cs i)^2 +
      2*(delta Cs i*(bit S i-S.card/(n:ℝ))) + (bit S i-S.card/(n:ℝ))^2 := by
    simp only [delta,visits_consR,mean_consR]; ring
  simp_rw [hi]
  simp only [sum_add_distrib,←mul_sum,cross hn]
  linarith [squareBound hn S]

theorem query_sum {n : ℕ} (hn : 0<n) (V η : ℚ) (Cs : List (Finset (Fin n))) :
    (∑ i, (query V η Cs i : ℝ)) = V := by
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  change (∑ i, (((V / n - η * (visits Cs i-mean Cs)) : ℚ):ℝ)) = _
  push_cast
  change (∑ i, ((V:ℝ)/n-(η:ℝ)*delta Cs i))=_
  simp [sum_sub_distrib,←mul_sum,centered hn,nsmul_eq_mul]
  field_simp

private theorem query_set {n : ℕ} (V η : ℚ) (Cs : List (Finset (Fin n))) (S : Finset (Fin n)) :
    (∑ i∈S, (query V η Cs i:ℝ)) = V*(S.card/(n:ℝ)) - η*(∑ i∈S,delta Cs i) := by
  simp only [query,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,
    sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,delta]
  ring

theorem telescope {n : ℕ} (hn : 0<n) (G : Graph n) (V η : ℚ) (hη : 0≤η)
    (Cs : List (Finset (Fin n))) (hc : Cuts G V η Cs) :
    cost G Cs ≤ V*(mean Cs : ℝ) + η*n*Cs.length/2 -
      η/2 * ∑ i, ((visits Cs i : ℝ)-(mean Cs : ℝ))^2 := by
  change _ ≤ _ - _ * ∑ i, (delta Cs i)^2
  induction Cs with
  | nil => simp [cost,delta,mean,visits]
  | cons S Cs ih =>
    obtain ⟨ok,cut⟩ := hc
    have prev := ih ok
    rw [query_set] at cut
    have ht := mul_le_mul_of_nonneg_left (energyChange hn Cs S)
      (by exact_mod_cast hη : (0:ℝ)≤η)
    rw [mean_consR,List.length_cons, Nat.cast_add_one]
    change subsetCost G S + cost G Cs ≤ _
    linarith

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

theorem search_spec {n : ℕ} (hn : 0<n) (G : Graph n) (t : ℕ) (o : Oracle n) (ho : goodOracle t G o)
    (V η : ℚ) (f : ℕ) (Cs : List (Finset (Fin n))) (hc : Cuts G V η Cs) :
    match search o V η f Cs with
    | .inl q => DualFeasible G (fun i => (q i : ℝ)/(1+(tolerance t : ℝ))) ∧ (∑ i, (q i : ℝ))=V
    | .inr xs => Cuts G V η xs ∧ xs.length = f + Cs.length := by
  induction f generalizing Cs with
  | zero => exact ⟨hc,(Nat.zero_add _).symm⟩
  | succ f ih =>
    have h := ho (prices V η Cs)
    cases he : o (prices V η Cs) with
    | none =>
      rw [he] at h
      simp only [search,he]; exact ⟨h,query_sum hn V η Cs⟩
    | some S =>
      rw [he] at h
      have hh := ih (S::Cs) ⟨hc,h⟩
      simp only [search,he]
      cases hs : search o V η f (S::Cs) with
      | inl q => simpa only [hs] using hh
      | inr xs =>
        rw [hs] at hh
        exact ⟨hh.1, by have hh' := hh.2; simp only [List.length_cons] at hh'; omega⟩

theorem cuts_nonempty {n : ℕ} (G : Graph n) (V η : ℚ) (Cs : List (Finset (Fin n)))
    (hc : Cuts G V η Cs) : ∀ S∈Cs, S.Nonempty := by
  induction Cs with
  | nil => simp
  | cons S Cs ih =>
    obtain ⟨hr,hS⟩ := hc
    intro U hu
    rcases List.mem_cons.mp hu with rfl | h
    · by_contra he; rw [Finset.not_nonempty_iff_eq_empty.mp he] at hS
      simp only [Finset.sum_empty] at hS
      exact (Master.cost_nonneg G _).not_gt hS
    · exact ih hr U h

theorem scale_pos (t : ℕ) : 0 < scaleIndex t := by unfold scaleIndex; omega

theorem tol_pos (t : ℕ) : 0 < tolerance t := by
  have h := scale_pos t
  unfold tolerance
  positivity

theorem rate_pos (t n : ℕ) : 0 < rate t n := by
  have h := scale_pos t
  unfold rate; positivity

theorem limit_pos (t n : ℕ) : 0 < cutLimit t n := by
  have h := scale_pos t
  unfold cutLimit; positivity

theorem error_budget (t n : ℕ) :
    (rate t n:ℝ)*n^2/2 + 2*(n:ℝ)^5 / ((rate t n:ℝ)*(cutLimit t n:ℝ)) ≤ (tolerance t:ℝ) := by
  let k : ℝ := scaleIndex t
  have hk : 0<k := by dsimp [k]; exact_mod_cast scale_pos t
  have hN : 0 < (n:ℝ)+1 := by positivity
  have hnn : (n:ℝ) ≤ n+1 := by linarith
  have h2 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤n) hnn 2
  have h5 := pow_le_pow_left₀ (by positivity : (0:ℝ)≤n) hnn 5
  simp only [rate,cutLimit,tolerance,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_add,Rat.cast_natCast,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  change (1/(k*(n+1)^2))*(n:ℝ)^2/2 + 2*(n:ℝ)^5/((1/(k*(n+1)^2))*(4*k^2*(n+1)^7)) ≤ 1/k
  have a : (1/(k*(n+1)^2))*(n:ℝ)^2/2 ≤ 1/k/2 := by
    calc
      _ ≤ (1/(k*(n+1)^2))*(n+1)^2/2 := by gcongr
      _ = _ := by field_simp
  have b : 2*(n:ℝ)^5/((1/(k*(n+1)^2))*(4*k^2*(n+1)^7)) ≤ 1/k/2 := by
    calc
      _ ≤ 2*((n:ℝ)+1)^5/((1/(k*(n+1)^2))*(4*k^2*(n+1)^7)) := by gcongr
      _ = _ := by field_simp; ring
  linarith

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

open Finset

theorem recovered_bound {n : ℕ} (G : Graph n) (Cs : List (Finset (Fin n)))
    (hn : 0<n) (hT : Cs ≠ []) (nonempty : ∀ S∈Cs, S.Nonempty)
    (V η : ℝ) (hV : 0 ≤ V) (hη : 0 < η)
    (hc : cost G Cs ≤ V*(mean Cs:ℝ)+η*n*Cs.length/2-
      η/2*∑ i : Fin n, ((visits Cs i:ℝ)-(mean Cs:ℝ))^2) :
    ValidSupport (make Cs) ∧ (make Cs).length ≤ Cs.length+n ∧
    primalValue G (fun S => (weightAt (make Cs) S : ℝ)) ≤ V + η*n^2/2 + 2*(n:ℝ)^5/(η*Cs.length) := by
  have hM := peak_pos Cs hT nonempty
  refine ⟨valid_make Cs hM,length_make Cs,?_⟩
  let m : ℝ := peak Cs
  let d : ℝ := mean Cs
  let T : ℝ := Cs.length
  let N : ℝ := n
  have hm : 0 < m := by dsimp [m]; exact_mod_cast hM
  have ht : 0 < T := by dsimp [T]; exact_mod_cast List.length_pos_iff.mpr hT
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hsum : (∑ i : Fin n, (visits Cs i : ℝ)) = N*d := by
    change _ = (n:ℝ)*((mean Cs:ℚ):ℝ)
    simp only [mean,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
    field_simp
  have hvmax (i : Fin n) : (visits Cs i : ℝ) ≤ m := by dsimp [m]; exact_mod_cast visits_le_peak Cs i
  have hdm : d ≤ m := by
    apply le_of_mul_le_mul_left _ hN
    rw [←hsum]
    exact (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => hvmax i)).trans_eq
      (by simp [N])
  have htn : T ≤ N*m := by
    have h := visits_lower Cs nonempty
    have hh : T ≤ (∑ i : Fin n,(visits Cs i:ℝ)) := by dsimp [T]; exact_mod_cast h
    rw [hsum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hdm hN.le)
  have hs : ∑ i : Fin n, subsetCost G {i} * (m-(visits Cs i:ℝ)) ≤ N^2*(m-d) := by
    calc
      _ ≤ ∑ i : Fin n, N * (m-(visits Cs i:ℝ)) := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_right (singleton_cost G i) (sub_nonneg.mpr (hvmax i)))
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib,hsum]; simp [N]; ring
  obtain ⟨k,hk⟩ := peak_index Cs hM
  have hsquares : (m-d)^2 ≤ ∑ i : Fin n, ((visits Cs i:ℝ)-d)^2 := by
    have e : (visits Cs k:ℝ) = m := by dsimp [m]; exact_mod_cast hk
    rw [←e]
    exact Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => sq_nonneg ((visits Cs i:ℝ)-d)) (Finset.mem_univ k)
  have msq := mul_le_mul_of_nonneg_left hsquares (show 0≤η/2 by positivity)
  have square : N^2*(m-d)-η/2*(m-d)^2 ≤ N^4/(2*η) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (N^2-η*(m-d))]
  have vc := mul_le_mul_of_nonneg_left hdm hV
  let val := primalValue G (fun S => (weightAt (make Cs) S : ℝ))
  have heq : val*m = cost G Cs + ∑ i, subsetCost G {i}*(m-(visits Cs i:ℝ)) := numerator G Cs hM
  change cost G Cs ≤ V*d+η*N*T/2-η/2*∑ i:Fin n, ((visits Cs i:ℝ)-d)^2 at hc
  have hmul : val*m ≤ V*m + η*N*T/2 + N^4/(2*η) := by linarith
  have he1 : η*N*T/2 ≤ (η*N^2/2)*m := by nlinarith [mul_le_mul_of_nonneg_left htn (show 0≤η*N by positivity)]
  have he2 : N^4/(2*η) ≤ (2*N^5/(η*T))*m := by
    field_simp [hη.ne',ht.ne']
    nlinarith [mul_le_mul_of_nonneg_left htn (show 0 ≤ N^4 by positivity),
      mul_nonneg (show 0 ≤ N^5 by positivity) hm.le]
  change val ≤ V + η*N^2/2 + 2*N^5/(η*T)
  apply le_of_mul_le_mul_right _ hm
  linarith

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

noncomputable abbrev val {n : ℕ} (G : Graph n) (L : SparseWeights n) : ℝ :=
  primalValue G (fun S => (weightAt L S : ℝ))

noncomputable abbrev revenue {n : ℕ} (q : Prices n) : ℝ := ∑ i, (q i : ℝ)

def certified {n : ℕ} (G : Graph n) (q : Prices n) := DualFeasible G (fun i => (q i : ℝ))

theorem level_good {n : ℕ} (hn : 0<n) (G : Graph n) (t j : ℕ) (o : Oracle n) (ho : goodOracle t G o) :
    match search o (levelValue t j) (rate t n) (cutLimit t n) [] with
    | .inl q => certified G (fun i => q i/(1+tolerance t)) ∧
        (1+(tolerance t:ℝ))*revenue (fun i => q i/(1+tolerance t)) = (levelValue t j:ℝ)
    | .inr Cs => ValidSupport (make Cs) ∧ (make Cs).length ≤ cutLimit t n+n ∧
        val G (make Cs) ≤ (levelValue t j:ℝ) + (tolerance t:ℝ) := by
  let V := levelValue t j
  let η := rate t n
  have hh := search_spec hn G t o ho V η (cutLimit t n) [] (by trivial)
  change match search o V η _ [] with | .inl q => _ | .inr Cs => _
  cases he : search o V η (cutLimit t n) [] with
  | inl q =>
    rw [he] at hh
    refine ⟨?_,?_⟩
    · simpa only [certified,Rat.cast_div,Rat.cast_add,Rat.cast_one] using hh.1
    · have hpos : (0:ℝ)<tolerance t := by exact_mod_cast tol_pos t
      have hd : (1+(tolerance t:ℝ)) ≠ 0 := by linarith
      simp only [revenue,Rat.cast_div,Rat.cast_add,Rat.cast_one,←Finset.sum_div]
      rw [hh.2]
      field_simp
      rfl
  | inr Cs =>
    rw [he] at hh
    have len : Cs.length = cutLimit t n := by simpa using hh.2
    have hne : Cs ≠ [] := List.length_pos_iff.mp (len ▸ limit_pos t n)
    have hη := rate_pos t n
    have hV : 0≤V := by dsimp [V,levelValue]; have h:=tol_pos t; positivity
    have hb := recovered_bound G Cs hn hne (cuts_nonempty G V η Cs hh.1) V η
      (by exact_mod_cast hV) (by exact_mod_cast hη) (telescope hn G V η hη.le Cs hh.1)
    obtain ⟨ha,hb,hc⟩ := hb
    rw [len] at hb hc
    refine ⟨ha,hb,?_⟩
    have h := error_budget t n
    change _ ≤ (V:ℝ) + _
    change _ ≤ (V:ℝ) + (rate t n:ℝ)*n^2/2 + _ at hc
    linarith

theorem grid_good {n : ℕ} (hn : 0<n) (G : Graph n) (t : ℕ) (o : Oracle n) (ho : goodOracle t G o) (j : ℕ) :
    match grid t o j with
    | .inl q => certified G q ∧ (1+(tolerance t:ℝ)) * revenue q = (levelValue t j:ℝ)
    | .inr (L,q) => ValidSupport L ∧ L.length ≤ cutLimit t n + n ∧ certified G q ∧
        val G L ≤ (1+(tolerance t:ℝ))*revenue q+2*(tolerance t:ℝ) := by
  induction j with
  | zero =>
    constructor
    · intro S; simpa using Master.cost_nonneg G S
    · simp [levelValue,revenue]
  | succ j ih =>
    rw [grid]
    cases he : grid t o j with
    | inr ans => simpa only [he] using ih
    | inl prev =>
      rw [he] at ih
      have h := level_good hn G t (j+1) o ho
      cases hh : search o (levelValue t (j+1)) (rate t n) (cutLimit t n) [] with
      | inl q => simpa only [hh] using h
      | inr Cs =>
        rw [hh] at h
        refine ⟨h.1,h.2.1,ih.1,?_⟩
        have heq : (levelValue t (j+1) : ℝ) = (levelValue t j:ℝ)+(tolerance t:ℝ) := by
          simp [levelValue,add_mul]
        rw [ih.2]
        linarith [h.2.2]

end DualSepClusterLP.CutRecovery

namespace DualSepClusterLP.CutRecovery

private theorem nonempty_n {n : ℕ} {G : Graph n} (h : ¬Master.EquivalenceGraph G) : 0<n := by
  by_contra! hn; obtain rfl := Nat.eq_zero_of_le_zero hn
  exact h (fun i => Fin.elim0 i)

private theorem cap_impossible {n : ℕ} (G : Graph n) (t : ℕ) (q : Prices n) (hg : certified G q)
    (he : (1+(tolerance t:ℝ))*revenue q=(levelValue t (levels t n):ℝ)) : False := by
  have ub := (Master.dual_le_opt G hg).trans (opt_upper G)
  change revenue q ≤ _ at ub
  have ht : 0 < (scaleIndex t:ℝ) := by exact_mod_cast scale_pos t
  have hk : 1 ≤ (scaleIndex t:ℝ) := by exact_mod_cast scale_pos t
  have hspan : (levelValue t (levels t n):ℝ) = 2*((n:ℝ)+1)^2 := by
    simp [levelValue,levels,tolerance]; field_simp
  have heps : (tolerance t : ℝ) ≤ 1 := by simp only [tolerance,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]; exact (div_le_one ht).2 hk
  have ht' : (0:ℝ)<tolerance t := by exact_mod_cast tol_pos t
  have hpos : 0≤(1+(tolerance t:ℝ)) := by linarith
  have hprod := (mul_le_mul_of_nonneg_left ub hpos).trans (mul_le_mul_of_nonneg_right
    (show (1+(tolerance t:ℝ))≤2 by linarith) (sq_nonneg (n:ℝ)))
  rw [he,hspan] at hprod
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

private theorem multiplicative (t : ℕ) (v q : ℝ) (hv : 1≤v)
    (h : v≤(1+(tolerance t:ℝ))*q+2*(tolerance t:ℝ)) :
    v≤ (1 + 1/((t:ℝ)+1))*q := by
  let δ : ℝ := tolerance t
  have hd : 0<δ := by dsimp [δ]; exact_mod_cast tol_pos t
  have hmax : δ≤1/8 := by
    change (tolerance t:ℝ) ≤ (1:ℝ)/8
    simp only [tolerance,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast (show 8 ≤ scaleIndex t by unfold scaleIndex; omega)
  have rhs : 1/((t:ℝ)+1)=8*δ := by
    simp [δ,tolerance,scaleIndex]; field_simp
  change v≤(1+δ)*q+2*δ at h
  have hq : (1:ℝ)/2≤q := by
    by_contra! hn
    have hc := mul_lt_mul_of_pos_left hn (show 0<1+δ by positivity)
    linarith
  have e := mul_le_mul_of_nonneg_left hq hd.le
  rw [rhs]
  linarith

theorem untrimmed_good {n : ℕ} (G : Graph n) (t : ℕ) (o : Oracle n) (ho : goodOracle t G o) :
    let (L,q) := untrimmed G t o
    ValidSupport L ∧ L.length≤cutLimit t n+n ∧ certified G q ∧
      val G L ≤ (1+1/((t:ℝ)+1))*revenue q := by
  unfold untrimmed
  by_cases hG : Master.EquivalenceGraph G
  · rw [if_pos hG]
    obtain ⟨hf,hl,hv⟩ := Master.zeroList_ok hG
    refine ⟨hf,by omega,fun S => ?_,?_⟩
    · simpa using Master.cost_nonneg G S
    · simp [val,hv,revenue]
  · rw [if_neg hG]
    have hg := grid_good (nonempty_n hG) G t o ho (levels t n)
    cases h : grid t o (levels t n) with
    | inl q =>
      rw [h] at hg
      exact (cap_impossible G t q hg.1 hg.2).elim
    | inr ans =>
      rcases ans with ⟨L,q⟩
      rw [h] at hg
      exact ⟨hg.1,hg.2.1,hg.2.2.1,multiplicative t _ _ ((Master.unit_le_opt hG).trans
        (Master.opt_le G hg.1.2.2)) hg.2.2.2⟩

theorem solve_good {n : ℕ} (G : Graph n) (t : ℕ) (o : Oracle n) (ho : goodOracle t G o) :
    let (L,q) := solve G t o
    ValidSupport L ∧ L.length ≤ 257*(n+1)^9 ∧ certified G q ∧
      Master.opt G ≤ (1+1/((t:ℝ)+1))*revenue q ∧
      val G L ≤ (1+1/((t:ℝ)+1))*Master.opt G := by
  have h := untrimmed_good G t o ho
  unfold solve
  generalize hp : untrimmed G t o = ans at *
  rcases ans with ⟨L,q⟩
  obtain ⟨hv,hlen,hq,hgap⟩ := h
  have hz := Master.sandwich G hv.2.2 hq (by positivity : (0:ℝ)≤1+1/((t:ℝ)+1)) hgap
  dsimp only
  by_cases ht : n≤t
  · rw [if_pos ht]
    obtain ⟨hv',hl,he⟩ := Compression.compress_primal G L hv
    refine ⟨hv',?_,hq,hz.1,he.trans_le hz.2⟩
    have hh : n+1≤(n+1)^9 := Nat.le_self_pow (by decide) _
    omega
  · rw [if_neg ht]
    refine ⟨hv,?_,hq,hz.1,hz.2⟩
    have hh : t+1≤n+1 := by omega
    have hlim : cutLimit t n ≤ 256*(n+1)^9 := by
      unfold cutLimit scaleIndex
      calc
        _ ≤ 4*(8*(n+1))^2*(n+1)^7 := by gcongr
        _ = _ := by ring
    have hh' : n+1≤(n+1)^9 := Nat.le_self_pow (by decide) _
    omega

end DualSepClusterLP.CutRecovery

open DualSepClusterLP

theorem solution {n : ℕ} (G : Graph n) (t : ℕ) (o : CutRecovery.Oracle n)
    (ho : CutRecovery.goodOracle t G o) :
    let (L,q) := CutRecovery.solve G t o
    let opt : ℝ := sInf {v : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = v}
    let factor : ℝ := 1+1/((t:ℝ)+1)
    ValidSupport L ∧ L.length ≤ 257*(n+1)^9 ∧ DualFeasible G (fun i => (q i : ℝ)) ∧
      opt ≤ factor * ∑ i, (q i : ℝ) ∧
      primalValue G (fun S => (weightAt L S : ℝ)) ≤ factor * opt := CutRecovery.solve_good G t o ho
