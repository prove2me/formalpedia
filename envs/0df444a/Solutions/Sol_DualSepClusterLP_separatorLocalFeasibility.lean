-- Prove2me | solution 1 for DualSepClusterLP.separatorLocalFeasibility
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T14:48:36.317182+00:00
-- url     : https://prove2.me/submissions/5009432e-5710-416b-bb32-40e748976f2b

import Definitions.Def_DualSepClusterLP_SeparationChecks


section
namespace DualSepClusterLP.SepStructure
open Finset
def edges {n : ℕ} (G : Graph n) (A B : Finset (Fin n)) := ∑ v∈A, degree G B v
@[simp] theorem edge_diag {n : ℕ} (G : Graph n) (i : Fin n) : edge G i i = false := by simp [edge]
theorem edge_symm {n : ℕ} (G : Graph n) (i j : Fin n) : edge G i j = edge G j i := by
  rcases lt_trichotomy i j with h|rfl|h
  · simp [edge,h,not_lt_of_ge h.le]
  · rfl
  · simp [edge,h,not_lt_of_ge h.le]
def discrepancy {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (v : Fin n) :=
  ((closed G v \ S) ∪ (S \ closed G v)).card
def gap {n : ℕ} (G : Graph n) (q : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n)) : Prop :=
  (1+ε)*subsetCost G S < ∑ v∈S,q v
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
private def hit {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if i∈S ∧ (j ∈ closed G i ↔ j∉S) then 1 else 0
private theorem upper {n : ℕ} (f : Fin n → Fin n → ℝ) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, if i<j then f i j+f j i else 0) = ∑ i, ∑ j, f i j := by
  have hs : (∑ i, ∑ j, if i<j then f j i else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0 := Finset.sum_comm
  simp_rw [ite_add_zero,Finset.sum_add_distrib]
  rw [hs,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rcases lt_trichotomy i j with h|rfl|h
  · simp [h,not_lt_of_ge h.le]
  · simp [hd]
  · simp [h,not_lt_of_ge h.le]
theorem discrepancy_sum {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    (∑ v∈S, (discrepancy G S v : ℝ)) = 2*subsetCost G S := by
  classical
  have hd (i : Fin n) : hit G S i i = 0 := by
    by_cases h : i∈S <;> simp [hit,h,closed]
  have hu := upper (hit G S) hd
  have hr : 2*subsetCost G S = ∑ i,∑ j, if i<j then hit G S i j + hit G S j i else 0 := by
    unfold subsetCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : i < j
    · have hji := not_lt_of_ge hj.le
      cases e : G i j <;> by_cases a : i∈S <;> by_cases b : j∈S <;>
        norm_num [hj,hji,hit,closed,neighbors,edge,hj.ne,hj.ne',e,a,b]
    · simp [hj]
  rw [hr,hu]
  rw [← Finset.sum_subset (show S ⊆ Finset.univ from Finset.subset_univ S)]
  · apply Finset.sum_congr rfl; intro v hv
    let D := (closed G v \ S) ∪ (S \ closed G v)
    have hD : (∑ j, if j∈D then (1:ℝ) else 0) = (D.card:ℝ) := by simp
    change (D.card:ℝ) = _
    rw [←hD]
    apply Finset.sum_congr rfl; intro j _
    by_cases hx : j∈closed G v <;> by_cases hy : j∈S <;> simp [D,hit,hv,hx,hy]
  · intro v _ h
    simp [hit,h]
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
theorem cost_nonneg {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : 0 ≤ subsetCost G S := by
  have h : 0 ≤ ∑ v∈S, (discrepancy G S v:ℝ) := by positivity
  rw [discrepancy_sum] at h
  linarith
theorem pos_cost_half {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (h : 0<subsetCost G S) :
    1 ≤ 2*subsetCost G S := by
  have e : ((∑ v∈S, discrepancy G S v : ℕ):ℝ) = 2*subsetCost G S := by
    push_cast; exact discrepancy_sum G S
  rw [←e]
  have hp : (0:ℝ) < ((∑ v∈S, discrepancy G S v : ℕ):ℝ) := by rw [e]; linarith
  exact_mod_cast (show 1 ≤ ∑ v∈S, discrepancy G S v from by exact_mod_cast hp)
theorem closed_of_zero {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (h : subsetCost G S=0)
    (v : Fin n) (hv : v∈S) : closed G v=S := by
  have ht := discrepancy_sum G S
  rw [h,mul_zero] at ht
  have hn := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈S) => Nat.cast_nonneg (α:=ℝ)
    (discrepancy G S i))).mp ht v hv
  have hd : discrepancy G S v = 0 := by exact_mod_cast hn
  rw [discrepancy,Finset.card_eq_zero,Finset.union_eq_empty] at hd
  exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hd.1)
    (Finset.sdiff_eq_empty_iff_subset.mp hd.2)
theorem gap_nonempty {n : ℕ} {G : Graph n} {q : Fin n → ℝ} {ε : ℝ} {S : Finset (Fin n)}
    (h : gap G q ε S) : S.Nonempty := by
  by_contra! he
  have h0 : subsetCost G (∅:Finset (Fin n))=0 := by
    have ht := discrepancy_sum G (∅:Finset (Fin n)); simp at ht; exact ht
  simp [gap,he,h0] at h
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
theorem feasible_iff_no_gap {n : ℕ} (G : Graph n) (q : Fin n → ℝ) (ε : ℝ) (hε : 0≤ε) :
    DualFeasible G (fun i => q i/(1+ε)) ↔ ¬∃ S, gap G q ε S := by
  have h : 0 < 1+ε := by linarith
  rw [not_exists]
  unfold DualFeasible gap
  simp only [←Finset.sum_div,div_le_iff₀ h,not_lt]
  simp only [mul_comm (1+ε)]
theorem zero_cost_witness {n : ℕ} (G : Graph n) (q : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n))
    (hS : gap G q ε S) (hc : subsetCost G S=0) :
    ∃ v∈S, subsetCost G (closed G v) < ∑ j∈closed G v,q j := by
  obtain ⟨v,hv⟩ := gap_nonempty hS
  refine ⟨v,hv,?_⟩
  rw [closed_of_zero G S hc v hv,hc]
  simpa only [gap,hc,mul_zero] using hS
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
private noncomputable def term {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if i<j then if G i j then
    (if decide (i∈S) != decide (j∈S) then 1/2 else 0)
    else (if i∈S ∧ j∈S then 1 else 0) else 0
private theorem single_pair {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) :
    (∑ v∈S, term G {v} i j) ≤ term G S i j +
      (if i<j ∧ i∈S ∧ j∈S then (1:ℝ) else 0) := by
  by_cases h : i<j
  · cases p : G i j
    · have he (v : Fin n) : term G {v} i j = 0 := by
        simp [term,h,p]; intro hi; subst v; exact Ne.symm h.ne
      simp only [he,Finset.sum_const_zero]
      unfold term; split_ifs <;> norm_num
    · have he (v : Fin n) : term G {v} i j =
          (if v=i then (1:ℝ)/2 else 0)+(if v=j then 1/2 else 0) := by
        by_cases a : v=i
        · subst v; simp [term,h,p,h.ne,h.ne']
        · by_cases b : v=j
          · subst v; simp [term,h,p,h.ne,h.ne']
          · simp [term,h,p,a,b,Ne.symm a,Ne.symm b]
      simp only [he,Finset.sum_add_distrib,Finset.sum_ite_eq']
      by_cases a : i∈S <;> by_cases b : j∈S <;> norm_num [term,h,p,a,b]
  · simp [term,h]
private theorem sum_lt {n : ℕ} (S : Finset (Fin n)) :
    (∑ i∈S, ∑ j∈S, if i<j then (1:ℝ) else 0) =
      (S.card:ℝ)*((S.card:ℝ)-1)/2 := by
  let T := ∑ i∈S, ∑ j∈S, if i<j then (1:ℝ) else 0
  have hs : (∑ i ∈ S, ∑ j ∈ S, if j < i then (1:ℝ) else 0) = T := Finset.sum_comm
  have h (i : Fin n) (hi : i∈S) :
      (∑ j∈S, if i≠j then (1:ℝ) else 0) = S.card-1 := by
    calc
      _ = ∑ j∈S, ((1:ℝ) - (if j=i then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro j _
        by_cases a : j=i <;> simp [a,Ne.symm]
      _ = _ := by simp [Finset.sum_sub_distrib,hi]
  have hn : (∑ i∈S, ∑ j∈S, if i≠j then (1:ℝ) else 0) = S.card*(S.card-1) := by
    calc
      _ = ∑ i∈S, ((S.card:ℝ)-1) := Finset.sum_congr rfl h
      _ = _ := by simp; ring
  have hp (i j : Fin n) : (if i≠j then (1:ℝ) else 0) =
      (if i<j then 1 else 0)+(if j < i then 1 else 0) := by
    rcases lt_trichotomy i j with h|h|h
    · simp [h,h.ne,not_lt_of_ge h.le]
    · simp [h]
    · simp [h,h.ne',not_lt_of_ge h.le]
  simp_rw [hp,Finset.sum_add_distrib] at hn
  rw [hs] at hn
  dsimp [T] at *
  linarith
theorem singleton_sum {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    (∑ v∈S,subsetCost G {v}) ≤ subsetCost G S + (S.card:ℝ)*((S.card:ℝ)-1)/2 := by
  change (∑ v∈S, ∑ i, ∑ j, term G {v} i j) ≤ (∑ i, ∑ j, term G S i j) + _
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=S) (t:=(Finset.univ:Finset (Fin n)))]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (term G S i j + if i<j ∧ i∈S ∧ j∈S then 1 else 0) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => single_pair G S i j))
    _ = _ := by
      simp only [Finset.sum_add_distrib,add_right_inj]
      rw [←sum_lt]
      calc
        _ = ∑ i : Fin n, if i∈S then ∑ j : Fin n, if j∈S then if i<j then (1:ℝ) else 0 else 0 else 0 := by
          apply Finset.sum_congr rfl; intro i _
          by_cases hi : i∈S
          · simp only [hi,if_true,true_and]
            apply Finset.sum_congr rfl; intro j _
            by_cases hj : j∈S <;> simp [hj]
          · simp [hi]
        _ = _ := by simp
theorem large_cost {n : ℕ} (G : Graph n) (q : Fin n → ℝ) (S : Finset (Fin n)) (ε : ℝ)
    (hcost : (S.card:ℝ)*((S.card:ℝ)-1)/2 ≤ ε*subsetCost G S)
    (hviol : (1+ε)*subsetCost G S < ∑ i∈S, q i) :
    ∃ i∈S, subsetCost G {i} < q i := by
  by_contra! h
  have h' := (Finset.sum_le_sum h).trans (singleton_sum G S)
  linarith
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
variable {n : ℕ} (G : Graph n)
theorem degree_sum (A : Finset (Fin n)) (i : Fin n) :
    degree G A i = ∑ j∈A, if edge G i j then 1 else 0 := by
  have h : (neighbors G i ∩ A) = A.filter (fun j => edge G i j) := by
    ext j; simp [neighbors,and_comm]
  rw [degree,h,Finset.card_filter]
theorem edges_symm (A B : Finset (Fin n)) : edges G A B = edges G B A := by
  simp only [edges,degree_sum]
  rw [sum_comm]; apply sum_congr rfl
  intro i _; apply sum_congr rfl; intro j _; rw [edge_symm G j i]
theorem edges_le (A B : Finset (Fin n)) : edges G A B ≤ A.card*B.card := by
  have hs (i : Fin n) : degree G B i ≤ B.card := card_le_card inter_subset_right
  simpa [edges] using sum_le_sum (s:=A) (f:=degree G B) (g:=fun _ => B.card) (fun i _ => hs i)
theorem edges_split_left (U A B : Finset (Fin n)) (h : A ⊆ U) :
    edges G (U \ A) B + edges G A B = edges G U B := sum_sdiff h
theorem edges_split_right (U A B : Finset (Fin n)) (h : A ⊆ U) :
    edges G B (U \ A) + edges G B A = edges G B U := by
  simpa only [edges_symm G B] using edges_split_left G U A B h
theorem disc_counts (S : Finset (Fin n)) (i : Fin n) (hi : i∈S) :
    discrepancy G S i + 2*degree G S i + 1 = S.card+degree G univ i := by
  have hni : i∉neighbors G i := by simp [neighbors]
  have he : closed G i ∩ S = insert i (neighbors G i ∩ S) := by ext j; by_cases h : j=i <;> simp [closed,h,hi]
  have hd : Disjoint (closed G i \ S) (S \ closed G i) := Finset.disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1)
  have h1 := card_sdiff_add_card_inter (closed G i) S
  have h2 := card_sdiff_add_card_inter S (closed G i)
  rw [inter_comm S,he,card_insert_of_notMem (by simp [hni])] at h2
  have hc : (closed G i).card = (neighbors G i).card+1 := card_insert_of_notMem hni
  rw [he,card_insert_of_notMem (by simp [hni]),hc] at h1
  simp only [discrepancy,card_union_of_disjoint hd,degree,inter_univ]
  omega
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
variable {n : ℕ} (G : Graph n)
theorem cost_quad (S : Finset (Fin n)) :
    2*subsetCost G S = (S.card:ℝ)*((S.card:ℝ)-1)+(edges G S univ:ℝ)-2*(edges G S S:ℝ) := by
  have h := sum_congr (s₁:=S) (s₂:=S) rfl (fun i hi => disc_counts G S i hi)
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one] at h
  have hq := congrArg (fun a : ℕ => (a:ℝ)) h
  push_cast at hq
  rw [discrepancy_sum] at hq
  simp only [edges,Nat.cast_sum]
  nlinarith
theorem cut_mass (S : Finset (Fin n)) : (edges G (univ \ S) S : ℝ) ≤ 2*subsetCost G S := by
  rw [edges_symm,edges,←discrepancy_sum]
  push_cast
  apply sum_le_sum
  intro i hi
  apply Nat.cast_le.mpr
  have hin : neighbors G i ∩ (univ \ S) ⊆ (closed G i \ S) ∪ (S \ closed G i) := by
    intro j hj
    obtain ⟨h1,h2⟩ := mem_inter.mp hj
    exact mem_union_left _ (mem_sdiff.mpr ⟨mem_insert_of_mem h1,(mem_sdiff.mp h2).2⟩)
  exact card_le_card hin
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
private theorem cross_union {n : ℕ} (G : Graph n) (A B T : Finset (Fin n)) (hd : Disjoint A B) :
    edges G (A∪B) T = edges G A T + edges G B T := by simp [edges,sum_union hd]
private theorem union_cross {n : ℕ} (G : Graph n) (A B T : Finset (Fin n)) (hd : Disjoint A B) :
    edges G T (A∪B) = edges G T A + edges G T B := by
  simpa only [edges_symm G T] using cross_union G A B T hd
theorem partition_identity {n : ℕ} (G : Graph n) (A B : Finset (Fin n)) (hd : Disjoint A B) :
    subsetCost G A + subsetCost G B = subsetCost G (A∪B) + 2*(edges G A B:ℝ) - A.card*B.card := by
  have h := cost_quad G (A∪B)
  rw [Finset.card_union_of_disjoint hd,cross_union G A B univ hd,
    cross_union G A B (A∪B) hd,union_cross G A B A hd,union_cross G A B B hd,edges_symm G B A] at h
  push_cast at h
  nlinarith [cost_quad G A,cost_quad G B]
theorem exists_cut_dense_gap {n : ℕ} (G : Graph n) (q : Fin n → ℝ) (ε : ℝ) (hε : 0<ε)
    (h : ∃ S, gap G q ε S) : ∃ S, gap G q ε S ∧
    ∀ A B : Finset (Fin n), Disjoint A B → A∪B=S → A.card*B.card ≤ 2*edges G A B := by
  classical
  let F := univ.filter (gap G q ε)
  have hf : F.Nonempty := by obtain ⟨S,hS⟩ := h; exact ⟨S,by simpa [F] using hS⟩
  obtain ⟨S,hS,hm⟩ := exists_min_image F Finset.card hf
  have hg : gap G q ε S := by simpa [F] using hS
  have hl (T : Finset (Fin n)) (hT : T.card < S.card) :
      (∑ v∈T,q v) ≤ (1+ε)*subsetCost G T := by
    by_contra! hx
    exact (hm T (by simpa [F,gap] using hx)).not_gt hT
  refine ⟨S,hg,?_⟩
  intro A B hdis hab
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · have hh : A.card + B.card = S.card := by rw [←card_union_of_disjoint hdis,hab]
      have xa := ha.card_pos; have xb := hb.card_pos
      have hv := add_le_add (hl A (by omega)) (hl B (by omega))
      rw [←Finset.sum_union hdis,hab,←mul_add] at hv
      have hh' := (mul_lt_mul_iff_right₀ (show 0<1+ε by linarith)).mp (hg.trans_le hv)
      have he := partition_identity G A B hdis
      rw [hab] at he
      have : (A.card:ℝ)*B.card ≤ 2*(edges G A B:ℝ) := by linarith
      exact_mod_cast this
    · simp [Finset.not_nonempty_iff_eq_empty.mp hb]
  · simp [Finset.not_nonempty_iff_eq_empty.mp ha]
theorem exists_dense_gap {n : ℕ} (G : Graph n) (q : Fin n → ℝ) (ε : ℝ) (hε : 0<ε)
    (h : ∃ S, gap G q ε S) : ∃ S, gap G q ε S ∧
    ∀ v∈S, S.card ≤ 2*((closed G v) ∩ S).card := by
  obtain ⟨S,hS,hd⟩ := exists_cut_dense_gap G q ε hε h
  refine ⟨S,hS,?_⟩
  intro v hv
  have h := hd {v} (S.erase v) (by simp) (by simpa using insert_erase hv)
  simp only [card_singleton,one_mul,edges,Finset.sum_singleton] at h
  have he : neighbors G v ∩ S.erase v ⊆ closed G v ∩ S :=
    Finset.inter_subset_inter (by apply subset_insert) (erase_subset v S)
  have hn : v ∉ neighbors G v ∩ S.erase v := by simp
  have hi : v ∈ closed G v ∩ S := by simp [closed,hv]
  have hs := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨he,fun e => hn (e ▸ hi)⟩)
  rw [card_erase_of_mem hv] at h
  unfold degree at h
  omega
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.SepStructure
open Finset
theorem ineligible_bound {n : ℕ} (G : Graph n) (t : ℕ) (S : Finset (Fin n))
    (h : (1/((t:ℝ)+1))*subsetCost G S < (S.card:ℝ)*(S.card-1)/2) :
    100*(S \ eligible G t S.card).card ≤ S.card := by
  classical
  let B := S \ eligible G t S.card
  let s := S.card
  have hn (v : Fin n) (hv : v∈B) : 100*(t+1)*s ≤ discrepancy G S v := by
    have hh := (Finset.mem_sdiff.mp hv).2
    have he : (100*(t+1)+1)*s < (closed G v).card := by simpa [eligible,s] using hh
    have hs : (closed G v).card ≤ (closed G v \ S).card + s := Finset.card_le_card_sdiff_add_card
    have hu : (closed G v \ S).card ≤ discrepancy G S v :=
      Finset.card_le_card Finset.subset_union_left
    rw [Nat.add_mul,one_mul] at he
    omega
  have hm : (B.card:ℝ)*(100*(t+1)*s:ℕ) ≤ 2*subsetCost G S := by
    rw [←discrepancy_sum]
    calc
      _ = ∑ _ ∈ B, ((100*(t+1)*s:ℕ):ℝ) := by simp
      _ ≤ ∑ v ∈ B, (discrepancy G S v:ℝ) := Finset.sum_le_sum (fun v hv => by exact_mod_cast hn v hv)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intros; positivity)
  have ht : 0 < (t:ℝ)+1 := by positivity
  have hC : 2*subsetCost G S < (((s:ℝ)*((s:ℝ)-1)))*((t:ℝ)+1) := by
    change 1/((t:ℝ)+1)*subsetCost G S < _ at h
    rw [one_div,inv_mul_eq_div] at h
    have hh := (div_lt_iff₀ ht).mp h
    dsimp [s]; linarith
  change 100*B.card ≤ s
  by_contra! hn'
  have hle : (s:ℝ) < 100*(B.card:ℝ) := by exact_mod_cast hn'
  have hs : 0≤(s:ℝ) := Nat.cast_nonneg s
  push_cast at hm
  have he := mul_le_mul_of_nonneg_right hle.le (mul_nonneg ht.le hs)
  nlinarith
end DualSepClusterLP.SepStructure
end


section
namespace DualSepClusterLP.TwoPivot
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
private theorem incidences (N : α → Finset α) (hs : ∀ u v, u∈N v ↔ v∈N u)
    (A B : Finset α) : (∑ u∈A, (N u ∩ B).card) = ∑ v∈B, (N v ∩ A).card := by
  have hn (u : α) (C : Finset α) : (N u ∩ C).card = ∑ v∈C, if v∈N u then 1 else 0 := by
    rw [Finset.inter_comm]
    simp [Finset.filter_mem_eq_inter]
  simp_rw [hn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro u _
  by_cases h : u∈N v
  · simp [h,(hs u v).mp h]
  · simp [h,mt (hs u v).mpr h]
private theorem lost (N S P : Finset α) :
    (N ∩ S).card ≤ (N ∩ (S ∩ P)).card + (S \ P).card := by
  have h := Finset.card_sdiff_add_card_inter (N ∩ S) P
  have hh : ((N ∩ S) \ P) ⊆ (S \ P) := by intro x; simp only [Finset.mem_sdiff,Finset.mem_inter]; tauto
  rw [Finset.inter_assoc] at h
  have := Finset.card_le_card hh
  omega
theorem locate (N : α → Finset α) (hsym : ∀ u v, u∈N v ↔ v∈N u) (S P : Finset α)
    (hS : S.Nonempty) (D : ℕ)
    (hhalf : ∀ u∈S, S.card ≤ 2*(N u ∩ S).card)
    (hex : 100*(S\P).card ≤ S.card)
    (hcap : ∀ v∈P, (N v).card ≤ D*S.card) :
    ∃ v∈P, ∃ w∈P, S ⊆ window N P S.card v w ∧
      (window N P S.card v w).card ≤ 20*D^2*S.card := by
  let K := S ∩ P
  have hpos := Finset.card_pos.mpr hS
  have hk : K.Nonempty := by
    apply Finset.card_pos.mp
    have := Finset.card_sdiff_add_card_inter S P
    change 0 < (S ∩ P).card
    omega
  have hdeg (u : α) (hu : u∈S) : 2*S.card ≤ 5*(N u ∩ K).card := by
    have := hhalf u hu
    have := lost (N u) S P
    change _ ≤ 5*(N u ∩ (S ∩ P)).card
    omega
  have cover (B : Finset α) (hb : B ⊆ S) : ∃ v∈K, 5*(B \ N v).card ≤ 3*B.card := by
    obtain ⟨v,hv,hbest⟩ := K.exists_max_image (fun v => (N v ∩ B).card) hk
    have counts := Finset.sum_le_sum (s:=B) (fun u hu => hdeg u (hb hu))
    simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at counts
    rw [incidences N hsym B K] at counts
    have hsum := Finset.sum_le_sum hbest
    simp only [Finset.sum_const,nsmul_eq_mul] at hsum
    have hK : K.card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
    have e : S.card*(2*B.card) ≤ S.card*(5*(N v ∩ B).card) := calc
      _ = B.card*(2*S.card) := by ring
      _ ≤ 5*∑ z∈K,(N z ∩ B).card := counts
      _ ≤ 5*(K.card * (N v ∩ B).card) := Nat.mul_le_mul_left _ hsum
      _ ≤ 5*(S.card * (N v ∩ B).card) := by gcongr
      _ = _ := by ring
    have e' := Nat.le_of_mul_le_mul_left e hpos
    have h := Finset.card_sdiff_add_card_inter B (N v)
    rw [Finset.inter_comm] at h
    exact ⟨v,hv,by omega⟩
  obtain ⟨v,hv,hvB⟩ := cover S (fun _ h => h)
  obtain ⟨w,hw,hwB⟩ := cover (S \ N v) Finset.sdiff_subset
  let U := N v ∪ N w
  let W := U ∩ P
  have hmiss : 25*(S\U).card ≤ 9*S.card := by
    have he : (S \ U) = (S \ N v) \ N w := by ext; simp [U]; tauto
    rw [he]; omega
  have hin : S ⊆ window N P S.card v w := by
    intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have h := hhalf u hu
    have a := lost (N u) S P
    have b := lost (N u) K U
    have sub : K\U ⊆ S\U := by intro x; simp only [K,Finset.mem_inter,Finset.mem_sdiff]; tauto
    have c := Finset.card_le_card sub
    have sub' : N u ∩ (K ∩ U) ⊆ N u ∩ W := by
      intro x; simp only [K,W,Finset.mem_inter]; tauto
    have e := Finset.card_le_card sub'
    change (N u ∩ S).card ≤ (N u ∩ K).card + _ at a
    change S.card ≤ 10*(N u ∩ W).card
    omega
  have hvP := (Finset.mem_inter.mp hv).2
  have hwP := (Finset.mem_inter.mp hw).2
  refine ⟨v,hvP,w,hwP,hin,?_⟩
  let C := window N P S.card v w
  have hd (u : α) (hu : u∈C) : S.card ≤ 10*(N u ∩ W).card := (Finset.mem_filter.mp hu).2
  have hc := Finset.sum_le_sum hd
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hc
  rw [incidences N hsym C W] at hc
  have hd' (u : α) (hu : u∈W) : (N u ∩ C).card ≤ D*S.card :=
    (Finset.card_le_card Finset.inter_subset_left).trans (hcap u (Finset.mem_inter.mp hu).2)
  have hs := Finset.sum_le_sum hd'
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hu : W.card ≤ 2*(D*S.card) := calc
    _ ≤ U.card := Finset.card_le_card Finset.inter_subset_left
    _ ≤ (N v).card+(N w).card := Finset.card_union_le _ _
    _ ≤ D*S.card+D*S.card := Nat.add_le_add (hcap _ hvP) (hcap _ hwP)
    _ = _ := by ring
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc
    C.card * S.card ≤ 10*∑ z∈W,(N z ∩ C).card := hc
    _ ≤ 10*(W.card*(D*S.card)) := Nat.mul_le_mul_left _ hs
    _ ≤ 10*((2*(D*S.card))*(D*S.card)) := by gcongr
    _ = (20*D^2*S.card)*S.card := by ring
end DualSepClusterLP.TwoPivot
end


section
namespace DualSepClusterLP.Near
open Finset
variable {n : ℕ}
theorem top_max (U S : Finset (Fin n)) (f : Fin n → ℚ) (hs : S⊆U) (hne : S.Nonempty) :
    ∃ h ∈ U, (top U f h).card = S.card ∧ ∑ i∈S, f i ≤ ∑ i∈top U f h, f i := by
  let key (i : Fin n) := toLex (-f i,i.val)
  have hinj : Function.Injective key := by
    intro i j he
    exact Fin.ext (congrArg (fun x => (ofLex x).2) he)
  let K := U.image key
  let e := K.orderIsoOfFin rfl
  have hKU : K.card=U.card := card_image_of_injective _ hinj
  let j : Fin K.card := ⟨S.card-1,by have h := card_le_card hs; have h' := card_pos.mpr hne; omega⟩
  obtain ⟨h,hU,hh⟩ := mem_image.mp (show (e j).val ∈ U.image key from (e j).property)
  have htop (i) : i∈top U f h ↔ i∈U ∧ key i≤key h := by
    simp [top,key,Prod.Lex.toLex_le_toLex]
  have hset : (top U f h).image key = (Iic j).image (fun k => (e k).val) := by
    ext y; simp only [mem_image]; constructor
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨hi,hle⟩ := (htop i).mp hi
      let w : K := ⟨key i,mem_image.mpr ⟨i,hi,rfl⟩⟩
      refine ⟨e.symm w,?_,by simp [w]⟩
      apply mem_Iic.mpr; apply e.le_iff_le.mp
      rw [e.apply_symm_apply]
      change key i ≤ (e j).val
      rwa [←hh]
    · rintro ⟨k,hk,rfl⟩
      obtain ⟨i,hi,he⟩ := mem_image.mp (show (e k).val ∈ U.image key from (e k).property)
      refine ⟨i,(htop i).mpr ⟨hi,?_⟩,he⟩
      rw [he,hh]; exact e.monotone (mem_Iic.mp hk)
  have hcard : (top U f h).card = S.card := by
    have he : Function.Injective (fun k => (e k).val) := Subtype.val_injective.comp e.injective
    rw [←card_image_of_injective (top U f h) hinj,hset,card_image_of_injective _ he,Fin.card_Iic]
    change S.card-1+1=S.card; have := card_pos.mpr hne; omega
  refine ⟨h,hU,hcard,?_⟩
  let T := top U f h
  have hl (i : Fin n) (hi : i ∈ S \ T) : f i ≤ f h := by
    apply le_of_not_gt; intro he
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨hs (mem_sdiff.mp hi).1,Or.inl he⟩)
  have hu (i : Fin n) (hi : i ∈ T \ S) : f h ≤ f i := by
    obtain hh|hh := (mem_filter.mp (mem_sdiff.mp hi).1).2
    · exact hh.le
    · exact hh.1.ge
  have hleft := sum_le_sum (s:=S\T) (g:=fun _ => f h) hl
  have hright := sum_le_sum (s:=T\S) (f:=fun _ => f h) hu
  have heq : (S\T).card=(T\S).card := card_sdiff_comm hcard.symm
  simp only [sum_const,nsmul_eq_mul,heq] at hleft hright
  have hd : S\T = S\(S∩T) := by ext i; simp <;> tauto
  have hd' : T\S = T\(S∩T) := by ext i; simp <;> tauto
  have hl' := sum_sdiff (f:=f) (inter_subset_left (s₂:=T) (s₁:=S))
  have hr' := sum_sdiff (f:=f) (inter_subset_right (s₂:=T) (s₁:=S))
  rw [←hd] at hl'; rw [←hd'] at hr'
  change _ ≤ ∑ i∈T, f i
  linarith
end DualSepClusterLP.Near
end


section
namespace DualSepClusterLP.Near
open Finset SepStructure
variable {n : ℕ} (G : Graph n)
theorem count_switch (A B : Finset (Fin n)) (u : Fin n) : count G A u ≤ count G B u + (A\B).card := by
  have h := card_le_card_sdiff_add_card (s:=closed G u ∩ A) (t:=closed G u ∩ B)
  have hd : (closed G u ∩ A) \ (closed G u ∩ B) ⊆ A\B := by
    intro i hi; simp at hi ⊢; tauto
  unfold count
  have hb := card_le_card hd
  omega
theorem count_in (S : Finset (Fin n)) (i : Fin n) (hi : i∈S) :
    count G S i = degree G S i+1 := by
  have he : closed G i ∩ S = insert i (neighbors G i∩S) := by
    ext j; by_cases h : j=i <;> simp [closed,h,hi]
  rw [count,he,card_insert_of_notMem (by simp [neighbors])]; rfl
theorem count_out (S : Finset (Fin n)) (i : Fin n) (hi : i∉S) :
    count G S i = degree G S i := by
  unfold count degree
  congr 1; ext j; by_cases h : j=i <;> simp [closed,h,hi]
theorem localization (S : Finset (Fin n)) (hne : S.Nonempty)
    (hdens : ∀ i∈S, S.card ≤ 2*count G S i)
    (hsmall : 200*subsetCost G S ≤ (S.card:ℝ)^2) :
    ∃ v ∈ S, S ⊆ zone G S.card v ∧
      ((zone G S.card v \ S).card:ℝ)*S.card ≤ 8*subsetCost G S := by
  have hs : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hne
  have hp : ∃ v∈S, (discrepancy G S v : ℝ)*S.card ≤ 2*subsetCost G S := by
    by_contra! hh
    have hh' := sum_lt_sum_of_nonempty hne hh
    simp only [sum_const,nsmul_eq_mul] at hh'
    rw [←sum_mul,discrepancy_sum] at hh'
    linarith only [hh']
  obtain ⟨v,hv,hd⟩ := hp
  let A := closed G v
  let U := zone G S.card v
  have hnear : 100*discrepancy G S v ≤ S.card := by
    have hmul : (100*(discrepancy G S v:ℝ))*S.card ≤ (S.card:ℝ)*S.card := by nlinarith [hd,hsmall]
    exact_mod_cast (le_of_mul_le_mul_right hmul hs)
  have ha : (A\S).card ≤ discrepancy G S v := card_le_card (subset_union_left)
  have hb : (S\A).card ≤ discrepancy G S v := card_le_card (subset_union_right)
  have incl : S ⊆ U := by
    intro i hi; apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
    have h1 := hdens i hi
    have h2 := count_switch G S A i
    change S.card ≤ 3*count G A i
    omega
  have hge (i) (hi : i∈U\S) : S.card ≤ 4*degree G S i := by
    have hu := (mem_filter.mp (mem_sdiff.mp hi).1).2
    change S.card ≤ 3*count G A i at hu
    have h2 := count_switch G A S i
    rw [count_out G S i (mem_sdiff.mp hi).2] at h2
    omega
  have hsum := sum_le_sum (s:=U\S) hge
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at hsum
  have hin : U\S ⊆ univ\S := by intro i hi; exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp hi).2⟩
  have he : edges G (U\S) S ≤ edges G (univ\S) S := sum_le_sum_of_subset_of_nonneg hin (by simp)
  have hm := cut_mass G S
  have hsum' : ((U\S).card:ℝ)*S.card ≤ 4*(edges G (U\S) S:ℝ) := by exact_mod_cast hsum
  have he' : (edges G (U\S) S:ℝ) ≤ (edges G (univ\S) S:ℝ) := by exact_mod_cast he
  refine ⟨v,hv,incl,?_⟩
  change ((U\S).card:ℝ)*S.card ≤ _
  linarith
end DualSepClusterLP.Near
end


section
namespace DualSepClusterLP.Near
open Finset SepStructure
variable {n : ℕ} (G : Graph n) (q : Fin n → ℚ)
theorem score_sum (U X : Finset (Fin n)) :
    (∑ i∈X, (score G q U i:ℝ)) =
      2*(edges G X U:ℝ)-(edges G X univ:ℝ)/2+∑ i∈X,(q i:ℝ) := by
  simp only [score,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,
    Rat.cast_natCast,sum_add_distrib,sum_sub_distrib,←mul_sum,←sum_div,edges,Nat.cast_sum]
theorem linearization (U X : Finset (Fin n)) (hx : X⊆U) :
    lag G q X + (∑ i∈X,(score G q U i:ℝ)) + (edges G (U\X) (U\X):ℝ) =
      (X.card:ℝ)*((X.card:ℝ)-1)/2+(edges G U U:ℝ) := by
  let D := U\X
  have a := edges_split_left G U X U hx
  have b := edges_split_right G U X D hx
  have c := edges_split_right G U X X hx
  change edges G D U + edges G X U = edges G U U at a
  change edges G D D + edges G D X = edges G D U at b
  change edges G X D + edges G X X = edges G X U at c
  rw [edges_symm G X D] at c
  have hh : edges G D D+2*edges G X U = edges G U U+edges G X X := by omega
  have hh' := congrArg (fun a:ℕ => (a:ℝ)) hh
  push_cast at hh'
  rw [score_sum,lag]; change _ + _ + (edges G D D:ℝ) = _
  linarith only [hh',cost_quad G X]
theorem near_witness (S : Finset (Fin n)) (ε : ℝ) (hne : S.Nonempty)
    (hdens : ∀ i∈S, S.card ≤ 2*count G S i)
    (heps : 0 < ε) (heps1 : ε ≤ 1)
    (hlow : 12800*subsetCost G S ≤ ε*(S.card:ℝ)^2)
    (hgap : gap G (fun i => (q i:ℝ)) ε S) :
    ∃ v ∈ S, ∃ h ∈ zone G S.card v,
      subsetCost G (candidate G q S.card v h) < ∑ i∈candidate G q S.card v h,(q i:ℝ) := by
  let c := subsetCost G S
  let s : ℝ := S.card
  have hs : 0<s := by dsimp [s]; exact_mod_cast card_pos.mpr hne
  have hc : 0≤c := by
    have h := discrepancy_sum G S
    have h' : 0 ≤ ∑ i∈S,(discrepancy G S i:ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    dsimp [c]; linarith
  change 12800*c ≤ ε*s^2 at hlow
  obtain ⟨v,hv,hin,hk⟩ := localization G S hne hdens (by
    change 200*c ≤ s^2
    linarith only [hlow,hc,mul_le_mul_of_nonneg_right heps1 (sq_nonneg s)])
  let U := zone G S.card v
  obtain ⟨h,hh,hcard,hmax⟩ := top_max U S (score G q U) hin hne
  let T := candidate G q S.card v h
  have hT : T ⊆ U := filter_subset _ _
  change T.card=S.card at hcard
  have hm : ∑ i∈S,(score G q U i:ℝ) ≤ ∑ i∈T,(score G q U i:ℝ) := by exact_mod_cast hmax
  have hs1 := linearization G q U S hin
  have ht1 := linearization G q U T hT
  rw [hcard] at ht1
  let k : ℝ := (U\S).card
  have hbound : (edges G (U\S) (U\S):ℝ) ≤ k^2 := by
    rw [sq]; dsimp [k]; exact_mod_cast edges_le G (U\S) (U\S)
  have hTnn : 0 ≤ (edges G (U\T) (U\T):ℝ) := Nat.cast_nonneg _
  have hl : lag G q T ≤ lag G q S+k^2 := by linarith
  change k*s ≤ 8*c at hk
  have hk0 : 0≤k := Nat.cast_nonneg _
  have hsq := mul_self_le_mul_self (mul_nonneg hk0 hs.le) hk
  have hn : 64*c ≤ ε*s^2 := by linarith
  have hk2 : k^2 ≤ ε*c := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hs)).mp
    nlinarith only [hsq,mul_le_mul_of_nonneg_right hn hc]
  refine ⟨v,hv,h,hh,?_⟩
  change subsetCost G T < _
  change (1+ε)*c < _ at hgap
  change subsetCost G T - _ ≤ c - _ + k^2 at hl
  linarith
end DualSepClusterLP.Near
end


section
namespace DualSepClusterLP.SepCheck
open Finset
end DualSepClusterLP.SepCheck
end


section
namespace DualSepClusterLP.SepCheck
open Finset SepStructure
theorem checks_feasible {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) (hc : Checks t G q) :
    DualFeasible G (fun i => (q i:ℝ)/(1+1/((t:ℝ)+1))) := by
  let ε : ℝ := 1/((t:ℝ)+1)
  have he : 0<ε := by dsimp [ε]; positivity
  have he1 : ε ≤ 1 := (div_le_one (by positivity : 0<(t:ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) t])
  apply (feasible_iff_no_gap G (fun i => (q i:ℝ)) ε he.le).mpr
  intro hx
  obtain ⟨S,hgap,hd⟩ := exists_dense_gap G _ ε he hx
  have hn := gap_nonempty hgap
  have sn : S.card ≤ n := by simpa using Finset.card_le_univ S
  by_cases high : (S.card:ℝ)*(S.card-1)/2 ≤ ε*subsetCost G S
  · obtain ⟨i,_,hi⟩ := large_cost G _ S ε high hgap
    exact hi.not_ge (hc.1 i)
  by_cases low : 12800*subsetCost G S ≤ ε*(S.card:ℝ)^2
  · obtain ⟨v,hv,h,_,hh⟩ := Near.near_witness G q S ε hn hd he he1 low hgap
    have hl := hc.2.1 S.card sn v h
    unfold Near.lag at hl; linarith
  let P := eligible G t S.card
  have hsym (u v : Fin n) : u∈closed G v ↔ v∈closed G u := by
    simp only [closed,neighbors,Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [edge_symm G v u,eq_comm (a:=u) (b:=v)]
  have hcap (v : Fin n) (hv : v∈P) : (closed G v).card ≤ scale t*S.card :=
    (Finset.mem_filter.mp hv).2
  obtain ⟨v,_,w,_,hsub,hsize⟩ := TwoPivot.locate (closed G) hsym S P hn (scale t) hd
    (ineligible_bound G t S (lt_of_not_ge high)) hcap
  let U := localize t G S.card v w
  change U.card ≤ growth t*S.card at hsize
  have hsq : (U.card:ℝ)^2 ≤ (growth t:ℝ)^2*(S.card:ℝ)^2 := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsize) _
  have bad := hc.2.2 S.card sn v w S hsub
  change 0 ≤ (accuracy t:ℝ)*(subsetCost G S-∑ i∈S,(q i:ℝ)) + 2*(U.card:ℝ)^2 at bad
  have hneg : (subsetCost G S-∑ i∈S,(q i:ℝ)) < -(ε * subsetCost G S) := by
    unfold gap at hgap; linarith
  have ht : 0 < (t:ℝ)+1 := by positivity
  have hg : 0 < (growth t:ℝ) := by unfold growth scale; positivity
  have hacc : 0 < (accuracy t:ℝ) := by
    simp only [accuracy,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos ht)) (sq_pos_of_pos hg)
  have hlag := mul_lt_mul_of_pos_left hneg hacc
  have hlow : (S.card:ℝ)^2 < 12800*subsetCost G S*((t:ℝ)+1) := by
    have hl := lt_of_not_ge low
    dsimp [ε] at hl; rw [one_div,inv_mul_eq_div] at hl
    exact (div_lt_iff₀ ht).mp hl
  have scaled := mul_lt_mul_of_pos_left hlow (sq_pos_of_pos hg)
  have heq : (accuracy t:ℝ)*(-(ε*subsetCost G S)) =
        -25600*(t+1:ℝ)*(growth t:ℝ)^2*subsetCost G S := by
    simp only [accuracy,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,ε]
    field_simp <;> ring
  rw [heq] at hlag
  nlinarith only [bad,hsq,scaled,hlag]
end DualSepClusterLP.SepCheck
end

open DualSepClusterLP

theorem solution {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) (h : SepCheck.Checks t G q) :
    DualFeasible G (fun i => (q i:ℝ)/(1+1/((t:ℝ)+1))) := SepCheck.checks_feasible t G q h
