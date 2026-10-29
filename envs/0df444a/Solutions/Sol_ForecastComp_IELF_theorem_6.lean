-- Prove2me | solution 1 for ForecastComp.IELF.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T04:12:49.435227+00:00
-- url     : https://prove2.me/submissions/3f02e1f6-e7b6-4f9d-a41c-9da76d8d257b

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

section
namespace PriorStrict
open ForecastComp.IELF
namespace Queelius.ForecastMean
lemma product_marginal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (q : ι → κ → ℝ) (hnorm : ∀ l, ∑ j,q l j=1) (k : ι) (G : κ → ℝ) :
    (∑ w : ι → κ,(∏ l,q l (w l))*G (w k)) = ∑ j,q k j*G j := by
  classical
  have he (w : ι → κ) : (∏ l,q l (w l)*(if l=k then G (w l) else 1)) = (∏ l,q l (w l))*G (w k) := by
    rw [Finset.prod_mul_distrib]
    simp
  calc
    _ = ∑ w : ι → κ,∏ l,q l (w l)*(if l=k then G (w l) else 1) := Finset.sum_congr rfl (fun w _ => (he w).symm)
    _ = ∏ l,∑ j,q l j*(if l=k then G j else 1) := (Fintype.prod_sum (fun l j => q l j*(if l=k then G j else 1))).symm
    _ = ∑ j,q k j*G j := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro l hl hlk
        simp [hlk,hnorm]
      · simp
lemma product_mass {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (q : ι → κ → ℝ) (hnorm : ∀ l, ∑ j,q l j=1) :
    (∑ w : ι → κ,∏ l,q l (w l))=1 := by rw [← Fintype.prod_sum];simp [hnorm]
lemma count_sum {m n : ℕ} (w : Fin m → Fin n) (i : Fin n) :
    (winCount w i : ℝ) = ∑ k : Fin m,(if w k=i then 1 else 0 : ℝ) := by
  classical
  simp only [winCount,Finset.card_eq_sum_ones,Nat.cast_sum,Nat.cast_one,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp
lemma count_expectation {m n : ℕ} (q : Fin m → Fin n → ℝ)
    (hnorm : ∀ l, ∑ j,q l j=1) (i : Fin n) :
    (∑ w : Fin m → Fin n,(∏ k,q k (w k))*(winCount w i : ℝ)) = ∑ k,q k i := by
  classical
  simp_rw [count_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [product_marginal q hnorm k (fun j => if j=i then 1 else 0)]
  simp
lemma erase_sum {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i,v j = (∑ j,v j)-v i := by
  have h := Finset.sum_erase_add Finset.univ v (Finset.mem_univ i)
  linarith
lemma elf_closed {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (ys : Fin n → ℝ) (x : Bool) (i : Fin n) :
    elfProb R ys x i = (((n:ℝ)-1)/n+R (ys i) x-(∑ j,R (ys j) x)/n)/((n:ℝ)-1) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have h : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [elfProb,erase_sum]
  field_simp
  <;> ring
lemma elf_mass {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (ys : Fin n → ℝ) (x : Bool) :
    ∑ i,elfProb R ys x i=1 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have h : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp_rw [elf_closed hn]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  <;> ring
lemma elf_gap {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (ys : Fin n → ℝ) (x : Bool) (i j : Fin n) :
    elfProb R ys x i-elfProb R ys x j = (R (ys i) x-R (ys j) x)/((n:ℝ)-1) := by
  rw [elf_closed hn,elf_closed hn]
  ring
lemma bern_mass {m : ℕ} (θ : Fin m → ℝ) : ∑ x,bernWeight θ x=1 := by
  unfold bernWeight
  exact product_mass (fun (k : Fin m) (b : Bool) => if b then θ k else 1-θ k) (fun k => by simp)
lemma bern_marginal {m : ℕ} (θ : Fin m → ℝ) (k : Fin m) (G : Bool → ℝ) :
    (∑ x,bernWeight θ x*G (x k))=θ k*G true+(1-θ k)*G false := by
  have hnorm (l : Fin m) : (∑ b : Bool,if b then θ l else 1-θ l)=1 := by simp [Fintype.sum_bool]
  have h := product_marginal (fun l b => if b then θ l else 1-θ l) hnorm k G
  simpa [bernWeight,Fintype.sum_bool,add_comm] using h
lemma expWins_gap {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ)
    (y : Fin n → Fin m → ℝ) (i j : Fin n) :
    expWins R θ y i-expWins R θ y j =
      (∑ k,(expScore R (y i k) (θ k)-expScore R (y j k) (θ k)))/((n:ℝ)-1) := by
  classical
  unfold expWins
  simp_rw [count_expectation _ (fun _ => elf_mass hn _ _ _)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub,← Finset.sum_sub_distrib,elf_gap hn]
  simp_rw [← Finset.sum_div,← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [bern_marginal θ k (fun b => R (y i k) b-R (y j k) b)]
  simp only [expScore]
  ring
lemma average_gap {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ)
    (y : Fin n → Fin m → ℝ) (i j : Fin n) :
    expWins R θ y i-expWins R θ y j =
      (m:ℝ)*(avgScore R θ (y i)-avgScore R θ (y j))/((n:ℝ)-1) := by
  rw [expWins_gap hn]
  by_cases hm : m=0
  · subst m
    simp [avgScore]
  · have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
    unfold avgScore
    rw [Finset.sum_sub_distrib]
    field_simp
    <;> ring
lemma gap_lower_bound {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ)
    (y : Fin n → Fin m → ℝ) (i j : Fin n) (Δ : ℝ)
    (hΔ : Δ ≤ avgScore R θ (y i)-avgScore R θ (y j)) :
    (m:ℝ)*Δ/((n:ℝ)-1) ≤ expWins R θ y i-expWins R θ y j := by
  rw [average_gap hn]
  apply div_le_div_of_nonneg_right _ (by
    have h : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  exact mul_le_mul_of_nonneg_left hΔ (Nat.cast_nonneg _)
lemma no_events_control {n : ℕ} (R : ℝ → Bool → ℝ) (θ : Fin 0 → ℝ) (y : Fin n → Fin 0 → ℝ) (i : Fin n) :
    expWins R θ y i=0 ∧ avgScore R θ (y i)=0 := by simp [expWins,winCount,avgScore]
lemma deterministic_outcome_control (G : Bool → ℝ) :
    (0:ℝ)*G true+(1-0)*G false=G false ∧ (1:ℝ)*G true+(1-1)*G false=G true := by simp
end Queelius.ForecastMean
namespace Queelius.ForecastTransfer
open ForecastComp.IELF
noncomputable def restCount {m n : ℕ} (w : Fin m → Fin n) (k : Fin m) (l : Fin n) : ℕ :=
  ∑ t ∈ Finset.univ.erase k,if w t=l then 1 else 0
lemma count_update {m n : ℕ} (w : Fin m → Fin n) (k : Fin m) (j l : Fin n) :
    winCount (Function.update w k j) l = restCount w k l+if j=l then 1 else 0 := by
  classical
  simp only [winCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [← Finset.sum_erase_add Finset.univ (fun t => if Function.update w k j t=l then (1:ℕ) else 0) (Finset.mem_univ k)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
lemma share_bounds {m n : ℕ} (w : Fin m → Fin n) (i : Fin n) :
    0 ≤ tieShare w i ∧ tieShare w i ≤ 1 := by
  unfold tieShare
  split_ifs with hi
  · have hc : (1:ℝ) ≤ (topSet w).card := by
      exact_mod_cast (show 1 ≤ (topSet w).card from Finset.card_pos.mpr ⟨i,hi⟩)
    exact ⟨by positivity,by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hc⟩
  · simp
lemma top_after_transfer {m n : ℕ} (w : Fin m → Fin n) (k : Fin m) (i j : Fin n) (hij : i≠j)
    (hi : i ∈ topSet (Function.update w k j)) :
    topSet (Function.update w k i)={i} := by
  classical
  have hold := (Finset.mem_filter.mp hi).2
  have hstrict (l : Fin n) (hli : l≠i) :
      winCount (Function.update w k i) l < winCount (Function.update w k i) i := by
    have hh := hold l
    rw [count_update,count_update] at hh ⊢
    simp only [if_true,if_neg (Ne.symm hli)] at *
    have hji : j≠i := Ne.symm hij
    simp only [if_neg hji] at hh
    split_ifs at hh <;> omega
  have hnew : i ∈ topSet (Function.update w k i) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,fun l => ?_⟩
    by_cases hl : l=i
    · simp [hl]
    · exact (hstrict l hl).le
  ext l
  constructor
  · intro hl
    have hh := (Finset.mem_filter.mp hl).2 i
    have he : l=i := by by_contra hn;have := hstrict l hn;omega
    simp [he]
  · intro hl
    have he : l=i := by simpa using hl
    simpa [he] using hnew
lemma share_update_mono {m n : ℕ} (w : Fin m → Fin n) (k : Fin m) (i j : Fin n) :
    tieShare (Function.update w k j) i ≤ tieShare (Function.update w k i) i := by
  classical
  by_cases hij : i=j
  · subst j
    rfl
  by_cases hi : i ∈ topSet (Function.update w k j)
  · have he := top_after_transfer w k i j hij hi
    have hnew : tieShare (Function.update w k i) i=1 := by simp [tieShare,he]
    rw [hnew]
    exact (share_bounds _ _).2
  · simpa only [tieShare,if_neg hi] using (share_bounds (Function.update w k i) i).1
lemma sum_condition {m n : ℕ} (q : Fin (m+1) → Fin n → ℝ) (k : Fin (m+1))
    (F : (Fin (m+1) → Fin n) → ℝ) :
    (∑ w : Fin (m+1) → Fin n,(∏ l,q l (w l))*F w) =
      ∑ h : Fin m → Fin n,(∏ l,q (k.succAbove l) (h l)) *
        ∑ j : Fin n,q k j*F (@Fin.insertNth m (fun _ => Fin n) k j h) := by
  classical
  let e := Fin.insertNthEquiv (fun _ : Fin (m+1) => Fin n) k
  rw [← e.sum_comp (fun w => (∏ l,q l (w l))*F w),Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (∏ l,q l (@Fin.insertNth m (fun _ => Fin n) k j h l))*F (e (j,h)) = _
  rw [Fin.prod_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  change (q k j*(∏ l,q (k.succAbove l) (h l)))*F (@Fin.insertNth m (fun _ => Fin n) k j h) = _
  ring
lemma row_transfer {n : ℕ} (hn : 2 ≤ n) (q q' F : Fin n → ℝ) (i : Fin n) (ε : ℝ)
    (hε : 0 ≤ ε) (hi : q' i=q i+ε)
    (hj : ∀ j,j≠i → q' j=q j-ε/((n:ℝ)-1)) (hF : ∀ j,F j ≤ F i) :
    ∑ j,q j*F j ≤ ∑ j,q' j*F j := by
  classical
  have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hd : (n:ℝ)-1 ≠ 0 := by linarith
  have he : (∑ j,q' j*F j)-(∑ j,q j*F j) = ε*F i-ε/((n:ℝ)-1)*(∑ j ∈ Finset.univ.erase i,F j) := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_erase_add Finset.univ (fun j => q' j*F j-q j*F j) (Finset.mem_univ i)]
    rw [hi]
    have hsum : (∑ j ∈ Finset.univ.erase i,(q' j*F j-q j*F j)) =
        -(ε/((n:ℝ)-1))*(∑ j ∈ Finset.univ.erase i,F j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hjmem
      rw [hj j (Finset.ne_of_mem_erase hjmem)]
      ring
    rw [hsum]
    ring
  have hsum : (∑ j ∈ Finset.univ.erase i,F j) ≤ ((n:ℝ)-1)*F i := by
    have hh := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hF j)
    have hc : ((Finset.univ.erase i : Finset (Fin n)).card : ℝ)=(n:ℝ)-1 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ i),Nat.cast_sub (show 1 ≤ n by omega)]
    simpa only [Finset.sum_const,nsmul_eq_mul,hc] using hh
  have hm := mul_le_mul_of_nonneg_left hsum (div_nonneg hε (by linarith : 0 ≤ (n:ℝ)-1))
  have hcancel : ε/((n:ℝ)-1)*(((n:ℝ)-1)*F i)=ε*F i := by field_simp
  rw [hcancel] at hm
  linarith
lemma win_transfer {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε)
    (hother : ∀ l,l≠k → q' l=q l) (hi : q' k i=q k i+ε)
    (hj : ∀ j,j≠i → q' k j=q k j-ε/((n:ℝ)-1))
    (hpos : ∀ l,l≠k → ∀ j,0 ≤ q l j) : winProbOf q i ≤ winProbOf q' i := by
  classical
  cases m with
  | zero => exact Fin.elim0 k
  | succ m =>
    unfold winProbOf
    rw [sum_condition q k (fun w => tieShare w i),sum_condition q' k (fun w => tieShare w i)]
    have ho (l : Fin m) : q' (k.succAbove l)=q (k.succAbove l) := hother _ (Fin.succAbove_ne _ _)
    simp_rw [ho]
    apply Finset.sum_le_sum
    intro h hh
    apply mul_le_mul_of_nonneg_left
    · apply row_transfer hn (q k) (q' k) (fun j => tieShare (@Fin.insertNth m (fun _ => Fin n) k j h) i) i ε hε hi hj
      intro j
      let w := @Fin.insertNth m (fun _ => Fin n) k i h
      have hu : Function.update w k j = @Fin.insertNth m (fun _ => Fin n) k j h := by simp [w]
      have hui : Function.update w k i=w := by simp [w]
      have hv := share_update_mono w k i j
      rw [hu,hui] at hv
      exact hv
    · apply Finset.prod_nonneg
      intro l hl
      exact hpos _ (Fin.succAbove_ne _ _) _
lemma empty_events_tie {n : ℕ} (w : Fin 0 → Fin n) (i : Fin n) : tieShare w i=1/(n:ℝ) := by
  simp [tieShare,topSet,winCount]
lemma one_event_count {n : ℕ} (i j : Fin n) (hij : i≠j) :
    winCount (fun _ : Fin 1 => i) i=1 ∧ winCount (fun _ : Fin 1 => i) j=0 := by
  simp [winCount,hij]
end Queelius.ForecastTransfer
open ForecastComp.IELF in
 theorem previous_transfer_solution {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k₀ : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε)
    (hother : ∀ l,l≠k₀ → q' l=q l) (hi : q' k₀ i=q k₀ i+ε)
    (hj : ∀ j,j≠i → q' k₀ j=q k₀ j-ε/((n:ℝ)-1))
    (hnonneg : ∀ l,l≠k₀ → ∀ j,0 ≤ q l j) : winProbOf q i ≤ winProbOf q' i :=
  Queelius.ForecastTransfer.win_transfer hn q q' k₀ i ε hε hother hi hj hnonneg

namespace Queelius.ForecastStrict
open ForecastComp.IELF Queelius.ForecastTransfer
lemma insert_count {m n : ℕ} (k : Fin (m+1)) (h : Fin m → Fin n) (j l : Fin n) :
    winCount (@Fin.insertNth m (fun _ => Fin n) k j h) l =
      (Finset.univ.filter (fun t => h t=l)).card+if j=l then 1 else 0 := by
  classical
  simp only [winCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  omega
lemma split_counts (m : ℕ) {n : ℕ} (i j : Fin n) (hij : i≠j) :
    let h : Fin m → Fin n := fun t => if t.val < (m+1)/2 then i else j
    (Finset.univ.filter (fun t => h t=i)).card=(m+1)/2 ∧
    (Finset.univ.filter (fun t => h t=j)).card=m-(m+1)/2 ∧
    ∀ l,l≠i → l≠j → (Finset.univ.filter (fun t => h t=l)).card=0 := by
  classical
  dsimp only
  have ha : (m+1)/2 ≤ m := by omega
  have hi : (Finset.univ.filter (fun t : Fin m => (if t.val < (m+1)/2 then i else j)=i)) =
      Finset.univ.filter (fun t : Fin m => t.val < (m+1)/2) := by
    ext t
    by_cases ht : t.val < (m+1)/2 <;> simp [ht,hij,Ne.symm hij]
  have hj : (Finset.univ.filter (fun t : Fin m => (if t.val < (m+1)/2 then i else j)=j)) =
      Finset.univ.filter (fun t : Fin m => ¬t.val < (m+1)/2) := by
    ext t
    by_cases ht : t.val < (m+1)/2 <;> simp [ht,hij,Ne.symm hij]
  have hc : (Finset.univ.filter (fun t : Fin m => t.val < (m+1)/2)).card=(m+1)/2 := by
    rw [Fin.card_filter_val_lt,Nat.min_eq_right ha]
  refine ⟨by rw [hi,hc],?_,?_⟩
  · rw [hj]
    have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun t : Fin m => t.val < (m+1)/2)
    simp only [Finset.card_univ,Fintype.card_fin,hc] at hh
    omega
  · intro l hli hlj
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t
    by_cases ht : t.val < (m+1)/2 <;> simp [ht,Ne.symm hli,Ne.symm hlj]
lemma pivotal_exists {m n : ℕ} (hn : 2 ≤ n) (k : Fin (m+1)) (i : Fin n) :
    ∃ h : Fin m → Fin n,∃ j : Fin n,j≠i ∧
      tieShare (@Fin.insertNth m (fun _ => Fin n) k i h) i=1 ∧
      tieShare (@Fin.insertNth m (fun _ => Fin n) k j h) i < 1 := by
  classical
  have hnontrivial : Nontrivial (Fin n) := ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro he;have := congrArg Fin.val he;norm_num at this⟩⟩
  letI := hnontrivial
  obtain ⟨j,hji⟩ := exists_ne i
  let h : Fin m → Fin n := fun t => if t.val < (m+1)/2 then i else j
  have hc := split_counts m i j (Ne.symm hji)
  change (Finset.univ.filter (fun t => h t=i)).card=(m+1)/2 ∧
    (Finset.univ.filter (fun t => h t=j)).card=m-(m+1)/2 ∧
    ∀ l,l≠i → l≠j → (Finset.univ.filter (fun t => h t=l)).card=0 at hc
  have htop : topSet (@Fin.insertNth m (fun _ => Fin n) k i h)={i} := by
    ext l
    simp only [topSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hli
      have hh := hl i
      simp only [insert_count,eq_self_iff_true,ite_true,hc.1,if_neg (Ne.symm hli)] at hh
      by_cases hlj : l=j
      · subst l
        rw [hc.2.1] at hh
        omega
      · rw [hc.2.2 l hli hlj] at hh
        omega
    · intro hli a
      rw [hli]
      simp only [insert_count,eq_self_iff_true,ite_true,hc.1]
      by_cases hai : a=i
      · rw [hai]
        simp [hc.1]
      · simp only [if_neg (Ne.symm hai)]
        by_cases haj : a=j
        · rw [haj,hc.2.1]
          omega
        · rw [hc.2.2 a hai haj]
          omega
  have hshare : tieShare (@Fin.insertNth m (fun _ => Fin n) k i h) i=1 := by simp [tieShare,htop]
  refine ⟨h,j,hji,hshare,?_⟩
  by_cases hi : i ∈ topSet (@Fin.insertNth m (fun _ => Fin n) k j h)
  · have hj : j ∈ topSet (@Fin.insertNth m (fun _ => Fin n) k j h) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,fun l => ?_⟩
      have hli := (Finset.mem_filter.mp hi).2 l
      have hij := (Finset.mem_filter.mp hi).2 j
      simp only [insert_count,hc.1,hc.2.1,if_neg hji,eq_self_iff_true,ite_true] at hij hli ⊢
      omega
    have hcard : 2 ≤ (topSet (@Fin.insertNth m (fun _ => Fin n) k j h)).card :=
      by
        have hsub : ({i,j} : Finset (Fin n)) ⊆ topSet (@Fin.insertNth m (fun _ => Fin n) k j h) := by
          intro a ha
          rcases Finset.mem_insert.mp ha with ha | ha
          · simpa [ha] using hi
          · have he : a=j := Finset.mem_singleton.mp ha
            simpa [he] using hj
        have hh := Finset.card_le_card hsub
        simpa [Ne.symm hji] using hh
    have hcardR : (1:ℝ) < (topSet (@Fin.insertNth m (fun _ => Fin n) k j h)).card := by exact_mod_cast (show 1 < _ from hcard)
    simp only [tieShare,if_pos hi]
    exact (div_lt_one (by linarith : (0:ℝ) < _)).mpr hcardR
  · simp [tieShare,hi]
lemma row_transfer_strict {n : ℕ} (hn : 2 ≤ n) (q q' F : Fin n → ℝ) (i : Fin n) (ε : ℝ)
    (hε : 0 < ε) (hi : q' i=q i+ε)
    (hj : ∀ j,j≠i → q' j=q j-ε/((n:ℝ)-1)) (hF : ∀ j,F j ≤ F i)
    (hstrict : ∃ j,j≠i ∧ F j < F i) :
    ∑ j,q j*F j < ∑ j,q' j*F j := by
  classical
  have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hd : (n:ℝ)-1 ≠ 0 := by linarith
  have he : (∑ j,q' j*F j)-(∑ j,q j*F j) = ε*F i-ε/((n:ℝ)-1)*(∑ j ∈ Finset.univ.erase i,F j) := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_erase_add Finset.univ (fun j => q' j*F j-q j*F j) (Finset.mem_univ i)]
    rw [hi]
    have hsum : (∑ j ∈ Finset.univ.erase i,(q' j*F j-q j*F j)) =
        -(ε/((n:ℝ)-1))*(∑ j ∈ Finset.univ.erase i,F j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hjmem
      rw [hj j (Finset.ne_of_mem_erase hjmem)]
      ring
    rw [hsum]
    ring
  have hsum : (∑ j ∈ Finset.univ.erase i,F j) < ((n:ℝ)-1)*F i := by
    have hh : (∑ j ∈ Finset.univ.erase i,F j) < ∑ _j ∈ Finset.univ.erase i,F i := by
      apply Finset.sum_lt_sum (fun j _ => hF j)
      obtain ⟨j,hji,hjlt⟩ := hstrict
      exact ⟨j,Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩,hjlt⟩
    have hc : ((Finset.univ.erase i : Finset (Fin n)).card : ℝ)=(n:ℝ)-1 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ i),Nat.cast_sub (show 1 ≤ n by omega)]
    simpa only [Finset.sum_const,nsmul_eq_mul,hc] using hh
  have hm := mul_lt_mul_of_pos_left hsum (div_pos hε (by linarith : 0 < (n:ℝ)-1))
  have hcancel : ε/((n:ℝ)-1)*(((n:ℝ)-1)*F i)=ε*F i := by field_simp
  rw [hcancel] at hm
  linarith
lemma win_transfer_strict {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 < ε)
    (hother : ∀ l,l≠k → q' l=q l) (hi : q' k i=q k i+ε)
    (hj : ∀ j,j≠i → q' k j=q k j-ε/((n:ℝ)-1))
    (hpos : ∀ l,l≠k → ∀ j,0 < q l j) : winProbOf q i < winProbOf q' i := by
  classical
  cases m with
  | zero => exact Fin.elim0 k
  | succ m =>
    unfold winProbOf
    rw [sum_condition q k (fun w => tieShare w i),sum_condition q' k (fun w => tieShare w i)]
    have ho (l : Fin m) : q' (k.succAbove l)=q (k.succAbove l) := hother _ (Fin.succAbove_ne _ _)
    simp_rw [ho]
    have hF (h : Fin m → Fin n) (j : Fin n) :
        tieShare (@Fin.insertNth m (fun _ => Fin n) k j h) i ≤ tieShare (@Fin.insertNth m (fun _ => Fin n) k i h) i := by
      let w := @Fin.insertNth m (fun _ => Fin n) k i h
      have hu : Function.update w k j = @Fin.insertNth m (fun _ => Fin n) k j h := by simp [w]
      have hui : Function.update w k i=w := by simp [w]
      have hv := share_update_mono w k i j
      rw [hu,hui] at hv
      exact hv
    apply Finset.sum_lt_sum
    · intro h hh
      apply mul_le_mul_of_nonneg_left
      · exact row_transfer hn (q k) (q' k) _ i ε hε.le hi hj (hF h)
      · exact (Finset.prod_pos (fun l _ => hpos _ (Fin.succAbove_ne _ _) _)).le
    · obtain ⟨h,j,hji,hwin,hlose⟩ := pivotal_exists hn k i
      refine ⟨h,Finset.mem_univ _,?_⟩
      apply mul_lt_mul_of_pos_left
      · apply row_transfer_strict hn (q k) (q' k) _ i ε hε hi hj (hF h)
        exact ⟨j,hji,by rw [hwin];exact hlose⟩
      · exact Finset.prod_pos (fun l _ => hpos _ (Fin.succAbove_ne _ _) _)
end Queelius.ForecastStrict
open ForecastComp.IELF in
 theorem solution {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k₀ : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 < ε)
    (hother : ∀ l,l≠k₀ → q' l=q l) (hi : q' k₀ i=q k₀ i+ε)
    (hj : ∀ j,j≠i → q' k₀ j=q k₀ j-ε/((n:ℝ)-1))
    (hpos : ∀ l,l≠k₀ → ∀ j,0 < q l j) : winProbOf q i < winProbOf q' i :=
  Queelius.ForecastStrict.win_transfer_strict hn q q' k₀ i ε hε hother hi hj hpos


end PriorStrict
end

section
namespace CommunityFactor
open MeasureTheory

namespace Aux_IELF_bif
open ForecastComp.IELF

lemma meas_bool {β : Type*} [MeasurableSpace β] (g : β → Bool → ℝ)
    (hg : ∀ x, Measurable (fun b => g b x)) :
    Measurable (fun b : Bool × β => g b.2 b.1) := by
  have h : (fun b : Bool × β => g b.2 b.1) =
      fun b => if b.1 = true then g b.2 true else g b.2 false := by
    funext b; cases b.1 <;> simp
  rw [h]
  refine Measurable.ite ?_ ((hg true).comp measurable_snd) ((hg false).comp measurable_snd)
  exact measurable_fst (measurableSet_singleton true)

lemma int_elf {n : ℕ} (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1) (i : Fin n) (z : ℝ)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (l : Fin n) :
    Integrable (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i z) b.1 l) ν := by
  have hk : ∀ k,
      Integrable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) ν := by
    intro k
    have hm : Measurable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) := by
      apply meas_bool (fun (w : Fin n → ℝ) (x : Bool) => R (Function.update w i z k) x)
      intro x
      by_cases hki : k = i
      · subst hki
        simp only [Function.update_self]
        exact measurable_const
      · simp only [Function.update_of_ne hki]
        exact (hmeas x).comp (measurable_pi_apply k)
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [hrep] with b hb
    have hmem : Function.update b.2 i z k ∈ Set.Icc (0:ℝ) 1 := by
      by_cases hki : k = i
      · subst hki; rw [Function.update_self]; exact hz
      · rw [Function.update_of_ne hki]; exact hb k
    have := hbdd _ hmem b.1
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  unfold elfProb
  exact (integrable_const _).add (((hk l).sub
    ((integrable_finset_sum _ (fun k _ => hk k)).const_mul _)).const_mul _)

end Aux_IELF_bif

open ForecastComp.IELF in
theorem solution {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R) (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Fin m → Measure (Bool × (Fin n → ℝ))) [∀ k, IsProbabilityMeasure (ν k)]
    (hrep : ∀ k, ∀ᵐ b ∂(ν k), ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1)
    (i : Fin n) (yi : Fin m → ℝ) (hyi : ∀ k, yi k ∈ Set.Icc (0:ℝ) 1) :
    ∫ ω, ielfSelProb R (Function.update (reportsOf ω) i yi) (outcomeOf ω) i ∂(Measure.pi ν) =
      winProbOf (fun k l => ∫ b, elfProb R (Function.update b.2 i (yi k)) b.1 l ∂(ν k)) i := by
  have hfun : ∀ (ω : Fin m → Bool × (Fin n → ℝ)) k,
      (fun j => Function.update (reportsOf ω) i yi j k) = Function.update (ω k).2 i (yi k) := by
    intro ω k
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, reportsOf]
  have hrw : (fun ω : Fin m → Bool × (Fin n → ℝ) =>
      ielfSelProb R (Function.update (reportsOf ω) i yi) (outcomeOf ω) i) =
      fun ω => ∑ w : Fin m → Fin n, (∏ k, (fun b : Bool × (Fin n → ℝ) =>
        elfProb R (Function.update b.2 i (yi k)) b.1 (w k)) (ω k)) * tieShare w i := by
    funext ω
    unfold ielfSelProb winProbOf
    refine Finset.sum_congr rfl (fun w _ => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp only [hfun ω k, outcomeOf]
  rw [hrw, integral_finset_sum]
  · unfold winProbOf
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [integral_mul_const]
    congr 1
    exact integral_fintype_prod_eq_prod (𝕜 := ℝ) (E := fun _ => Bool × (Fin n → ℝ))
      (fun k (b : Bool × (Fin n → ℝ)) => elfProb R (Function.update b.2 i (yi k)) b.1 (w k))
  · intro w _
    apply Integrable.mul_const
    exact Integrable.fintype_prod (fun k =>
      Aux_IELF_bif.int_elf R hbdd hmeas (ν k) (hrep k) i (yi k) (hyi k) (w k))

end CommunityFactor
end

section
namespace CommunityTransfer
open MeasureTheory

namespace Aux_IELF_ut
open ForecastComp.IELF

lemma meas_bool {β : Type*} [MeasurableSpace β] (g : β → Bool → ℝ)
    (hg : ∀ x, Measurable (fun b => g b x)) :
    Measurable (fun b : Bool × β => g b.2 b.1) := by
  have h : (fun b : Bool × β => g b.2 b.1) =
      fun b => if b.1 = true then g b.2 true else g b.2 false := by
    funext b; cases b.1 <;> simp
  rw [h]
  refine Measurable.ite ?_ ((hg true).comp measurable_snd) ((hg false).comp measurable_snd)
  exact measurable_fst (measurableSet_singleton true)

lemma sum_one {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (ys : Fin n → ℝ) (x : Bool) :
    ∑ l, elfProb R ys x l = 1 := by
  unfold elfProb
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  have hn1 : (n:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n:ℝ) ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

lemma diff_i {n : ℕ} (R : ℝ → Bool → ℝ) (v : Fin n → ℝ) (i : Fin n) (y y' : ℝ) (x : Bool) :
    elfProb R (Function.update v i y') x i - elfProb R (Function.update v i y) x i =
      1 / (n:ℝ) * (R y' x - R y x) := by
  unfold elfProb
  simp only [Function.update_self]
  have : ∀ z, ∑ j ∈ Finset.univ.erase i, R (Function.update v i z j) x =
      ∑ j ∈ Finset.univ.erase i, R (v j) x := fun z =>
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this y, this y']
  ring

lemma diff_j {n : ℕ} (R : ℝ → Bool → ℝ) (v : Fin n → ℝ) (i j : Fin n) (hji : j ≠ i)
    (y y' : ℝ) (x : Bool) :
    elfProb R (Function.update v i y') x j - elfProb R (Function.update v i y) x j =
      -(1 / (n:ℝ) * (R y' x - R y x)) / ((n:ℝ) - 1) := by
  unfold elfProb
  simp only [Function.update_of_ne hji]
  have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩
  have : ∀ z, ∑ k ∈ Finset.univ.erase j, R (Function.update v i z k) x =
      R z x + ∑ k ∈ (Finset.univ.erase j).erase i, R (v k) x := by
    intro z
    rw [← Finset.add_sum_erase _ _ hmem, Function.update_self]
    congr 1
    exact Finset.sum_congr rfl (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  rw [this y, this y']
  ring

end Aux_IELF_ut

open ForecastComp.IELF in
theorem solution {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R) (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν, ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1) (i : Fin n)
    (y y' : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (hy' : y' ∈ Set.Icc (0:ℝ) 1) :
    (∑ l, ∫ b, elfProb R (Function.update b.2 i y) b.1 l ∂ν) = 1 ∧
    ∀ j, j ≠ i →
      (∫ b, elfProb R (Function.update b.2 i y') b.1 j ∂ν) -
          ∫ b, elfProb R (Function.update b.2 i y) b.1 j ∂ν =
        -((∫ b, elfProb R (Function.update b.2 i y') b.1 i ∂ν) -
            ∫ b, elfProb R (Function.update b.2 i y) b.1 i ∂ν) / ((n:ℝ) - 1) := by
  -- integrability of each score term
  have hk : ∀ z, z ∈ Set.Icc (0:ℝ) 1 → ∀ k,
      Integrable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) ν := by
    intro z hz k
    have hm : Measurable (fun b : Bool × (Fin n → ℝ) => R (Function.update b.2 i z k) b.1) := by
      apply Aux_IELF_ut.meas_bool (fun (w : Fin n → ℝ) (x : Bool) => R (Function.update w i z k) x)
      intro x
      by_cases hki : k = i
      · subst hki
        simp only [Function.update_self]
        exact measurable_const
      · simp only [Function.update_of_ne hki]
        exact (hmeas x).comp (measurable_pi_apply k)
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [hrep] with b hb
    have hmem : Function.update b.2 i z k ∈ Set.Icc (0:ℝ) 1 := by
      by_cases hki : k = i
      · subst hki; rw [Function.update_self]; exact hz
      · rw [Function.update_of_ne hki]; exact hb k
    have := hbdd _ hmem b.1
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hint : ∀ z, z ∈ Set.Icc (0:ℝ) 1 → ∀ l,
      Integrable (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i z) b.1 l) ν := by
    intro z hz l
    unfold elfProb
    exact (integrable_const _).add (((hk z hz l).sub
      ((integrable_finset_sum _ (fun k _ => hk z hz k)).const_mul _)).const_mul _)
  refine ⟨?_, fun j hji => ?_⟩
  · rw [← integral_finset_sum _ (fun l _ => hint y hy l)]
    simp_rw [Aux_IELF_ut.sum_one hn]
    simp
  · rw [← integral_sub (hint y' hy' j) (hint y hy j), ← integral_sub (hint y' hy' i) (hint y hy i)]
    simp_rw [Aux_IELF_ut.diff_j R _ i j hji y y', Aux_IELF_ut.diff_i R _ i y y']
    rw [integral_div, integral_neg]

end CommunityTransfer
end

namespace Queelius.ForecastIC
open ForecastComp.IELF MeasureTheory
open PriorStrict.Queelius.ForecastTransfer
lemma outcome_integrable {n : ℕ} (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν] :
    Integrable (fun b => if b.1 then (1:ℝ) else 0) ν := by
  have hm : Measurable (fun b : Bool × (Fin n → ℝ) => if b.1 then (1:ℝ) else 0) :=
    CommunityFactor.Aux_IELF_bif.meas_bool (fun (_ : Fin n → ℝ) (b : Bool) => if b then (1:ℝ) else 0) (fun _ => measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun b => by cases b.1 <;> norm_num)
lemma mean_unit {n : ℕ} (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν] (p : ℝ)
    (hp : (∫ b,if b.1 then (1:ℝ) else 0 ∂ν)=p) : p ∈ Set.Icc (0:ℝ) 1 := by
  have hn : 0 ≤ ∫ b,if b.1 then (1:ℝ) else 0 ∂ν := integral_nonneg (fun b => by cases b.1 <;> norm_num)
  have hu := integral_mono_ae (outcome_integrable ν) (integrable_const (1:ℝ))
    (ae_of_all ν (fun b => show (if b.1 then (1:ℝ) else 0) ≤ 1 by cases b.1 <;> norm_num))
  simpa [hp] using And.intro hn hu
lemma score_affine {n : ℕ} (R : ℝ → Bool → ℝ) (z : ℝ) (b : Bool × (Fin n → ℝ)) :
    R z b.1=R z false+(R z true-R z false)*(if b.1 then (1:ℝ) else 0) := by
  cases b.1 <;> simp <;> ring
lemma score_integrable {n : ℕ} (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (R : ℝ → Bool → ℝ) (z : ℝ) : Integrable (fun b => R z b.1) ν := by
  have he : (fun b : Bool × (Fin n → ℝ) => R z b.1)=fun b => R z false+(R z true-R z false)*(if b.1 then (1:ℝ) else 0) := funext (score_affine R z)
  rw [he]
  exact (integrable_const _).add ((outcome_integrable ν).const_mul _)
lemma score_expectation {n : ℕ} (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (R : ℝ → Bool → ℝ) (z p : ℝ) (hp : (∫ b,if b.1 then (1:ℝ) else 0 ∂ν)=p) :
    (∫ b,R z b.1 ∂ν)=expScore R z p := by
  have he : (fun b : Bool × (Fin n → ℝ) => R z b.1)=fun b => R z false+(R z true-R z false)*(if b.1 then (1:ℝ) else 0) := funext (score_affine R z)
  rw [he,integral_add (integrable_const _) ((outcome_integrable ν).const_mul _),integral_const_mul,hp]
  simp only [integral_const,probReal_univ,one_smul,expScore]
  ring
lemma expected_gain {n : ℕ} (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x,Measurable (fun y => R y x))
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν,∀ j,b.2 j ∈ Set.Icc (0:ℝ) 1) (i : Fin n)
    (z p : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) (hpunit : p ∈ Set.Icc (0:ℝ) 1)
    (hp : (∫ b,if b.1 then (1:ℝ) else 0 ∂ν)=p) :
    ((∫ b,elfProb R (Function.update b.2 i p) b.1 i ∂ν)-∫ b,elfProb R (Function.update b.2 i z) b.1 i ∂ν)=
      (expScore R p p-expScore R z p)/(n:ℝ) := by
  rw [← integral_sub
    (CommunityFactor.Aux_IELF_bif.int_elf R hbdd hmeas ν hrep i p hpunit i)
    (CommunityFactor.Aux_IELF_bif.int_elf R hbdd hmeas ν hrep i z hz i)]
  have he : (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i p) b.1 i-elfProb R (Function.update b.2 i z) b.1 i)=
      fun b => 1/(n:ℝ)*(R p b.1-R z b.1) := funext (fun b => CommunityTransfer.Aux_IELF_ut.diff_i R b.2 i z p b.1)
  rw [he,integral_const_mul,integral_sub (score_integrable ν R p) (score_integrable ν R z),score_expectation ν R p p hp,score_expectation ν R z p hp]
  ring
lemma elf_nonnegative {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (ys : Fin n → ℝ) (hys : ∀ j,ys j ∈ Set.Icc (0:ℝ) 1) (x : Bool) (i : Fin n) :
    0 ≤ elfProb R ys x i := by
  have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : (∑ j ∈ Finset.univ.erase i,R (ys j) x) ≤ (n:ℝ)-1 := by
    have h := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => (hbdd _ (hys j) x).2)
    simpa [Nat.cast_sub (show 1 ≤ n by omega)] using h
  have hd : (∑ j ∈ Finset.univ.erase i,R (ys j) x)/((n:ℝ)-1) ≤ 1 := (div_le_one (by linarith)).mpr hs
  have hr := (hbdd _ (hys i) x).1
  have hh : 0 ≤ 1+R (ys i) x-(∑ j ∈ Finset.univ.erase i,R (ys j) x)/((n:ℝ)-1) := by linarith
  have hm := mul_nonneg (le_of_lt (one_div_pos.mpr (by linarith : (0:ℝ) < n))) hh
  have he : elfProb R ys x i = 1/(n:ℝ)*(1+R (ys i) x-(∑ j ∈ Finset.univ.erase i,R (ys j) x)/((n:ℝ)-1)) := by unfold elfProb;ring
  rw [he]
  exact hm
end Queelius.ForecastIC

namespace Queelius.ForecastIC
open ForecastComp.IELF MeasureTheory
lemma elf_positive {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (hlt : ∀ z ∈ Set.Icc (0:ℝ) 1,∀ x,R z x < 1)
    (ys : Fin n → ℝ) (hys : ∀ j,ys j ∈ Set.Icc (0:ℝ) 1) (x : Bool) (i : Fin n) :
    0 < elfProb R ys x i := by
  classical
  have hnR : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j,hji⟩ := exists_ne i
  have hs : (∑ j ∈ Finset.univ.erase i,R (ys j) x) < (n:ℝ)-1 := by
    have h : (∑ j ∈ Finset.univ.erase i,R (ys j) x) < ∑ _j ∈ Finset.univ.erase i,(1:ℝ) := by
      apply Finset.sum_lt_sum (fun j _ => (hlt _ (hys j) x).le)
      exact ⟨j,Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩,hlt _ (hys j) x⟩
    simpa [Nat.cast_sub (show 1 ≤ n by omega)] using h
  have hd : (∑ j ∈ Finset.univ.erase i,R (ys j) x)/((n:ℝ)-1) < 1 := (div_lt_one (by linarith)).mpr hs
  have hr := (hbdd _ (hys i) x).1
  have hh : 0 < 1+R (ys i) x-(∑ j ∈ Finset.univ.erase i,R (ys j) x)/((n:ℝ)-1) := by linarith
  have he : elfProb R ys x i = 1/(n:ℝ)*(1+R (ys i) x-(∑ j ∈ Finset.univ.erase i,R (ys j) x)/((n:ℝ)-1)) := by unfold elfProb;ring
  rw [he]
  exact mul_pos (one_div_pos.mpr (by linarith)) hh
lemma expected_row_nonnegative {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (ν : Measure (Bool × (Fin n → ℝ))) (hrep : ∀ᵐ b ∂ν,∀ j,b.2 j ∈ Set.Icc (0:ℝ) 1)
    (i : Fin n) (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) (l : Fin n) :
    0 ≤ ∫ b,elfProb R (Function.update b.2 i z) b.1 l ∂ν := by
  apply integral_nonneg_of_ae
  filter_upwards [hrep] with b hb
  apply elf_nonnegative hn R hbdd _ _ b.1 l
  intro j
  by_cases hji : j=i
  · subst j;simpa using hz
  · simpa [Function.update_of_ne hji] using hb j
lemma expected_row_positive {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x,Measurable (fun y => R y x)) (hlt : ∀ z ∈ Set.Icc (0:ℝ) 1,∀ x,R z x < 1)
    (ν : Measure (Bool × (Fin n → ℝ))) [IsProbabilityMeasure ν]
    (hrep : ∀ᵐ b ∂ν,∀ j,b.2 j ∈ Set.Icc (0:ℝ) 1)
    (i : Fin n) (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1) (l : Fin n) :
    0 < ∫ b,elfProb R (Function.update b.2 i z) b.1 l ∂ν := by
  have hpos : ∀ᵐ b ∂ν,0 < elfProb R (Function.update b.2 i z) b.1 l := by
    filter_upwards [hrep] with b hb
    apply elf_positive hn R hbdd hlt _ _ b.1 l
    intro j
    by_cases hji : j=i
    · subst j;simpa using hz
    · simpa [Function.update_of_ne hji] using hb j
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le))
    (CommunityFactor.Aux_IELF_bif.int_elf R hbdd hmeas ν hrep i z hz l)).mpr
  have he : Function.support (fun b : Bool × (Fin n → ℝ) => elfProb R (Function.update b.2 i z) b.1 l) =ᵐ[ν] (Set.univ : Set (Bool × (Fin n → ℝ))) := by
    filter_upwards [hpos] with b hb
    change (elfProb R (Function.update b.2 i z) b.1 l≠0) = True
    simp [ne_of_gt hb]
  rw [measure_congr he,measure_univ]
  exact zero_lt_one
lemma rowwise_mono {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ) (i : Fin n) (δ : Fin m → ℝ)
    (hδ : ∀ k,0 ≤ δ k) (hi : ∀ k,q' k i=q k i+δ k)
    (hj : ∀ k j,j≠i → q' k j=q k j-δ k/((n:ℝ)-1))
    (hq : ∀ k j,0 ≤ q k j) (hq' : ∀ k j,0 ≤ q' k j) : winProbOf q i ≤ winProbOf q' i := by
  classical
  let mix (s : Finset (Fin m)) : Fin m → Fin n → ℝ := fun k => if k∈s then q' k else q k
  have hall (s : Finset (Fin m)) : winProbOf q i ≤ winProbOf (mix s) i := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert k s hks ih =>
      apply ih.trans
      apply PriorStrict.Queelius.ForecastTransfer.win_transfer hn (mix s) (mix (insert k s)) k i (δ k) (hδ k)
      · intro l hl
        simp [mix,hl]
      · simpa [mix,hks] using hi k
      · intro j hji
        simpa [mix,hks] using hj k j hji
      · intro l hl j
        dsimp [mix]
        split_ifs
        · exact hq' l j
        · exact hq l j
  simpa [mix] using hall Finset.univ
lemma rowwise_strict {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ) (i : Fin n) (δ : Fin m → ℝ)
    (hδ : ∀ k,0 ≤ δ k) (hi : ∀ k,q' k i=q k i+δ k)
    (hj : ∀ k j,j≠i → q' k j=q k j-δ k/((n:ℝ)-1))
    (hq : ∀ k j,0 ≤ q k j) (hq' : ∀ k j,0 ≤ q' k j)
    (hpos : 2 ≤ m → ∀ k j,0 < q k j) (hstrict : ∃ k,0 < δ k) : winProbOf q i < winProbOf q' i := by
  classical
  obtain ⟨k,hk⟩ := hstrict
  let q1 := Function.update q k (q' k)
  have hfirst : winProbOf q i < winProbOf q1 i := by
    apply PriorStrict.Queelius.ForecastStrict.win_transfer_strict hn q q1 k i (δ k) hk
    · intro l hl;exact Function.update_of_ne hl _ _
    · simpa [q1] using hi k
    · intro j hji;simpa [q1] using hj k j hji
    · intro l hl j
      have htwo : 2 ≤ m := Fin.nontrivial_iff_two_le.mp (nontrivial_of_ne l k hl)
      exact hpos htwo l j
  apply hfirst.trans_le
  apply rowwise_mono hn q1 q' i (fun l => if l=k then 0 else δ l)
  · intro l;split_ifs <;> simp [hδ]
  · intro l;by_cases hl : l=k
    · subst l;simp [q1]
    · simpa [q1,Function.update_of_ne hl,hl] using hi l
  · intro l j hji;by_cases hl : l=k
    · subst l;simp [q1]
    · simpa [q1,Function.update_of_ne hl,hl] using hj l j hji
  · intro l j
    by_cases hl : l=k
    · subst l;simpa [q1] using hq' k j
    · simpa [q1,Function.update_of_ne hl] using hq l j
  · exact hq'
end Queelius.ForecastIC

open ForecastComp.IELF MeasureTheory in
 theorem solution {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hprop : IsStrictlyProper R) (hbdd : IsUnitBounded R)
    (hmeas : ∀ x,Measurable (fun y => R y x)) (m : ℕ) (hm : 1 ≤ m)
    (hlt : 2 ≤ m → ∀ y ∈ Set.Icc (0:ℝ) 1,∀ x,R y x < 1) :
    StrictlyICUnderBeliefIndep (ielfSelProb (m := m) (n := n) R) := by
  classical
  intro i p ν inst hp hrep y hy hne
  have hpunit (k : Fin m) : p k ∈ Set.Icc (0:ℝ) 1 := Queelius.ForecastIC.mean_unit (ν k) (p k) (hp k)
  rw [CommunityFactor.solution hn R hbdd hmeas ν hrep i y hy,
    CommunityFactor.solution hn R hbdd hmeas ν hrep i p hpunit]
  let qb : Fin m → Fin n → ℝ := fun k l => ∫ b,elfProb R (Function.update b.2 i (y k)) b.1 l ∂ν k
  let qt : Fin m → Fin n → ℝ := fun k l => ∫ b,elfProb R (Function.update b.2 i (p k)) b.1 l ∂ν k
  let δ : Fin m → ℝ := fun k => qt k i-qb k i
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgain (k : Fin m) : δ k=(expScore R (p k) (p k)-expScore R (y k) (p k))/(n:ℝ) :=
    Queelius.ForecastIC.expected_gain R hbdd hmeas (ν k) (hrep k) i (y k) (p k) (hy k) (hpunit k) (hp k)
  have hd (k : Fin m) : 0 ≤ δ k := by
    by_cases he : y k=p k
    · rw [hgain,he]
      simp
    · rw [hgain]
      exact (div_pos (sub_pos.mpr (hprop _ (hpunit k) _ (hy k) he)) hnR).le
  have hi (k : Fin m) : qt k i=qb k i+δ k := by dsimp [δ];ring
  have hj (k : Fin m) (j : Fin n) (hji : j≠i) : qt k j=qb k j-δ k/((n:ℝ)-1) := by
    have h := (CommunityTransfer.solution hn R hbdd hmeas (ν k) (hrep k) i (y k) (p k) (hy k) (hpunit k)).2 j hji
    change qt k j-qb k j=-(qt k i-qb k i)/((n:ℝ)-1) at h
    rw [neg_div] at h
    dsimp [δ]
    linarith
  have hqb (k : Fin m) (j : Fin n) : 0 ≤ qb k j :=
    Queelius.ForecastIC.expected_row_nonnegative hn R hbdd (ν k) (hrep k) i (y k) (hy k) j
  have hqt (k : Fin m) (j : Fin n) : 0 ≤ qt k j :=
    Queelius.ForecastIC.expected_row_nonnegative hn R hbdd (ν k) (hrep k) i (p k) (hpunit k) j
  have hpos (hm2 : 2 ≤ m) (k : Fin m) (j : Fin n) : 0 < qb k j :=
    Queelius.ForecastIC.expected_row_positive hn R hbdd hmeas (hlt hm2) (ν k) (hrep k) i (y k) (hy k) j
  have hex : ∃ k : Fin m,y k≠p k := by
    by_contra h
    apply hne
    funext k
    by_contra hk
    exact h ⟨k,hk⟩
  obtain ⟨k,hk⟩ := hex
  have hstrict : ∃ k,0 < δ k := by
    refine ⟨k,?_⟩
    rw [hgain]
    exact div_pos (sub_pos.mpr (hprop _ (hpunit k) _ (hy k) hk)) hnR
  exact Queelius.ForecastIC.rowwise_strict hn qb qt i δ hd hi hj hqb hqt hpos hstrict
