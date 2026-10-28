-- Prove2me | solution 1 for ForecastComp.IELF.win_prob_transfer_mono
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T14:18:22.695027+00:00
-- url     : https://prove2.me/submissions/bbc865df-cc6f-4793-927e-e3cf19159b5e

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model
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
 theorem solution {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k₀ : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε)
    (hother : ∀ l,l≠k₀ → q' l=q l) (hi : q' k₀ i=q k₀ i+ε)
    (hj : ∀ j,j≠i → q' k₀ j=q k₀ j-ε/((n:ℝ)-1))
    (hnonneg : ∀ l,l≠k₀ → ∀ j,0 ≤ q l j) : winProbOf q i ≤ winProbOf q' i :=
  Queelius.ForecastTransfer.win_transfer hn q q' k₀ i ε hε hother hi hj hnonneg
