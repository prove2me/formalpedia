-- Prove2me | solution 1 for ForecastComp.IELF.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T13:42:27.703102+00:00
-- url     : https://prove2.me/submissions/25311139-bb7c-4938-b3ce-b81a606fedf9

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
 theorem solution {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (i j : Fin n) (hij : i≠j) :
    expWins R θ y i-expWins R θ y j = (m:ℝ)*(avgScore R θ (y i)-avgScore R θ (y j))/((n:ℝ)-1) ∧
    ∀ Δ : ℝ,Δ ≤ avgScore R θ (y i)-avgScore R θ (y j) →
      (m:ℝ)*Δ/((n:ℝ)-1) ≤ expWins R θ y i-expWins R θ y j :=
  ⟨Queelius.ForecastMean.average_gap hn R θ y i j,fun Δ h => Queelius.ForecastMean.gap_lower_bound hn R θ y i j Δ h⟩
