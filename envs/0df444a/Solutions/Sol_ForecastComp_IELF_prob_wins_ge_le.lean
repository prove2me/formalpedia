-- Prove2me | solution 1 for ForecastComp.IELF.prob_wins_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T05:00:51.017998+00:00
-- url     : https://prove2.me/submissions/d90b83aa-1b83-4e6b-ab8a-e5a0f86be651

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
 theorem mean_gap_solution {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (i j : Fin n) (hij : i≠j) :
    expWins R θ y i-expWins R θ y j = (m:ℝ)*(avgScore R θ (y i)-avgScore R θ (y j))/((n:ℝ)-1) ∧
    ∀ Δ : ℝ,Δ ≤ avgScore R θ (y i)-avgScore R θ (y j) →
      (m:ℝ)*Δ/((n:ℝ)-1) ≤ expWins R θ y i-expWins R θ y j :=
  ⟨Queelius.ForecastMean.average_gap hn R θ y i j,fun Δ h => Queelius.ForecastMean.gap_lower_bound hn R θ y i j Δ h⟩

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Queelius.ForecastAccuracy
open ForecastComp.IELF
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
noncomputable def rowLaw {α : Type*} [Fintype α] [MeasurableSpace α]
    (q : α → ℝ) (hq : ∀ a,0 ≤ q a) (hn : ∑ a,q a=1) : Measure α :=
  (PMF.ofFintype (fun a => ENNReal.ofReal (q a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hq a),hn,ENNReal.ofReal_one])).toMeasure
instance rowLaw_probability {α : Type*} [Fintype α] [MeasurableSpace α]
    (q : α → ℝ) (hq : ∀ a,0 ≤ q a) (hn : ∑ a,q a=1) : IsProbabilityMeasure (rowLaw q hq hn) := by
  unfold rowLaw;infer_instance
lemma rowLaw_atom {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : α → ℝ) (hq : ∀ a,0 ≤ q a) (hn : ∑ a,q a=1) (a : α) :
    (rowLaw q hq hn).real {a}=q a := by
  unfold Measure.real rowLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),PMF.ofFintype_apply,ENNReal.toReal_ofReal (hq a)]
lemma product_integral {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : ι → α → ℝ) (hq : ∀ k a,0 ≤ q k a) (hn : ∀ k,∑ a,q k a=1)
    (F : (ι → α) → ℝ) :
    (∫ w,F w ∂Measure.pi (fun k => rowLaw (q k) (hq k) (hn k)))=
      ∑ w,(∏ k,q k (w k))*F w := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  simp only [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro k _
  exact rowLaw_atom (q k) (hq k) (hn k) (w k)
lemma bounded_left_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (X : Fin m → Ω → ℝ) (hind : iIndepFun X μ) (hmeas : ∀ k,Measurable (X k))
    (hbd : ∀ k,∀ᵐ ω ∂μ,X k ω ∈ Set.Icc (-1:ℝ) 1) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∫ ω',∑ k,X k ω' ∂μ)-∑ k,X k ω} ≤ Real.exp (-t^2/(2*(m:ℝ))) := by
  have hint : ∀ k,Integrable (X k) μ := fun k => Integrable.of_mem_Icc (-1) 1 (hmeas k).aemeasurable (hbd k)
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω => (∫ ω',X k ω' ∂μ)-X k ω) (1 : NNReal) μ := by
    intro k _
    have hh := (hasSubgaussianMGF_of_mem_Icc (hmeas k).aemeasurable (hbd k)).neg
    have he : -(fun ω => X k ω-(∫ ω',X k ω' ∂μ))=(fun ω => (∫ ω',X k ω' ∂μ)-X k ω) := by
      funext ω;dsimp;ring
    rw [he] at hh
    norm_num at hh
    exact hh
  have hi : iIndepFun (fun k ω => (∫ ω',X k ω' ∂μ)-X k ω) μ :=
    hind.comp (fun k z => (∫ ω',X k ω' ∂μ)-z) (fun k => measurable_const.sub measurable_id)
  have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi hsub ht
  have he (ω : Ω) : (∑ k,((∫ ω',X k ω' ∂μ)-X k ω))=(∫ ω',∑ k,X k ω' ∂μ)-∑ k,X k ω := by
    rw [integral_finsetSum _ (fun k _ => hint k),Finset.sum_sub_distrib]
  simp only [he] at hh
  simpa using hh

noncomputable def pairWeight {m n : ℕ} (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ)
    (y : Fin n → Fin m → ℝ) (k : Fin m) (z : Bool × Fin n) : ℝ :=
  (if z.1 then θ k else 1-θ k)*elfProb R (fun j => y j k) z.1 z.2
lemma pair_nonnegative {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1) (k : Fin m) (z : Bool × Fin n) :
    0 ≤ pairWeight R θ y k z := by
  apply mul_nonneg
  · split_ifs <;> linarith [(hθ k).1,(hθ k).2]
  · exact elf_nonnegative hn R hbdd (fun j => y j k) (fun j => hy j k) z.1 z.2
lemma pair_mass {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (θ : Fin m → ℝ)
    (y : Fin n → Fin m → ℝ) (k : Fin m) : ∑ z,pairWeight R θ y k z=1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  change (∑ j,θ k*elfProb R (fun l => y l k) true j)+(∑ j,(1-θ k)*elfProb R (fun l => y l k) false j)=1
  rw [← Finset.mul_sum,← Finset.mul_sum,Queelius.ForecastMean.elf_mass hn,Queelius.ForecastMean.elf_mass hn]
  ring
noncomputable def experiment {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1) : Measure (Fin m → Bool × Fin n) :=
  Measure.pi (fun k => rowLaw (pairWeight R θ y k) (pair_nonnegative hn R hbdd θ hθ y hy k) (pair_mass hn R θ y k))
instance experiment_probability {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1) :
    IsProbabilityMeasure (experiment hn R hbdd θ hθ y hy) := by unfold experiment;infer_instance
lemma experiment_integral {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1) (G : (Fin m → Fin n) → ℝ) :
    (∫ z,G (fun k => (z k).2) ∂experiment hn R hbdd θ hθ y hy)=
      ∑ x,bernWeight θ x*∑ w,(∏ k,elfProb R (fun j => y j k) (x k) (w k))*G w := by
  unfold experiment
  rw [product_integral]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun p : (Fin m → Bool) × (Fin m → Fin n) =>
    bernWeight θ p.1*((∏ k,elfProb R (fun j => y j k) (p.1 k) (p.2 k))*G p.2))]
  apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Bool) (fun _ => Fin n))
  intro z
  change (∏ k,(if (z k).1 then θ k else 1-θ k)*elfProb R (fun j => y j k) (z k).1 (z k).2)*G (fun k => (z k).2)=
    (∏ k,if (z k).1 then θ k else 1-θ k)*((∏ k,elfProb R (fun j => y j k) (z k).1 (z k).2)*G (fun k => (z k).2))
  rw [Finset.prod_mul_distrib]
  ring
lemma experiment_count_mean {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1) (i : Fin n) :
    (∫ z,(winCount (fun k => (z k).2) i : ℝ) ∂experiment hn R hbdd θ hθ y hy)=expWins R θ y i := by
  exact experiment_integral hn R hbdd θ hθ y hy (fun w => (winCount w i : ℝ))
lemma experiment_comparison {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1) (i j : Fin n) :
    (experiment hn R hbdd θ hθ y hy).real {z | winCount (fun k => (z k).2) i ≤ winCount (fun k => (z k).2) j}=
      probWinsGe R θ y j i := by
  rw [← integral_indicator_one (by measurability)]
  simp only [Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq]
  exact experiment_integral hn R hbdd θ hθ y hy
    (fun w => if winCount w i ≤ winCount w j then (1:ℝ) else 0)

noncomputable def countDiff {n : ℕ} (i j : Fin n) (z : Bool × Fin n) : ℝ :=
  (if z.2=i then 1 else 0)-(if z.2=j then 1 else 0)
lemma countDiff_sum {m n : ℕ} (z : Fin m → Bool × Fin n) (i j : Fin n) :
    (∑ k,countDiff i j (z k))=(winCount (fun k => (z k).2) i : ℝ)-(winCount (fun k => (z k).2) j : ℝ) := by
  simp only [countDiff,Finset.sum_sub_distrib,Queelius.ForecastMean.count_sum]
lemma comparison_exp_bound {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k,θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k,y j k ∈ Set.Icc (0:ℝ) 1)
    (i j : Fin n) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : Δ ≤ avgScore R θ (y i)-avgScore R θ (y j)) :
    probWinsGe R θ y j i ≤ Real.exp (-((m:ℝ)*Δ^2)/(2*((n:ℝ)-1)^2)) := by
  by_cases hm : m=0
  · subst m
    simp [avgScore] at hgap
    linarith
  have hmR : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hnR : (0:ℝ) < (n:ℝ)-1 := by exact_mod_cast (show (0:ℤ) < (n:ℤ)-1 by omega)
  let μ := experiment hn R hbdd θ hθ y hy
  let X : Fin m → (Fin m → Bool × Fin n) → ℝ := fun k z => countDiff i j (z k)
  have hf : Measurable (countDiff i j) := by unfold countDiff;measurability
  have hi : iIndepFun X μ := by
    unfold μ experiment X
    exact iIndepFun_pi (fun _ => hf.aemeasurable)
  have hx : ∀ k,Measurable (X k) := fun k => hf.comp (measurable_pi_apply k)
  have hb : ∀ k,∀ᵐ z ∂μ,X k z ∈ Set.Icc (-1:ℝ) 1 := by
    intro k
    filter_upwards [] with z
    dsimp [X,countDiff]
    split_ifs <;> norm_num
  let t : ℝ := (m:ℝ)*Δ/((n:ℝ)-1)
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hΔ.le) hnR.le
  have he : (∫ z,∑ k,X k z ∂μ)=expWins R θ y i-expWins R θ y j := by
    change (∫ z,∑ k,countDiff i j (z k) ∂μ)=_
    simp_rw [countDiff_sum]
    rw [integral_sub Integrable.of_finite Integrable.of_finite,
      experiment_count_mean hn R hbdd θ hθ y hy i,experiment_count_mean hn R hbdd θ hθ y hy j]
  have hg : t ≤ (∫ z,∑ k,X k z ∂μ) := by
    rw [he]
    exact Queelius.ForecastMean.gap_lower_bound hn R θ y i j Δ hgap
  have hs : {z | winCount (fun k => (z k).2) i ≤ winCount (fun k => (z k).2) j} ⊆
      {z | t ≤ (∫ z',∑ k,X k z' ∂μ)-∑ k,X k z} := by
    intro z hz
    have hh : (winCount (fun k => (z k).2) i : ℝ) ≤ (winCount (fun k => (z k).2) j : ℝ) := by exact_mod_cast hz
    change t ≤ (∫ z',∑ k,X k z' ∂μ)-∑ k,countDiff i j (z k)
    rw [countDiff_sum]
    linarith
  rw [← experiment_comparison hn R hbdd θ hθ y hy i j]
  calc
    _ ≤ μ.real {z | t ≤ (∫ z',∑ k,X k z' ∂μ)-∑ k,X k z} := measureReal_mono hs
    _ ≤ Real.exp (-t^2/(2*(m:ℝ))) := bounded_left_tail μ X hi hx hb t ht
    _ = _ := by
      congr 1
      dsimp [t]
      field_simp [hmR,ne_of_gt hnR]
lemma two_forecaster_dependence_control :
    (∑ a : Fin 2,(1/2 : ℚ)*(if a=0 then 1 else 0)*(if a=1 then 1 else 0))=0 ∧
      (1/2 : ℚ)*(1/2 : ℚ) ≠ 0 := by norm_num [Fin.sum_univ_succ]
end Queelius.ForecastAccuracy



namespace ForecastComp.IELF

/-- Proof of Theorem 7 (Appendix M), p. 36: if forecaster `i`'s expected score exceeds `j`'s by
at least `Δ > 0`, then under independent outcomes the probability that `j` wins at least as many
event lotteries as `i` is at most `2 e^{−mΔ²/(2(n−1)²)}`. -/
theorem _root_.solution {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k, θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k, y j k ∈ Set.Icc (0:ℝ) 1)
    (i j : Fin n) (hij : i ≠ j) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : Δ ≤ avgScore R θ (y i) - avgScore R θ (y j)) :
    probWinsGe R θ y j i ≤
      2 * Real.exp (-((m:ℝ) * Δ ^ 2) / (2 * ((n:ℝ) - 1) ^ 2)) := by
  have h := Queelius.ForecastAccuracy.comparison_exp_bound hn R hbdd θ hθ y hy i j Δ hΔ hgap
  have hp := Real.exp_pos (-((m:ℝ)*Δ^2)/(2*((n:ℝ)-1)^2))
  linarith

end ForecastComp.IELF
