-- Prove2me | solution 1 for CongestionPoA.Mixed.mixed_sum_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:16:40.848705+00:00
-- url     : https://prove2.me/submissions/7c691dfd-2876-4f98-9de4-79e723db462d

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model

set_option autoImplicit false

namespace MixedSumCostAux

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]

/-- The involution `(x, s) ↦ (s i, update s i x)`. -/
def swapE (i : ι) : (S i × (∀ j, S j)) ≃ (S i × (∀ j, S j)) where
  toFun p := (p.2 i, Function.update p.2 i p.1)
  invFun p := (p.2 i, Function.update p.2 i p.1)
  left_inv p := by simp
  right_inv p := by simp

lemma prob_update (σ : ∀ i, S i → ℝ) (i : ι) (τ : S i → ℝ) (s : ∀ j, S j) :
    AGT.profileProb (Function.update σ i τ) s = τ (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma prob_eq (σ : ∀ i, S i → ℝ) (i : ι) (s : ∀ j, S j) :
    AGT.profileProb σ s = σ i (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  have := prob_update σ i (σ i) s
  rwa [Function.update_eq_self] at this

lemma rest_update (σ : ∀ i, S i → ℝ) (i : ι) (s : ∀ j, S j) (x : S i) :
    ∏ j ∈ univ.erase i, σ j (Function.update s i x j) = ∏ j ∈ univ.erase i, σ j (s j) :=
  Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])

lemma swap_sum (σ : ∀ i, S i → ℝ) (i : ι) (τ : S i → ℝ) (hσ : ∑ x, σ i x = 1)
    (hτ : ∑ x, τ x = 1) (F : (∀ j, S j) → ℝ)
    (hF : ∀ s x, F (Function.update s i x) = F s) :
    ∑ s, AGT.profileProb (Function.update σ i τ) s * F s = ∑ s, AGT.profileProb σ s * F s := by
  set R : (∀ j, S j) → ℝ := fun s => ∏ j ∈ univ.erase i, σ j (s j) with hR
  have h1 : ∑ s, AGT.profileProb (Function.update σ i τ) s * F s
      = ∑ p : S i × (∀ j, S j), σ i p.1 * (τ (p.2 i) * R p.2 * F p.2) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_mul, hσ, one_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [prob_update]
  have h2 : ∑ s, AGT.profileProb σ s * F s
      = ∑ p : S i × (∀ j, S j), τ p.1 * (σ i (p.2 i) * R p.2 * F p.2) := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_mul, hτ, one_mul]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [prob_eq σ i]
  rw [h1, h2, ← (swapE (S := S) i).sum_comp]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [swapE, Equiv.coe_fn_mk, Function.update_self, hR, rest_update, hF]
  ring

end MixedSumCostAux

namespace MixedSumCostAux2

open Finset

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

lemma load_update_le (A : ι → Finset E) (i : ι) (X : Finset E) (e : E) :
    CongestionPoA.AsymSum.load (Function.update A i X) e ≤ CongestionPoA.AsymSum.load A e + 1 := by
  unfold CongestionPoA.AsymSum.load
  calc (univ.filter (fun j => e ∈ Function.update A i X j)).card
      ≤ (insert i (univ.filter (fun j => e ∈ A j))).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj
        by_cases hji : j = i
        · simp [hji]
        · rw [Function.update_of_ne hji] at hj
          simp [hj]
    _ ≤ _ := Finset.card_insert_le _ _

lemma regroup (P : ι → Finset E) (g : E → ℝ) :
    ∑ i, ∑ e ∈ P i, g e = ∑ e, (CongestionPoA.AsymSum.load P e : ℝ) * g e := by
  unfold CongestionPoA.AsymSum.load
  symm
  calc ∑ e, ((univ.filter (fun i => e ∈ P i)).card : ℝ) * g e
      = ∑ e, ∑ i, if e ∈ P i then g e else 0 := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ i, ∑ e, if e ∈ P i then g e else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_filter]
        congr 1
        ext; simp

end MixedSumCostAux2

open CongestionPoA.Mixed in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e k, G.latency e k = a e * k + b e)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    mixedSumCost G σ ≤ ∑ e, (CongestionPoA.AsymSum.load P e : ℝ) * (a e * (expLoad G σ e + 1) + b e) := by
  classical
  rw [← MixedSumCostAux2.regroup]
  unfold mixedSumCost
  apply Finset.sum_le_sum
  intro i _
  set p : ↥(G.strategies i) := ⟨P i, hP i⟩ with hp
  set δ : ↥(G.strategies i) → ℝ := fun x => if x = p then 1 else 0 with hδdef
  have hδ : AGT.IsLottery δ := by
    refine ⟨fun x => ?_, ?_⟩
    · simp only [hδdef]; split_ifs <;> norm_num
    · simp [hδdef]
  have hN := hσ.2 i δ hδ
  have hneg : ∀ τ : (∀ j, ↥(G.strategies j) → ℝ), AGT.expectedPayoff (payoff G) τ i
      = -∑ s, AGT.profileProb τ s * CongestionPoA.AsymSum.cost G (fun j => (s j).1) i := by
    intro τ
    simp [AGT.expectedPayoff, payoff, Finset.sum_neg_distrib, mul_neg]
  rw [hneg, hneg] at hN
  have h1 : expCost G σ i ≤ ∑ s, AGT.profileProb (Function.update σ i δ) s
      * CongestionPoA.AsymSum.cost G (fun j => (s j).1) i := by
    unfold expCost; linarith
  set F : (∀ j, ↥(G.strategies j)) → ℝ :=
    fun s => CongestionPoA.AsymSum.cost G (fun j => (Function.update s i p j).1) i with hF
  have h2 : ∑ s, AGT.profileProb (Function.update σ i δ) s
      * CongestionPoA.AsymSum.cost G (fun j => (s j).1) i
      = ∑ s, AGT.profileProb (Function.update σ i δ) s * F s := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : s i = p
    · have : Function.update s i p = s := Function.update_eq_self_iff.mpr hs.symm
      simp only [hF, this]
    · rw [MixedSumCostAux.prob_update]
      simp [hδdef, hs]
  have h3 := MixedSumCostAux.swap_sum σ i δ (hσ.1 i).2 hδ.2 F
    (fun s x => by simp only [hF, Function.update_idem])
  have hpos : ∀ s, 0 ≤ AGT.profileProb σ s :=
    fun s => Finset.prod_nonneg (fun j _ => (hσ.1 j).1 _)
  have htot : ∑ s, AGT.profileProb σ s = 1 := by
    unfold AGT.profileProb
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun j _ => (hσ.1 j).2)
  have h4 : ∀ s, F s ≤ ∑ e ∈ P i,
      (a e * ((CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ) + 1) + b e) := by
    intro s
    have hfun : (fun j => (Function.update s i p j).1)
        = Function.update (fun j => (s j).1) i (P i) := by
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [hp]
      · simp [Function.update_of_ne hj]
    simp only [hF, CongestionPoA.AsymSum.cost, hfun, Function.update_self, hlat]
    apply Finset.sum_le_sum
    intro e _
    have hl := MixedSumCostAux2.load_update_le (fun j => (s j).1) i (P i) e
    have hl' : (CongestionPoA.AsymSum.load (Function.update (fun j => (s j).1) i (P i)) e : ℝ)
        ≤ (CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ) + 1 := by exact_mod_cast hl
    have := mul_le_mul_of_nonneg_left hl' (ha e)
    linarith
  calc expCost G σ i ≤ ∑ s, AGT.profileProb σ s * F s := by rw [← h3, ← h2]; exact h1
    _ ≤ ∑ s, AGT.profileProb σ s * ∑ e ∈ P i,
          (a e * ((CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ) + 1) + b e) :=
        Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h4 s) (hpos s))
    _ = ∑ e ∈ P i, (a e * (expLoad G σ e + 1) + b e) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        have : ∑ s, AGT.profileProb σ s
              * (a e * ((CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ) + 1) + b e)
            = a e * ∑ s, AGT.profileProb σ s * (CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ)
              + (a e + b e) * ∑ s, AGT.profileProb σ s := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          ring
        rw [this, htot]
        unfold expLoad
        ring
