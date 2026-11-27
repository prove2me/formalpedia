-- Prove2me | solution 1 for BayesProphet.MultiSec.Supplement.allocation_regret_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:39.993745+00:00
-- url     : https://prove2.me/submissions/334cd504-2609-4862-93e8-16d8ae372aef

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_Supplement_Arrivals
import Definitions.Def_BayesProphet_MultiSec_Supplement_Allocation

open BayesProphet
open BayesProphet.MultiSec
open BayesProphet.MultiSec.Supplement

theorem solution :
    ¬ ∀ (d n : ℕ) [NeZero n] (m : Fin n → ℕ) (bund : (j : Fin n) → Fin (m j) → Fin d → ℕ),
      (∀ j, Function.Injective (bund j)) →
      ∀ μ : Seminorm ℝ (Fin n → ℝ), (∀ y, μ y = 0 → y = 0) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (rew : (j : Fin n) → Fin (m j) → ℝ), (∀ j s, 0 ≤ rew j s) →
        ∀ (T : ℕ) (w : (Fin T → Fin n) → ℝ), IsArrivalLaw w →
        ∀ (c : Fin n → ℝ) (τ : Fin n → ℕ) (p : Fin n → ℝ),
          AllTimeDeviation w μ (fun j => κ * ((m j : ℝ) + 1) / 2) c τ →
          (∀ j, ∀ t ∈ Finset.Icc 1 T, probL w (fun θ => θ t = j) ≤ p j) →
        ∀ (B : Fin d → ℕ)
          (X : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j)) → ℝ),
          IsAllocFluidSelection bund rew w X →
        ∀ K : ℕ → (Fin (d + 1) → ℕ) → (j : Fin n) → Option (Fin (m j)),
          IsAllocArgmaxSelection X K →
          allocationExpectedRegret bund rew w K B ≤
            allocRmax rew * ∑ j, p j * (c j + τ j) := by
              classical
              intro H
              let m : Fin 1 → ℕ := fun _ => 2
              let bund : (j : Fin 1) → Fin (m j) → Fin 1 → ℕ := fun _ s _ => if s.val = 0 then 3 else 2
              let rew : (j : Fin 1) → Fin (m j) → ℝ := fun _ s => if s.val = 0 then 3 else 1
              let w : (Fin 1 → Fin 1) → ℝ := fun _ => 1
              have hinj : ∀ j, Function.Injective (bund j) := by
                intro j a b hab
                have h0 := congrFun hab 0
                have ha : a.val < 2 := a.2
                have hb : b.val < 2 := b.2
                apply Fin.ext
                simp only [bund] at h0
                split_ifs at h0 <;> omega
              obtain ⟨κ, hκ, H⟩ := H 1 1 m bund hinj (normSeminorm ℝ (Fin 1 → ℝ))
                (fun y hy => norm_eq_zero.mp hy)
              -- mean vector at time 1
              have hcount : ∀ θ : ℕ → Fin 1, ∀ j, cumCount θ 1 j = 1 := by
                intro θ j
                have : ∀ a, θ a = j := fun a => Subsingleton.elim _ _
                simp [cumCount, this]
              have hmean : ∀ j, meanCount w 1 j = 1 := by
                intro j
                simp [meanCount, expectL, hcount, w]
              have hmeanv : meanVec w 1 = fun _ => 1 := by
                funext j; exact hmean j
              have hcv : ∀ θ : ℕ → Fin 1, countVec θ 1 = fun _ => 1 := by
                intro θ; funext j; simp [countVec, hcount]
              -- existence of an optimal selection
              have hopt : ∀ (b : Fin 2 → ℝ) (y : Fin 1 → ℝ), (allocFluidFeas bund b y).Nonempty →
                  ∃ x, x ∈ allocFluidOpt bund rew b y := by
                intro b y hne
                have hclosed : IsClosed (allocFluidFeas bund b y) := by
                  have : allocFluidFeas bund b y =
                    (⋂ i, {x | ∑ j, ∑ s, (allocCons bund j s i : ℝ) * x j s ≤ b i}) ∩
                    ((⋂ j, {x | ∑ s, x j s = y j}) ∩ ⋂ j, ⋂ s, {x | 0 ≤ x j s}) := by
                    ext x; simp [allocFluidFeas]
                  rw [this]
                  refine IsClosed.inter (isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)) (IsClosed.inter (isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)) (isClosed_iInter fun j => isClosed_iInter fun s => isClosed_le (by fun_prop) (by fun_prop)))
                have hsub : allocFluidFeas bund b y ⊆ Set.Icc (fun _ _ => 0) (fun j _ => y j) := by
                  rintro x ⟨_, h2, h3⟩
                  refine ⟨fun j s => h3 j s, fun j s => ?_⟩
                  show x j s ≤ y j
                  rw [← h2 j]
                  exact Finset.single_le_sum (f := fun s => x j s) (fun s _ => h3 j s) (Finset.mem_univ s)
                have hcomp : IsCompact (allocFluidFeas bund b y) :=
                  isCompact_Icc.of_isClosed_subset hclosed hsub
                obtain ⟨x, hx, hmax⟩ := hcomp.exists_isMaxOn hne
                  (f := fun x => ∑ j, ∑ s, x j s * allocReward rew j s) (by fun_prop)
                exact ⟨x, hx, fun x' hx' => hmax hx'⟩
              let X : ℕ → (Fin 2 → ℕ) → (j : Fin 1) → Option (Fin (m j)) → ℝ := fun t b =>
                if h : (allocFluidFeas bund (fun i => (b i : ℝ)) (meanVec w t)).Nonempty then
                  Classical.choose (hopt _ _ h) else 0
              have hX : IsAllocFluidSelection bund rew w X := by
                intro t b h
                simp only [X, dif_pos h]
                exact Classical.choose_spec (hopt _ _ h)
              have hKex : ∀ t b j, ∃ s0, ∀ s, X t b j s ≤ X t b j s0 := fun t b j =>
                Finite.exists_max (X t b j)
              choose K hK using hKex
              have hfin := H rew (by intro j s; simp only [rew]; split_ifs <;> norm_num) 1 w
                (by constructor
                    · intro x; simp [w]
                    · simp [w])
                (fun _ => 0) (fun _ => 0) (fun _ => 1)
                (by
                  intro j
                  refine ⟨le_refl _, ?_⟩
                  intro t ht _
                  have ht1 : t = 1 := by simpa using ht
                  subst ht1
                  rw [hmean, hmeanv]
                  have hpos : ¬ (1 / (2 * (κ * ((m j : ℝ) + 1) / 2)) ≤ 0) := by
                    rw [not_le]; positivity
                  have hz : ∀ θ : ℕ → Fin 1, (normSeminorm ℝ (Fin 1 → ℝ)) (countVec θ 1 - fun _ => (1:ℝ)) = 0 := by
                    intro θ
                    rw [hcv θ, sub_self, map_zero]
                  simp only [hz, probL, if_neg hpos]
                  simp)
                (by
                  intro j t _
                  have : ∀ a : Fin 1, a = j := fun a => Subsingleton.elim _ _
                  simp [probL, w, this])
                (fun _ => 2) X hX K (fun t b j s => hK t b j s)
              have hb0 : allocInit (fun _ : Fin 1 => 2) 1 0 = 2 := by simp [allocInit]
              have hb1 : allocInit (fun _ : Fin 1 => 2) 1 1 = 1 := by simp [allocInit]
              set b0 : Fin 2 → ℕ := allocInit (fun _ : Fin 1 => 2) 1 with hbdef
              have c00 : allocCons bund 0 (some (0 : Fin 2)) 0 = 3 := by simp [allocCons, bund]
              have c01 : allocCons bund 0 (some (0 : Fin 2)) 1 = 0 := by simp [allocCons]
              have c10 : allocCons bund 0 (some (1 : Fin 2)) 0 = 2 := by simp [allocCons, bund]
              have c11 : allocCons bund 0 (some (1 : Fin 2)) 1 = 0 := by simp [allocCons]
              have cn0 : allocCons bund 0 none 0 = 0 := by simp [allocCons]
              have cn1 : allocCons bund 0 none 1 = 1 := by simp [allocCons]
              have r0 : allocReward rew 0 (some (0 : Fin 2)) = 3 := by simp [allocReward, rew]
              have r1 : allocReward rew 0 (some (1 : Fin 2)) = 1 := by simp [allocReward, rew]
              have rn : allocReward rew 0 none = 0 := rfl
              have hsum : ∀ f : Option (Fin (m 0)) → ℝ,
                  ∑ s, f s = f none + f (some (0 : Fin 2)) + f (some (1 : Fin 2)) := by
                intro f
                rw [Fintype.sum_option, add_assoc]
                congr 1
                exact Fin.sum_univ_two (fun s : Fin 2 => f (some s))
              have hfeas : ∀ x : (j : Fin 1) → Option (Fin (m j)) → ℝ,
                  x ∈ allocFluidFeas bund (fun i => (b0 i : ℝ)) (meanVec w 1) ↔
                  (3 * x 0 (some (0 : Fin 2)) + 2 * x 0 (some (1 : Fin 2)) ≤ 2 ∧ x 0 none ≤ 1) ∧
                  (x 0 none + x 0 (some (0 : Fin 2)) + x 0 (some (1 : Fin 2)) = 1) ∧
                  (0 ≤ x 0 none ∧ 0 ≤ x 0 (some (0 : Fin 2)) ∧ 0 ≤ x 0 (some (1 : Fin 2))) := by
                intro x
                unfold allocFluidFeas
                show (_ ∧ _ ∧ _) ↔ _
                rw [Fin.forall_fin_two, Fin.forall_fin_one, Fin.forall_fin_one,
                  Fin.sum_univ_one, Fin.sum_univ_one, hsum, hsum, hsum, hmeanv]
                beta_reduce
                rw [hb0, hb1, c00, c01, c10, c11, cn0, cn1]
                refine and_congr (and_congr ?_ ?_) (and_congr Iff.rfl ?_)
                · norm_num
                · norm_num
                · constructor
                  · intro h; exact ⟨h _, h _, h _⟩
                  · rintro ⟨h1, h2, h3⟩ s
                    match s with
                    | none => exact h1
                    | some ⟨0, _⟩ => exact h2
                    | some ⟨1, _⟩ => exact h3
              let xs : (j : Fin 1) → Option (Fin (m j)) → ℝ := fun j s =>
                match s with
                | none => 1/3
                | some a => if a.val = 0 then 2/3 else 0
              have xs0 : xs 0 (some (0 : Fin 2)) = 2/3 := by simp [xs]
              have xs1 : xs 0 (some (1 : Fin 2)) = 0 := by simp [xs]
              have xsn : xs 0 none = 1/3 := rfl
              have hxs : xs ∈ allocFluidFeas bund (fun i => (b0 i : ℝ)) (meanVec w 1) := by
                rw [hfeas, xs0, xs1, xsn]; norm_num
              have hXopt := hX 1 b0 ⟨xs, hxs⟩
              obtain ⟨hXf, hXm⟩ := hXopt
              have hXm := hXm xs hxs
              rw [Fin.sum_univ_one, Fin.sum_univ_one, hsum, hsum, r0, r1, rn, xs0, xs1, xsn] at hXm
              rw [hfeas] at hXf
              obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩ := hXf
              have hKeq : K 1 b0 0 = some (0 : Fin 2) := by
                have hk := hK 1 b0 0 (some (0 : Fin 2))
                rcases hk' : K 1 b0 0 with _ | ⟨a, ha⟩
                · rw [hk'] at hk; exfalso; linarith
                · have ha2 : a < 2 := ha
                  interval_cases a
                  · rfl
                  · rw [hk'] at hk; exfalso
                    change _ ≤ X 1 b0 0 (some (1 : Fin 2)) at hk
                    linarith
              have hreg : ∀ θ : ℕ → Fin 1, 1 ≤
                  (allocationProblem bund rew).regret (fluidBayesAllocation bund K) 1 b0 θ := by
                intro θ
                have hθ : θ 1 = 0 := Subsingleton.elim _ _
                have hon : (allocationProblem bund rew).onlineValue (fluidBayesAllocation bund K) 1 b0 θ = 0 := by
                  have hst : (allocationProblem bund rew).onlineState (fluidBayesAllocation bund K) 1 b0 θ 1 = b0 := rfl
                  have hact : fluidBayesAllocation bund K 1 θ b0 = ⟨0, none⟩ := by
                    unfold fluidBayesAllocation
                    rw [hθ, hKeq, if_neg]
                    intro hle
                    have := hle 0
                    rw [c00, hb0] at this
                    exact absurd this (by norm_num)
                  unfold OnlineProblem.onlineValue
                  rw [Finset.Icc_self, Finset.sum_singleton, hst, hact]
                  simp [allocationProblem, allocReward]
                have hoff : 1 ≤ (allocationProblem bund rew).offVal θ 1 b0 := by
                  unfold OnlineProblem.offVal
                  have hf : (⟨0, some (1 : Fin 2)⟩ : (j : Fin 1) × Option (Fin (m j))) ∈
                      (allocationProblem bund rew).feasible b0 := by
                    show allocCons bund 0 (some (1 : Fin 2)) ≤ b0
                    intro i
                    fin_cases i
                    · show allocCons bund 0 (some (1 : Fin 2)) 0 ≤ b0 0
                      rw [c10, hb0]
                    · show allocCons bund 0 (some (1 : Fin 2)) 1 ≤ b0 1
                      rw [c11]; exact Nat.zero_le _
                  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove ⟨_, hf⟩)
                  simp only [OnlineProblem.offVal, allocationProblem, zero_add, hθ, if_true, r1, add_zero, le_refl]
                unfold OnlineProblem.regret
                rw [hon]; linarith
              have hge : 1 ≤ allocationExpectedRegret bund rew w K (fun _ => 2) := by
                unfold allocationExpectedRegret expectL
                simp only [Fintype.sum_unique, w, one_mul]
                exact hreg _
              simp at hfin
              linarith
