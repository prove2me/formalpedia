-- Prove2me | solution 1 for DynamicOnlineLP.DLA.expected_partialOPT_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T04:59:54.158991+00:00
-- url     : https://prove2.me/submissions/f62c11b4-fb3b-4b9f-86aa-e9a3441b655f

import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Instance

open scoped BigOperators
open DynamicOnlineLP.DLA

private theorem feasible_optimum_exists {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    ∃ x : α → ℝ, IsPrimalOptimal S π a d x ∧ (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
      (∀ j, j ∉ S → x j = 0) ∧ primalObj S π x = optValue S π a d := by
  classical
  let K : Set (α → ℝ) := {x | IsFeasible S a d x} ∩ Set.Icc 0 1
  have hclosed : IsClosed {x : α → ℝ | IsFeasible S a d x} := by
    have heq : {x : α → ℝ | IsFeasible S a d x} =
        (⋂ i : Fin m, {x : α → ℝ | ∑ t ∈ S, a t i * x t ≤ d i}) ∩
        (⋂ j : α, ⋂ _ : j ∈ S, {x : α → ℝ | 0 ≤ x j ∧ x j ≤ 1}) := by
      ext x
      simp [IsFeasible]
    rw [heq]
    apply IsClosed.inter
    · exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
        (isClosed_le continuous_const (continuous_apply j)).inter
          (isClosed_le (continuous_apply j) continuous_const)
  have hcompact : IsCompact K := isCompact_Icc.inter_left hclosed
  have hzero : (0 : α → ℝ) ∈ K := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      simpa using hd i
    · simp
    · exact ⟨le_rfl, by intro j; norm_num⟩
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩
    (show ContinuousOn (primalObj S π) K by unfold primalObj; fun_prop)
  let z : α → ℝ := fun j ↦ if j ∈ S then x j else 0
  have hzfeas : IsFeasible S a d z := by
    constructor
    · simpa [z] using hx.1.1
    · intro j hj
      simpa [z, hj] using hx.1.2 j hj
  have hzbox : ∀ j, 0 ≤ z j ∧ z j ≤ 1 := by
    intro j
    by_cases hj : j ∈ S
    · simpa [z, hj] using And.intro (hx.2.1 j) (hx.2.2 j)
    · simp [z, hj]
  have hobj : primalObj S π z = primalObj S π x := by simp [primalObj, z]
  have hbound (w : α → ℝ) (hw : IsFeasible S a d w) :
      primalObj S π w ≤ primalObj S π z := by
    let w' : α → ℝ := fun j ↦ if j ∈ S then w j else 0
    have hw' : w' ∈ K := by
      refine ⟨?_, ?_⟩
      · constructor
        · simpa [w'] using hw.1
        · intro j hj
          simpa [w', hj] using hw.2 j hj
      · constructor <;> intro j <;> by_cases hj : j ∈ S
        · simpa [w', hj] using (hw.2 j hj).1
        · simp [w', hj]
        · simpa [w', hj] using (hw.2 j hj).2
        · simp [w', hj]
    rw [hobj]
    simpa [primalObj, w'] using hmax hw'
  refine ⟨z, ⟨hzfeas, hbound⟩, hzbox, ?_, ?_⟩
  · intro j hj
    simp [z, hj]
  · have hbd : BddAbove (primalObj S π '' {x | IsFeasible S a d x}) := by
      refine ⟨primalObj S π z, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact hbound w hw
    apply le_antisymm
    · exact le_csSup hbd ⟨z, hzfeas, rfl⟩
    · apply csSup_le
      · exact ⟨primalObj S π z, z, hzfeas, rfl⟩
      · rintro y ⟨w, hw, rfl⟩
        exact hbound w hw

private theorem sum_perm_indicator {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (S : Finset α) (j : α) :
    (∑ σ : Equiv.Perm α, if σ.symm j ∈ S then (1 : ℝ) else 0) =
      (Fintype.card (Equiv.Perm α) : ℝ) * S.card / Fintype.card α := by
  classical
  let f (k : α) : ℝ := ∑ σ : Equiv.Perm α, if σ.symm k ∈ S then 1 else 0
  have hsame (k : α) : f k = f j := by
    dsimp [f]
    rw [← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap j k))
      (fun σ : Equiv.Perm α ↦ if σ.symm k ∈ S then (1 : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro σ _
    change (if σ.symm ((Equiv.swap j k).symm k) ∈ S then (1 : ℝ) else 0) = _
    simp
  have htotal : ∑ k : α, f k = (Fintype.card (Equiv.Perm α) : ℝ) * S.card := by
    dsimp [f]
    rw [Finset.sum_comm]
    have hinner (σ : Equiv.Perm α) :
        (∑ k : α, if σ.symm k ∈ S then (1 : ℝ) else 0) = S.card := by
      rw [Equiv.sum_comp σ.symm (fun k ↦ if k ∈ S then (1 : ℝ) else 0)]
      simp
    simp_rw [hinner]
    simp
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change f j = _
  apply (eq_div_iff hcard).2
  calc
    f j * (Fintype.card α : ℝ) = ∑ k : α, f j := by simp [mul_comm]
    _ = ∑ k : α, f k := Finset.sum_congr rfl (fun k _ ↦ (hsame k).symm)
    _ = _ := htotal

private theorem firstTimes_card {n ℓ : ℕ} (hℓ : ℓ ≤ n) :
    (firstTimes n ℓ).card = ℓ := by
  classical
  let e : ↥(firstTimes n ℓ) ≃ Fin ℓ := {
    toFun := fun t ↦ ⟨t.val.val, by simpa [firstTimes] using t.property⟩
    invFun := fun t ↦ ⟨⟨t.val, lt_of_lt_of_le t.isLt hℓ⟩, by simp [firstTimes, t.isLt]⟩
    left_inv := by intro t; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro t; apply Fin.ext; rfl }
  simpa using Fintype.card_congr e

private theorem sum_reindex_supported {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (σ : Equiv.Perm α) (x f : α → ℝ)
    (hx : ∀ j, j ∉ S → x j = 0) :
    (∑ j, f j * x (σ.symm j)) = ∑ t ∈ S, f (σ t) * x t := by
  classical
  rw [← Equiv.sum_comp σ (fun j ↦ f j * x (σ.symm j))]
  simp only [σ.symm_apply_apply]
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro j _ hj
  rw [hx j hj, mul_zero]

theorem solution {m n : ℕ} (I : Instance m n) (hb : ∀ i : Fin m, 0 ≤ I.b i)
    (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    avgPerm (fun σ : Equiv.Perm (Fin n) =>
        I.partialOPT σ ℓ (fun i => ((ℓ : ℝ) / (n : ℝ)) * I.b i)) ≤
      ((ℓ : ℝ) / (n : ℝ)) * I.OPT := by
  classical
  let S := firstTimes n ℓ
  let c : ℝ := (ℓ : ℝ) / n
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hchoices (σ : Equiv.Perm (Fin n)) := feasible_optimum_exists S (I.arrPi σ)
    (I.arrA σ) (fun i ↦ c * I.b i) (fun i ↦ mul_nonneg hc (hb i))
  choose x hxopt hxbox hxout hxeq using hchoices
  by_cases hzero : ℓ = 0
  · subst ℓ
    have hval (σ : Equiv.Perm (Fin n)) :
        I.partialOPT σ 0 (fun i ↦ (0 : ℝ) / n * I.b i) = 0 := by
      have hxzero : primalObj S (I.arrPi σ) (x σ) = 0 := by
        simp [primalObj, S, firstTimes]
      simpa [Instance.partialOPT, S, c] using (hxeq σ).symm.trans hxzero
    have havg : avgPerm (fun σ ↦ I.partialOPT σ 0 (fun i ↦ (0 : ℝ) / n * I.b i)) = 0 := by
      simp_rw [hval]
      simp [avgPerm]
    simpa using havg.le
  have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero hzero
  have hn : 0 < n := lt_of_lt_of_le hℓpos hℓ
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcpos : 0 < c := div_pos (by exact_mod_cast hℓpos) (by exact_mod_cast hn)
  let P : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin n)))
  have hPc : 0 < P * c := mul_pos hP hcpos
  let z : Fin n → ℝ := fun j ↦ (∑ σ, x σ (σ.symm j)) / (P * c)
  have hzbox (j : Fin n) : 0 ≤ z j ∧ z j ≤ 1 := by
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun σ _ ↦ (hxbox σ _).1) hPc.le
    · apply (div_le_one hPc).2
      calc
        (∑ σ, x σ (σ.symm j)) ≤
            ∑ σ : Equiv.Perm (Fin n), if σ.symm j ∈ S then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro σ _
          by_cases hj : σ.symm j ∈ S
          · simpa [hj] using (hxbox σ (σ.symm j)).2
          · simp [hj, hxout σ _ hj]
        _ = P * c := by
          rw [sum_perm_indicator, firstTimes_card hℓ]
          simp only [Fintype.card_fin]
          dsimp [P, c]
          ring
  have hzload (i : Fin m) : ∑ j, I.a j i * z j ≤ I.b i := by
    have hnum :
        (∑ j, I.a j i * (∑ σ, x σ (σ.symm j))) ≤ (P * c) * I.b i := by
      calc
        (∑ j, I.a j i * (∑ σ, x σ (σ.symm j))) =
            ∑ σ, ∑ t ∈ S, I.arrA σ t i * x σ t := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro σ _
          exact sum_reindex_supported S σ (x σ) (fun j ↦ I.a j i) (hxout σ)
        _ ≤ ∑ _σ : Equiv.Perm (Fin n), c * I.b i := by
          apply Finset.sum_le_sum
          intro σ _
          exact (hxopt σ).1.1 i
        _ = (P * c) * I.b i := by simp [P]; ring
    dsimp [z]
    simp_rw [← mul_div_assoc, ← Finset.sum_div]
    exact (div_le_iff₀ hPc).2 (by nlinarith [hnum])
  have hzfeas : IsFeasible Finset.univ I.a I.b z :=
    ⟨hzload, fun j _ ↦ hzbox j⟩
  obtain ⟨w, hw, _, _, hweq⟩ := feasible_optimum_exists Finset.univ I.π I.a I.b hb
  have hobjle : primalObj Finset.univ I.π z ≤ I.OPT := by
    rw [Instance.OPT, ← hweq]
    exact hw.2 z hzfeas
  have hobj :
      primalObj Finset.univ I.π z =
        (∑ σ : Equiv.Perm (Fin n),
          I.partialOPT σ ℓ (fun i ↦ c * I.b i)) / (P * c) := by
    unfold primalObj
    dsimp [z]
    simp_rw [← mul_div_assoc, ← Finset.sum_div, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    rw [sum_reindex_supported S σ (x σ) I.π (hxout σ)]
    exact hxeq σ
  rw [hobj] at hobjle
  have hsumle := (div_le_iff₀ hPc).mp hobjle
  unfold avgPerm
  change (∑ σ, I.partialOPT σ ℓ (fun i ↦ c * I.b i)) / P ≤ c * I.OPT
  apply (div_le_iff₀ hP).2
  nlinarith [hsumle]
