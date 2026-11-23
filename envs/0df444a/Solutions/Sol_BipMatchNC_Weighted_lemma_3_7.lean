-- Prove2me | solution 1 for BipMatchNC.Weighted.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:53:46.557863+00:00
-- url     : https://prove2.me/submissions/42fab9de-ee80-4afb-865d-2cccec179a60

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph
import Theorems.Thm_AssignmentGame_CoreCorners_worth_le_permutation_bound
import Theorems.Thm_AssignmentGame_CoreCorners_optimal_matching_has_dual_potentials

set_option autoImplicit false

open BipMatchNC.Weighted

/-- Lemma 3.7, via a tight assignment-game dual certificate. -/
theorem solution (n : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) (hPM : G.HasPM) :
    ∃ y z : Fin n → ℝ,
      IsBalancedDualFeasible G.adj w y z ∧
      (∀ (y' z' : Fin n → ℝ), IsBalancedDualFeasible G.adj w y' z' →
        dualValue y z ≤ dualValue y' z') ∧
      dualValue y z = (G.maxPMWeight w : ℝ) ∧
      (∀ i, y i ≤ 0) ∧ (∀ j, 0 ≤ z j) ∧
      (∀ i, |y i| ≤ 2 * n * (G.maxEdgeWeight w : ℝ)) ∧
      (∀ j, |z j| ≤ 2 * n * (G.maxEdgeWeight w : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [IsBalancedDualFeasible, dualValue, BipGraph.maxPMWeight,
        maxPerfectMatchingWeight, BipGraph.maxEdgeWeight, matchingWeight]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  obtain ⟨π₀, hπ₀⟩ := hPM
  let S := {σ : Equiv.Perm (Fin n) // G.IsPerfectMatching σ}
  letI : Nonempty S := ⟨⟨π₀, hπ₀⟩⟩
  obtain ⟨π', hπ'⟩ := Finite.exists_max (fun σ : S => matchingWeight w σ.1)
  let π : Equiv.Perm (Fin n) := π'.1
  have hπ : G.IsPerfectMatching π := π'.2
  have hmax (σ : Equiv.Perm (Fin n)) (hσ : G.IsPerfectMatching σ) :
      matchingWeight w σ ≤ matchingWeight w π := hπ' ⟨σ, hσ⟩
  have hweight : matchingWeight w π = G.maxPMWeight w := by
    unfold BipGraph.maxPMWeight maxPerfectMatchingWeight
    apply Nat.le_antisymm
    · apply Finset.le_sup (f := fun σ : Equiv.Perm (Fin n) => matchingWeight w σ)
      exact (@Finset.mem_filter _ _ (fun _ => Fintype.decidableForallFintype)
        Finset.univ π).mpr ⟨Finset.mem_univ π, hπ⟩
    · apply Finset.sup_le
      intro σ hσ
      apply hmax σ
      exact ((@Finset.mem_filter _ _ (fun _ => Fintype.decidableForallFintype)
        Finset.univ σ).mp hσ).2
  have hw_le {i j : Fin n} (hij : G.adj i j = true) :
      w i j ≤ G.maxEdgeWeight w := by
    unfold BipGraph.maxEdgeWeight
    apply Finset.le_sup (b := (i, j)) (f := fun e : Fin n × Fin n => w e.1 e.2)
    simp [hij]
  let C : ℝ := ((n : ℝ) - 1) * (G.maxEdgeWeight w : ℝ)
  let a : Fin n → Fin n → ℝ := fun i j =>
    if G.adj i j then C + (w i j : ℝ) else 0
  have hC : 0 ≤ C := by
    dsimp [C]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  have hW : (0 : ℝ) ≤ (G.maxEdgeWeight w : ℝ) := by positivity
  have ha (i j : Fin n) : 0 ≤ a i j := by
    by_cases hij : G.adj i j = true
    · simp [a, hij, add_nonneg hC (Nat.cast_nonneg (w i j))]
    · simp [a, hij]
  have hsum_pm (f : Equiv.Perm (Fin n)) (hf : G.IsPerfectMatching f) :
      (∑ i, a i (f i)) = (n : ℝ) * C + (matchingWeight w f : ℝ) := by
    simp_rw [a, if_pos (hf _)]
    simp [Finset.sum_add_distrib, matchingWeight, Nat.cast_sum, nsmul_eq_mul, mul_add]
  let K : ℝ := (n : ℝ) * C + (G.maxPMWeight w : ℝ)
  have hK (f : Equiv.Perm (Fin n)) : (∑ i, a i (f i)) ≤ K := by
    by_cases hf : G.IsPerfectMatching f
    · rw [hsum_pm f hf]
      have h : (matchingWeight w f : ℝ) ≤ (matchingWeight w π : ℝ) := by
        exact_mod_cast hmax f hf
      dsimp [K]
      rw [← hweight]
      exact add_le_add (le_refl ((n : ℝ) * C)) h
    · have hf' : ¬ ∀ i, G.adj i (f i) = true := hf
      push_neg at hf'
      obtain ⟨i₀, hi₀⟩ := hf'
      have hi₀false : G.adj i₀ (f i₀) = false := by
        cases h : G.adj i₀ (f i₀) <;> simp_all
      have hai₀ : a i₀ (f i₀) = 0 := by simp [a, hi₀false]
      calc
        (∑ i, a i (f i)) = ∑ i ∈ Finset.univ.erase i₀, a i (f i) := by
          symm
          exact Finset.sum_erase Finset.univ hai₀
        _ ≤ ∑ _i ∈ Finset.univ.erase i₀, (C + (G.maxEdgeWeight w : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hij : G.adj i (f i) = true
          · simp only [a, if_pos hij]
            have h := hw_le hij
            have h' : (w i (f i) : ℝ) ≤ (G.maxEdgeWeight w : ℝ) := by exact_mod_cast h
            linarith
          · have hijfalse : G.adj i (f i) = false := by
              cases h : G.adj i (f i) <;> simp_all
            simp [a, hijfalse, add_nonneg hC hW]
        _ = ((Finset.univ.erase i₀).card : ℝ) * (C + (G.maxEdgeWeight w : ℝ)) := by
          simp [nsmul_eq_mul, mul_add]
        _ = (n : ℝ) * C := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i₀)]
          simp only [Finset.card_univ, Fintype.card_fin]
          rw [Nat.cast_sub hn1]
          dsimp [C]
          push_cast
          ring
        _ ≤ K := by
          dsimp [K]
          exact le_add_of_nonneg_right (by positivity)
  let P : Finset (Fin n × Fin n) := Finset.univ.image (fun i => (i, π i))
  have hPmem (i : Fin n) : (i, π i) ∈ P := by simp [P]
  have hP : AssignmentGame.CoreCorners.IsMatching Finset.univ Finset.univ P := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp
    · intro p hp q hq hpq
      simp only [P, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨j, rfl⟩ := hq
      have : i = j := hpq
      subst j
      rfl
    · intro p hp q hq hpq
      simp only [P, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨j, rfl⟩ := hq
      have hij : i = j := π.injective hpq
      subst j
      rfl
  have hsumP : (∑ p ∈ P, a p.1 p.2) = (n : ℝ) * C + (matchingWeight w π : ℝ) := by
    rw [show P = Finset.univ.image (fun i => (i, π i)) from rfl, Finset.sum_image]
    · exact hsum_pm π hπ
    · intro i hi j hj hij
      exact congrArg Prod.fst hij
  have hworth_le : AssignmentGame.CoreCorners.worth a Finset.univ Finset.univ ≤ K :=
    AssignmentGame.CoreCorners.worth_le_permutation_bound a ha π K hK
  have hPmatchings : P ∈ AssignmentGame.CoreCorners.matchings Finset.univ Finset.univ := by
    simp [AssignmentGame.CoreCorners.matchings, hP]
  have hworth_ge : (∑ p ∈ P, a p.1 p.2) ≤
      AssignmentGame.CoreCorners.worth a Finset.univ Finset.univ := by
    unfold AssignmentGame.CoreCorners.worth
    exact Finset.le_sup' (fun Q : Finset (Fin n × Fin n) => ∑ p ∈ Q, a p.1 p.2) hPmatchings
  have hopt : (∑ p ∈ P, a p.1 p.2) =
      AssignmentGame.CoreCorners.worth a Finset.univ Finset.univ := by
    apply le_antisymm
    · exact hworth_ge
    · rw [hsumP, hweight]
      exact hworth_le
  obtain ⟨u, v, hu, hv, huv, htight⟩ :=
    AssignmentGame.CoreCorners.optimal_matching_has_dual_potentials a ha P hP hopt
  have ht (i : Fin n) : u i + v (π i) = C + (w i (π i) : ℝ) := by
    simpa [a, hπ i] using htight (i, π i) (hPmem i)
  have hub (i : Fin n) : u i ≤ C + (G.maxEdgeWeight w : ℝ) := by
    have h := ht i
    have hnonneg := hv (π i)
    have hbound := hw_le (hπ i)
    have hbound' : (w i (π i) : ℝ) ≤ (G.maxEdgeWeight w : ℝ) := by exact_mod_cast hbound
    linarith
  have hvb (j : Fin n) : v j ≤ C + (G.maxEdgeWeight w : ℝ) := by
    have h := ht (π.symm j)
    simp only [Equiv.apply_symm_apply] at h
    have hnonneg := hu (π.symm j)
    have hbound := hw_le (hπ (π.symm j))
    have hbound' : (w (π.symm j) j : ℝ) ≤ (G.maxEdgeWeight w : ℝ) := by
      simpa only [Equiv.apply_symm_apply] using (show (w (π.symm j) (π (π.symm j)) : ℝ) ≤
        (G.maxEdgeWeight w : ℝ) by exact_mod_cast hbound)
    linarith
  let y : Fin n → ℝ := fun i => u i - (C + (G.maxEdgeWeight w : ℝ))
  let z : Fin n → ℝ := fun j => v j + (G.maxEdgeWeight w : ℝ)
  have huvsum : (∑ i, u i) + (∑ j, v j) =
      (n : ℝ) * C + (G.maxPMWeight w : ℝ) := by
    calc
      (∑ i, u i) + (∑ j, v j) = ∑ i, (u i + v (π i)) := by
        rw [Finset.sum_add_distrib, Equiv.sum_comp π]
      _ = ∑ i, (C + (w i (π i) : ℝ)) := Finset.sum_congr rfl fun i _ => ht i
      _ = (n : ℝ) * C + (matchingWeight w π : ℝ) := by
        simp [Finset.sum_add_distrib, matchingWeight, Nat.cast_sum, nsmul_eq_mul, mul_add]
      _ = (n : ℝ) * C + (G.maxPMWeight w : ℝ) := by rw [hweight]
  have hysum : (∑ i, y i) = (∑ i, u i) -
      (n : ℝ) * (C + (G.maxEdgeWeight w : ℝ)) := by
    dsimp [y]
    rw [Finset.sum_sub_distrib]
    simp [nsmul_eq_mul, mul_add]
  have hzsum : (∑ j, z j) = (∑ j, v j) +
      (n : ℝ) * (G.maxEdgeWeight w : ℝ) := by
    dsimp [z]
    rw [Finset.sum_add_distrib]
    simp [nsmul_eq_mul, mul_add]
  have hvalue : dualValue y z = (G.maxPMWeight w : ℝ) := by
    unfold dualValue
    rw [hysum, hzsum]
    have hCW : C + (G.maxEdgeWeight w : ℝ) = (n : ℝ) * (G.maxEdgeWeight w : ℝ) := by
      dsimp [C]
      ring
    rw [hCW]
    dsimp [C] at huvsum ⊢
    nlinarith [huvsum]
  have hfeas : IsBalancedDualFeasible G.adj w y z := by
    intro i j hij
    have h := huv i j
    simp only [a, if_pos hij] at h
    dsimp [y, z]
    linarith
  have hweak (y' z' : Fin n → ℝ) (hfeas' : IsBalancedDualFeasible G.adj w y' z')
      (f : Equiv.Perm (Fin n)) (hf : G.IsPerfectMatching f) :
      (matchingWeight w f : ℝ) ≤ dualValue y' z' := by
    change (↑(∑ i, w i (f i)) : ℝ) ≤ ∑ i, y' i + ∑ j, z' j
    rw [Nat.cast_sum]
    calc
      (∑ i, (w i (f i) : ℝ)) ≤ ∑ i, (y' i + z' (f i)) :=
        Finset.sum_le_sum fun i _ => hfeas' i (f i) (hf i)
      _ = ∑ i, y' i + ∑ j, z' j := by rw [Finset.sum_add_distrib, Equiv.sum_comp f]
  refine ⟨y, z, hfeas, ?_, hvalue, ?_, ?_, ?_, ?_⟩
  · intro y' z' hfeas'
    rw [hvalue, ← hweight]
    exact hweak y' z' hfeas' π hπ
  · intro i
    exact sub_nonpos.mpr (hub i)
  · intro j
    exact add_nonneg (hv j) hW
  · intro i
    have hu0 := hu i
    have hui := hub i
    have hCW : C + (G.maxEdgeWeight w : ℝ) = (n : ℝ) * (G.maxEdgeWeight w : ℝ) := by
      dsimp [C]
      ring
    rw [abs_le]
    constructor
    · change -((2 : ℝ) * n * (G.maxEdgeWeight w : ℝ)) ≤
        u i - (C + (G.maxEdgeWeight w : ℝ))
      rw [hCW]
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    · change u i - (C + (G.maxEdgeWeight w : ℝ)) ≤
        (2 : ℝ) * n * (G.maxEdgeWeight w : ℝ)
      rw [hCW]
      nlinarith [show (0 : ℝ) ≤ n by positivity]
  · intro j
    have hv0 := hv j
    have hvj := hvb j
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hC2 : C + 2 * (G.maxEdgeWeight w : ℝ) ≤
        2 * (n : ℝ) * (G.maxEdgeWeight w : ℝ) := by
      dsimp [C]
      nlinarith
    rw [abs_of_nonneg (add_nonneg hv0 hW)]
    change v j + (G.maxEdgeWeight w : ℝ) ≤
      2 * (n : ℝ) * (G.maxEdgeWeight w : ℝ)
    linarith

#print axioms solution
