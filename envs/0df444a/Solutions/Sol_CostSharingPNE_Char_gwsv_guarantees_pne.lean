-- Prove2me | solution 1 for CostSharingPNE.Char.gwsv_guarantees_pne
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:18:48.324461+00:00
-- url     : https://prove2.me/submissions/cc7c246e-2513-4dbc-b6e2-d4c4b2a72b61

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem

open CostSharingPNE.Char

namespace CSPGwsvPNEAux

variable {n : ℕ} (ω : WeightSystem n)

/-- `q_T / ∑_{j ∈ T̄} λ_j` (zero at `T = ∅`). -/
noncomputable def coef (V : Welfare n) (T : Finset (Fin n)) : ℝ :=
  mobius V T / ∑ j ∈ tbar ω T, ω.lam j

/-- The block-`k` potential `Q_k(S) = ∑_{T ⊆ S, T ⊆ blocks ≥ k} q_T / λ(T̄)`. -/
noncomputable def Q (V : Welfare n) (k : Fin ω.K) (S : Finset (Fin n)) : ℝ :=
  ∑ T ∈ S.powerset, if (∀ j ∈ T, k ≤ ω.block j) then coef ω V T else 0

/-- The increment of `Q_k` when `i` joins `R`. -/
noncomputable def E (V : Welfare n) (k : Fin ω.K) (i : Fin n) (R : Finset (Fin n)) : ℝ :=
  ∑ t ∈ R.powerset, if (∀ j ∈ insert i t, k ≤ ω.block j) then coef ω V (insert i t) else 0

lemma mem_tbar (i : Fin n) (T : Finset (Fin n)) :
    i ∈ tbar ω T ↔ i ∈ T ∧ ∀ j ∈ T, ω.block i ≤ ω.block j := by
  unfold tbar
  split_ifs with h
  · rw [Finset.mem_filter]
    constructor
    · rintro ⟨hi, he⟩
      refine ⟨hi, fun j hj => ?_⟩
      rw [he]; exact Finset.inf'_le _ hj
    · rintro ⟨hi, hle⟩
      refine ⟨hi, le_antisymm ?_ (Finset.inf'_le _ hi)⟩
      exact Finset.le_inf' _ _ hle
  · simp only [Finset.notMem_empty, false_iff, not_and]
    intro hi; exact absurd ⟨i, hi⟩ h

lemma gwsv_insert (V : Welfare n) (i : Fin n) (R : Finset (Fin n)) (hi : i ∉ R) :
    gwsv ω V i (insert i R) = ω.lam i * E ω V (ω.block i) i R := by
  unfold gwsv E
  rw [Finset.sum_filter, Finset.sum_powerset_insert hi, Finset.mul_sum]
  have h1 : ∑ t ∈ R.powerset, (if i ∈ tbar ω t then
      (ω.lam i / ∑ j ∈ tbar ω t, ω.lam j) * mobius V t else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [if_neg]
    rw [mem_tbar]
    rintro ⟨h, -⟩; exact hi (ht h)
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro t _
  have : i ∈ tbar ω (insert i t) ↔ ∀ j ∈ insert i t, ω.block i ≤ ω.block j := by
    rw [mem_tbar]; simp
  by_cases hc : ∀ j ∈ insert i t, ω.block i ≤ ω.block j
  · rw [if_pos (this.mpr hc), if_pos hc, coef]; ring
  · rw [if_neg (fun h => hc (this.mp h)), if_neg hc, mul_zero]

lemma Q_insert (V : Welfare n) (k : Fin ω.K) (i : Fin n) (R : Finset (Fin n)) (hi : i ∉ R) :
    Q ω V k (insert i R) = Q ω V k R + E ω V k i R := by
  unfold Q E
  rw [Finset.sum_powerset_insert hi]

lemma E_zero (V : Welfare n) (k : Fin ω.K) (i : Fin n) (R : Finset (Fin n))
    (hk : ω.block i < k) : E ω V k i R = 0 := by
  unfold E
  apply Finset.sum_eq_zero
  intro t _
  rw [if_neg]
  intro h
  exact absurd (h i (Finset.mem_insert_self _ _)) (not_le.mpr hk)

variable {m : ℕ}

/-- Players other than `i` on resource `r`. -/
def D (a : Fin n → Finset (Fin m)) (i : Fin n) (r : Fin m) : Finset (Fin n) :=
  (players a r).erase i

lemma players_eq (a : Fin n → Finset (Fin m)) (i : Fin n) (r : Fin m) :
    players a r = if r ∈ a i then insert i (D a i r) else D a i r := by
  unfold D
  split_ifs with h
  · rw [Finset.insert_erase]
    simp [players, h]
  · rw [Finset.erase_eq_of_notMem]
    simp [players, h]

lemma D_update (a : Fin n → Finset (Fin m)) (i : Fin n) (b : Finset (Fin m)) (r : Fin m) :
    D (Function.update a i b) i r = D a i r := by
  unfold D players
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, Function.update_of_ne hj]

lemma notMem_D (a : Fin n → Finset (Fin m)) (i : Fin n) (r : Fin m) : i ∉ D a i r := by
  unfold D; simp

/-- The block-`k` potential of a profile. -/
noncomputable def Phi (W : Fin m → Welfare n) (g : Welfare n → Welfare n) (k : Fin ω.K)
    (a : Fin n → Finset (Fin m)) : ℝ :=
  ∑ r, Q ω (g (W r)) k (players a r)

lemma Phi_split (W : Fin m → Welfare n) (g : Welfare n → Welfare n) (k : Fin ω.K)
    (a : Fin n → Finset (Fin m)) (i : Fin n) :
    Phi ω W g k a = ∑ r, Q ω (g (W r)) k (D a i r) +
      ∑ r ∈ a i, E ω (g (W r)) k i (D a i r) := by
  unfold Phi
  have : ∀ r, Q ω (g (W r)) k (players a r) = Q ω (g (W r)) k (D a i r) +
      (if r ∈ a i then E ω (g (W r)) k i (D a i r) else 0) := by
    intro r
    rw [players_eq a i r]
    split_ifs
    · exact Q_insert ω _ k i _ (notMem_D a i r)
    · ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]

lemma utility_eq (W : Fin m → Welfare n) (g : Welfare n → Welfare n)
    (a : Fin n → Finset (Fin m)) (i : Fin n) :
    utility W (fun V => gwsv ω (g V)) a i =
      ω.lam i * ∑ r ∈ a i, E ω (g (W r)) (ω.block i) i (D a i r) := by
  unfold utility
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [players_eq a i r, if_pos hr]
  exact gwsv_insert ω _ i _ (notMem_D a i r)

end CSPGwsvPNEAux

open CSPGwsvPNEAux in
theorem solution (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n))
    (ω : WeightSystem n) (g : Welfare n → Welfare n) :
    GuaranteesPNE 𝕎 (fun W => gwsv ω (g W)) := by
  intro m _ W _ A hA
  classical
  set P := Fintype.piFinset A with hP
  have hPne : P.Nonempty := Fintype.piFinset_nonempty.mpr hA
  let v : (Fin n → Finset (Fin m)) → Lex (Fin ω.K → ℝ) :=
    fun a => toLex (fun k => Phi ω W g (Fin.rev k) a)
  obtain ⟨a, haP, hmax⟩ := Finset.exists_max_image P v hPne
  refine ⟨a, fun i => (Fintype.mem_piFinset.mp haP) i, ?_⟩
  intro i b hb
  by_contra hlt
  rw [not_le] at hlt
  set a' := Function.update a i b with ha'
  have ha'P : a' ∈ P := by
    rw [hP, Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj; simp [ha', hb]
    · rw [ha', Function.update_of_ne hj]; exact (Fintype.mem_piFinset.mp haP) j
  have hD : ∀ r, D a' i r = D a i r := fun r => D_update a i b r
  have hai : a' i = b := by simp [ha']
  -- Higher blocks unchanged.
  have hhi : ∀ k, ω.block i < k → Phi ω W g k a' = Phi ω W g k a := by
    intro k hk
    rw [Phi_split ω W g k a' i, Phi_split ω W g k a i]
    simp only [hD, E_zero ω _ k i _ hk, Finset.sum_const_zero]
  -- Own block strictly increases.
  have hown : Phi ω W g (ω.block i) a < Phi ω W g (ω.block i) a' := by
    rw [Phi_split ω W g _ a' i, Phi_split ω W g _ a i]
    simp only [hD]
    rw [utility_eq, utility_eq] at hlt
    simp only [hD] at hlt
    have hl := ω.lam_pos i
    have := lt_of_mul_lt_mul_left hlt hl.le
    linarith
  have hv : v a < v a' := by
    show Pi.Lex (· < ·) (· < ·) _ _
    refine ⟨Fin.rev (ω.block i), ?_, ?_⟩
    · intro j hj
      change Phi ω W g (Fin.rev j) a = Phi ω W g (Fin.rev j) a'
      symm
      apply hhi
      rw [Fin.lt_rev_iff] at hj
      exact hj
    · change Phi ω W g (Fin.rev (Fin.rev (ω.block i))) a <
        Phi ω W g (Fin.rev (Fin.rev (ω.block i))) a'
      rw [Fin.rev_rev]
      exact hown
  exact absurd (hmax a' ha'P) (not_le.mpr hv)
