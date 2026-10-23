-- Prove2me | solution 1 for CircletTSP.Facet.stsp_vectorSpan_eq_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:14:07.124972+00:00
-- url     : https://prove2.me/submissions/be993b98-10e6-4e68-89d8-7c47db7ae3ea

import Mathlib
import Definitions.Def_CircletTSP_Facet_Setting

set_option autoImplicit false

open scoped BigOperators

namespace CircletTSP.Facet.TourCounts

lemma rotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    by_cases hi : i = Fin.last n
    · subst i
      simp at hv
      omega
    · simp [hi] at hv

lemma tourVec_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    0 ≤ MetricTSP.tourVec π u v := by
  unfold MetricTSP.tourVec
  positivity

lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma tourVec_eq_step_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = ∑ k : Fin n,
      if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
      then (1 : ℝ) else 0 := by
  unfold MetricTSP.tourVec MetricTSP.tourSteps
  exact Finset.natCast_card_filter _ _

lemma single_edge_mass_of_lt {n : ℕ} (a b : Fin n) (hab : a < b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  have heq (u v : Fin n) :
      (u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ↔ u = a ∧ v = b := by
    constructor
    · rintro ⟨huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨rfl, rfl⟩
      · exact (lt_asymm hab huv).elim
    · rintro ⟨rfl, rfl⟩
      exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
  simp_rw [heq]
  simp [ite_and]

lemma single_edge_mass {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (∑ u : Fin n, ∑ v : Fin n,
      if u < v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) then (1 : ℝ) else 0) = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact single_edge_mass_of_lt a b h
  · simpa [or_comm, and_comm] using single_edge_mass_of_lt b a h

lemma tour_unordered_mass {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, ∑ v : Fin n, if u < v then MetricTSP.tourVec π u v else 0) = n := by
  have hexpand (u v : Fin n) :
      (if u < v then MetricTSP.tourVec π u v else 0) =
      ∑ k : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
    rw [tourVec_eq_step_sum]
    by_cases huv : u < v <;> simp [huv]
  simp_rw [hexpand]
  calc
    _ = ∑ u : Fin n, ∑ k : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ u : Fin n, ∑ v : Fin n, if u < v ∧
        ((π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u))
        then (1 : ℝ) else 0 := by rw [Finset.sum_comm]
    _ = ∑ _k : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      apply single_edge_mass
      intro h
      exact rotate_ne_self hn k (π.injective h).symm
    _ = n := by simp

lemma cycLen_mem_range_of_lt {n : ℕ} (u v : Fin n) (huv : u < v) :
    cycLen n u v ∈ Finset.Icc 1 (n / 2) := by
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := huv
  simp only [Finset.mem_Icc, cycLen,
    Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt huv')]
  omega

lemma sum_lenCount_eq_mass (n : ℕ) (x : Fin n → Fin n → ℝ) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i x) =
      ∑ u : Fin n, ∑ v : Fin n, if u < v then x u v else 0 := by
  unfold lenCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases huv : u < v
  · have hmem := cycLen_mem_range_of_lt u v huv
    simp [huv, hmem]
  · simp [huv]

lemma sum_lenCount_tour {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.Icc 1 (n / 2), lenCount n i (MetricTSP.tourVec π)) = n := by
  rw [sum_lenCount_eq_mass]
  exact tour_unordered_mass hn π

lemma lenCount_nonneg {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) :
    0 ≤ lenCount n i (MetricTSP.tourVec π) := by
  unfold lenCount
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact tourVec_nonneg π u v
  · exact le_rfl

end CircletTSP.Facet.TourCounts

namespace CircletTSP.Facet.TourCounts

lemma tourVec_eq_successors {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    MetricTSP.tourVec π u v =
      (if π (finRotate n (π.symm u)) = v then 1 else 0) +
      (if π (finRotate n (π.symm v)) = u then 1 else 0) := by
  rw [tourVec_eq_step_sum]
  have hsplit (k : Fin n) :
      (if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
        then (1 : ℝ) else 0) =
      (if k = π.symm u then if π (finRotate n k) = v then 1 else 0 else 0) +
      (if k = π.symm v then if π (finRotate n k) = u then 1 else 0 else 0) := by
    have hku : π k = u ↔ k = π.symm u := π.eq_symm_apply.symm
    have hkv : π k = v ↔ k = π.symm v := π.eq_symm_apply.symm
    simp only [hku, hkv]
    by_cases hu : k = π.symm u
    · by_cases hv : k = π.symm v
      · exact (huv (π.symm.injective (hu.symm.trans hv))).elim
      · simp [hu, huv]
    · by_cases hv : k = π.symm v
      · simp [hv, Ne.symm huv]
      · simp [hu, hv]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

lemma tourVec_diagonal_zero {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    MetricTSP.tourVec π u u = 0 := by
  rw [tourVec_eq_step_sum]
  apply Finset.sum_eq_zero
  intro k _
  have hnot : ¬ (π k = u ∧ π (finRotate n k) = u) := by
    rintro ⟨ha, hb⟩
    exact rotate_ne_self hn k (π.injective (hb.trans ha.symm))
  simp only [or_self, if_neg hnot]

def successorPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π.symm.trans ((finRotate n).trans π)

lemma successor_ne_self {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    successorPerm π u ≠ u := by
  intro h
  have h' : finRotate n (π.symm u) = π.symm u := by
    apply π.injective
    simpa [successorPerm] using h
  exact rotate_ne_self hn (π.symm u) h'

lemma tourVec_eq_successors_all {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v =
      (if successorPerm π u = v then 1 else 0) +
      (if successorPerm π v = u then 1 else 0) := by
  by_cases huv : u = v
  · subst v
    simp [tourVec_diagonal_zero hn, successor_ne_self hn]
  · exact tourVec_eq_successors π u v huv

lemma tourVec_row_sum {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    (∑ v : Fin n, MetricTSP.tourVec π u v) = 2 := by
  simp_rw [tourVec_eq_successors_all hn]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ v : Fin n, if successorPerm π u = v then (1 : ℝ) else 0) = 1 := by simp
  have hright : (∑ v : Fin n, if successorPerm π v = u then (1 : ℝ) else 0) = 1 := by
    simp_rw [← (successorPerm π).eq_symm_apply]
    simp
  rw [hleft, hright]
  norm_num

lemma tourVec_trans {n : ℕ} (π σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec (π.trans σ) (σ u) (σ v) = MetricTSP.tourVec π u v := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps]

end CircletTSP.Facet.TourCounts


namespace CircletTSP.Facet.TwoOpt

noncomputable section

lemma rotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    by_cases hi : i = Fin.last n
    · subst i
      simp at hv
      omega
    · simp [hi] at hv

lemma tourVec_eq_step_sum {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = ∑ k : Fin n,
      if (π k = u ∧ π (finRotate n k) = v) ∨ (π k = v ∧ π (finRotate n k) = u)
      then (1 : ℝ) else 0 := by
  unfold MetricTSP.tourVec MetricTSP.tourSteps
  exact Finset.natCast_card_filter _ _

def edge {n : ℕ} (a b : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => (if a = i ∧ b = j then 1 else 0) + (if b = i ∧ a = j then 1 else 0)

lemma edge_symm {n : ℕ} (a b : Fin n) : edge a b = edge b a := by
  funext i j
  exact add_comm _ _

lemma edge_apply {n : ℕ} {a b : Fin n} (hab : a ≠ b) (i j : Fin n) :
    edge a b i j = if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0 := by
  simp only [edge]
  split_ifs <;> simp_all
  all_goals aesop

lemma tourVec_eq_sum_edges {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n)) :
    MetricTSP.tourVec π = ∑ k : Fin n, edge (π k) (π (finRotate n k)) := by
  funext i j
  rw [tourVec_eq_step_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hne : π k ≠ π (finRotate n k) := by
    intro h
    exact rotate_ne_self hn k (π.injective h).symm
  rw [edge_apply hne]

lemma adjacent_swap_difference {n : ℕ} (hn : 1 < n) (π : Equiv.Perm (Fin n))
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (_had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hrab : finRotate n a = b) (hrbc : finRotate n b = c) (hrcd : finRotate n c = d) :
    MetricTSP.tourVec π - MetricTSP.tourVec ((Equiv.swap b c).trans π) =
      edge (π a) (π b) + edge (π c) (π d) - edge (π a) (π c) - edge (π b) (π d) := by
  have he (k : Fin n) :
      edge (π k) (π (finRotate n k)) -
          edge (π (Equiv.swap b c k)) (π (Equiv.swap b c (finRotate n k))) =
        (if k = a then edge (π a) (π b) - edge (π a) (π c) else 0) +
        (if k = c then edge (π c) (π d) - edge (π b) (π d) else 0) := by
    by_cases hka : k = a
    · subst k
      rw [hrab, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
      simp only [ite_true, if_neg hac, add_zero]
    by_cases hkb : k = b
    · subst k
      rw [hrbc, Equiv.swap_apply_left, Equiv.swap_apply_right]
      simp only [if_neg hab.symm, if_neg hbc, add_zero]
      rw [edge_symm (π c) (π b), sub_self]
    by_cases hkc : k = c
    · subst k
      rw [hrcd, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbd.symm hcd.symm]
      simp only [if_neg hac.symm, ite_true, zero_add]
    have hrb : finRotate n k ≠ b := by
      intro h
      exact hka ((finRotate n).injective (h.trans hrab.symm))
    have hrc : finRotate n k ≠ c := by
      intro h
      exact hkb ((finRotate n).injective (h.trans hrbc.symm))
    rw [Equiv.swap_apply_of_ne_of_ne hkb hkc, Equiv.swap_apply_of_ne_of_ne hrb hrc]
    simp only [if_neg hka, if_neg hkc, sub_self, zero_add]
  rw [tourVec_eq_sum_edges hn, tourVec_eq_sum_edges hn, ← Finset.sum_sub_distrib]
  simp only [Equiv.trans_apply]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

lemma rotate_small {n k : ℕ} (h : k + 1 < n) :
    finRotate n ⟨k, by omega⟩ = ⟨k + 1, h⟩ := by
  cases n with
  | zero => omega
  | succ n => exact finRotate_of_lt (by omega)

lemma four_cycle_mem_span {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    edge a b + edge c d - edge a c - edge b d ∈ vectorSpan ℝ (STSP n) := by
  let g : Fin 4 → Fin n := ![a, b, c, d]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have hn4 : 4 ≤ n := by simpa using Fintype.card_le_of_injective g hg
  let f : Fin 4 → Fin n := fun i => i.castLE hn4
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simpa [f] using congrArg (Fin.val : Fin n → ℕ) hij
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hr01 : finRotate n (f 0) = f 1 := by
    exact rotate_small (by omega : 0 + 1 < n)
  have hr12 : finRotate n (f 1) = f 2 := by
    exact rotate_small (by omega : 1 + 1 < n)
  have hr23 : finRotate n (f 2) = f 3 := by
    exact rotate_small (by omega : 2 + 1 < n)
  have ht := adjacent_swap_difference (by omega : 1 < n) π (f 0) (f 1) (f 2) (f 3)
    (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide))
    (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide)) hr01 hr12 hr23
  have tour_mem (ρ : Equiv.Perm (Fin n)) : MetricTSP.tourVec ρ ∈ STSP n :=
    subset_convexHull ℝ _ (Set.mem_range_self ρ)
  have hv := vsub_mem_vectorSpan ℝ (tour_mem π) (tour_mem ((Equiv.swap (f 1) (f 2)).trans π))
  change MetricTSP.tourVec π - MetricTSP.tourVec ((Equiv.swap (f 1) (f 2)).trans π) ∈ _ at hv
  rw [ht] at hv
  simpa [hπ, g] using hv

end
end CircletTSP.Facet.TwoOpt

namespace CircletTSP.Facet.AnnihilatorProof

noncomputable section

def edge {n : ℕ} (i j : Fin n) : Fin n → Fin n → ℝ :=
  fun u v => (if i = u ∧ j = v then 1 else 0) + (if j = u ∧ i = v then 1 else 0)

theorem edge_symm {n : ℕ} (i j : Fin n) : edge i j = edge j i := by
  funext u v
  exact add_comm _ _

theorem potentials_of_quadrilateral (n : ℕ) (hn : 3 ≤ n)
    (w : Fin n → Fin n → ℝ) (hsymm : ∀ i j, w i j = w j i)
    (hquad : ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      w a b + w c d = w a c + w b d) :
    ∃ p : Fin n → ℝ, ∀ i j, i ≠ j → w i j = p i + p j := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  have hac : a ≠ c := by simp [a, c]
  have hbc : b ≠ c := by simp [b, c]
  let t : ℝ := (w a b + w a c - w b c) / 2
  let p : Fin n → ℝ := fun i => if i = a then t else w a i - t
  have hstar (i : Fin n) (hia : i ≠ a) (hib : i ≠ b) :
      w b i = w a i + w b c - w a c := by
    by_cases hic : i = c
    · subst i
      ring
    · have h := hquad a c i b hac (Ne.symm hia) hab (Ne.symm hic) (Ne.symm hbc) hib
      rw [hsymm i b, hsymm c b] at h
      linarith
  refine ⟨p, ?_⟩
  intro i j hij
  by_cases hia : i = a
  · subst i
    have hja : j ≠ a := hij.symm
    simp [p, hja]
  by_cases hja : j = a
  · subst j
    rw [hsymm]
    simp [p, hia]
  have hpi : p i = w a i - t := by simp [p, hia]
  have hpj : p j = w a j - t := by simp [p, hja]
  rw [hpi, hpj]
  by_cases hib : i = b
  · subst i
    have h := hstar j hja hij.symm
    dsimp [t]
    linarith
  by_cases hjb : j = b
  · subst j
    have h := hstar i hia hij
    rw [hsymm i b]
    dsimp [t]
    linarith
  have hq := hquad a i b j (Ne.symm hia) hab (Ne.symm hja) hib hij (Ne.symm hjb)
  have hs := hstar j hja hjb
  dsimp [t]
  linarith

theorem sum_edges {n : ℕ} (x : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, x i j = x j i) :
    (∑ i, ∑ j, x i j • edge i j) = x + x := by
  funext a b
  simp [edge, Finset.sum_add_distrib, mul_add, mul_ite, ite_and, hsymm b a]

theorem functional_zero_of_potentials {n : ℕ}
    (φ : (Fin n → Fin n → ℝ) →ₗ[ℝ] ℝ) (p : Fin n → ℝ)
    (hpot : ∀ i j, i ≠ j → φ (edge i j) = p i + p j)
    (x : Fin n → Fin n → ℝ) (hsymm : ∀ i j, x i j = x j i)
    (hdiag : ∀ i, x i i = 0) (hrow : ∀ i, ∑ j, x i j = 0) : φ x = 0 := by
  have hsum : φ x + φ x = ∑ i, ∑ j, x i j * φ (edge i j) := by
    rw [← map_add, ← sum_edges x hsymm]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hterms (i j : Fin n) :
      x i j * φ (edge i j) = x i j * (p i + p j) := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · rw [hpot i j hij]
  have hcol (j : Fin n) : ∑ i, x i j = 0 := by
    have heq : (∑ i, x i j) = ∑ i, x j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsymm i j
    rw [heq, hrow]
  have hleft : (∑ i, ∑ j, x i j * p i) = 0 := by
    simp only [← Finset.sum_mul, hrow, zero_mul, Finset.sum_const_zero]
  have hright : (∑ i, ∑ j, x i j * p j) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, zero_mul, Finset.sum_const_zero]
  simp_rw [hterms, mul_add, Finset.sum_add_distrib] at hsum
  rw [hleft, hright] at hsum
  linarith

theorem zero_degree_mem_of_quadrilaterals (n : ℕ) (hn : 3 ≤ n)
    (S : Submodule ℝ (Fin n → Fin n → ℝ))
    (hquad : ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      edge a b + edge c d - edge a c - edge b d ∈ S)
    (x : Fin n → Fin n → ℝ) (hsymm : ∀ i j, x i j = x j i)
    (hdiag : ∀ i, x i i = 0) (hrow : ∀ i, ∑ j, x i j = 0) : x ∈ S := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S x).mp
  intro φ hφ
  have hvanish := (Submodule.mem_dualAnnihilator φ).mp hφ
  have hwquad : ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      φ (edge a b) + φ (edge c d) = φ (edge a c) + φ (edge b d) := by
    intro a b c d hab hac had hbc hbd hcd
    have hz := hvanish _ (hquad a b c d hab hac had hbc hbd hcd)
    simp only [map_sub, map_add] at hz
    linarith
  obtain ⟨p, hp⟩ := potentials_of_quadrilateral n hn (fun i j => φ (edge i j))
    (fun i j => congrArg φ (edge_symm i j)) hwquad
  exact functional_zero_of_potentials φ p hp x hsymm hdiag hrow

def zeroDegree (n : ℕ) : Submodule ℝ (Fin n → Fin n → ℝ) where
  carrier := {x | (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧ ∀ i, ∑ j, x i j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      simp only [Pi.add_apply, hx.1 i j, hy.1 i j]
    · intro i
      simp [hx.2.1 i, hy.2.1 i]
    · intro i
      simp only [Pi.add_apply, Finset.sum_add_distrib, hx.2.2 i, hy.2.2 i, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      simp only [Pi.smul_apply, hx.1 i j]
    · intro i
      simp [hx.2.1 i]
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx.2.2 i, mul_zero]

theorem vectorSpan_le_zeroDegree (n : ℕ) (hn : 3 ≤ n) :
    vectorSpan ℝ (STSP n) ≤ zeroDegree n := by
  have hn2 : 1 < n := by omega
  rw [STSP, ← direction_affineSpan, affineSpan_convexHull, direction_affineSpan, vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨π, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    change MetricTSP.tourVec π i j - MetricTSP.tourVec σ i j =
      MetricTSP.tourVec π j i - MetricTSP.tourVec σ j i
    rw [TourCounts.tourVec_symm π i j, TourCounts.tourVec_symm σ i j]
  · intro i
    change MetricTSP.tourVec π i i - MetricTSP.tourVec σ i i = 0
    rw [TourCounts.tourVec_diagonal_zero hn2, TourCounts.tourVec_diagonal_zero hn2, sub_self]
  · intro i
    change (∑ j, (MetricTSP.tourVec π i j - MetricTSP.tourVec σ i j)) = 0
    rw [Finset.sum_sub_distrib, TourCounts.tourVec_row_sum hn2,
      TourCounts.tourVec_row_sum hn2, sub_self]

end
end CircletTSP.Facet.AnnihilatorProof

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    (vectorSpan ℝ (STSP n) : Set (Fin n → Fin n → ℝ)) =
      {x | (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧ ∀ i, ∑ j, x i j = 0} := by
  ext x
  constructor
  · intro hx
    exact AnnihilatorProof.vectorSpan_le_zeroDegree n hn hx
  · intro hx
    apply AnnihilatorProof.zero_degree_mem_of_quadrilaterals n hn (vectorSpan ℝ (STSP n))
      ?_ x hx.1 hx.2.1 hx.2.2
    intro a b c d hab hac had hbc hbd hcd
    exact TwoOpt.four_cycle_mem_span a b c d hab hac had hbc hbd hcd
