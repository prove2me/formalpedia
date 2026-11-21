-- Prove2me | solution 1 for CardinalMatching.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:14:49.514023+00:00
-- url     : https://prove2.me/submissions/8b2041d7-3abb-413c-b84f-f6f528d630a3

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

namespace Aux_CM

open Finset

theorem exists_delta {A G : Type} [Fintype A] [Fintype G] (s : Finset A) (N : Finset G)
    (f : A → G → ℝ) (hf : ∀ i ∈ s, ∀ j, j ∉ N → 0 < f i j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, ∀ j, j ∉ N → δ ≤ f i j := by
  classical
  by_cases hne : (s ×ˢ (univ \ N)).Nonempty
  · refine ⟨(s ×ˢ (univ \ N)).inf' hne (fun ij => f ij.1 ij.2), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      rintro ⟨i, j⟩ hij
      simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at hij
      exact hf i hij.1 j hij.2
    · intro i hi j hj
      have hmem : (i, j) ∈ s ×ˢ (univ \ N) := by
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨hi, hj⟩
      exact Finset.inf'_le (fun ij : A × G => f ij.1 ij.2) hmem
  · refine ⟨1, one_pos, ?_⟩
    intro i hi j hj
    exfalso
    apply hne
    refine ⟨(i, j), ?_⟩
    simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨hi, hj⟩

theorem hall_tight {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (s : Finset A) :
    s.card ≤ (s.biUnion (fun i => univ.filter (fun j => α i * u i j = q i + p j))).card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨N, hN⟩ : ∃ N, N = s.biUnion (fun i => univ.filter (fun j => α i * u i j = q i + p j)) :=
    ⟨_, rfl⟩
  rw [← hN] at hlt
  obtain ⟨δ, hδ, hδle⟩ := exists_delta s N (fun i j => q i + p j - α i * u i j) (by
    intro i hi j hj
    have hne : α i * u i j ≠ q i + p j := by
      intro heq
      apply hj
      rw [hN, Finset.mem_biUnion]
      exact ⟨i, hi, by simp [heq]⟩
    have h1 := hfeas i j
    have h2 : α i * u i j < q i + p j := lt_of_le_of_ne h1 hne
    show 0 < q i + p j - α i * u i j
    linarith)
  have key := hopt (fun j => p j + if j ∈ N then δ else 0)
    (fun i => q i - if i ∈ s then δ else 0) (by
    intro i j
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ N
    · simp only [hi, hj, if_true]
      have := hfeas i j; linarith
    · simp only [hi, hj, if_true, if_false]
      have h2 : δ ≤ q i + p j - α i * u i j := hδle i hi j hj
      linarith
    · simp only [hi, hj, if_true, if_false]
      have := hfeas i j; linarith
    · simp only [hi, hj, if_false]
      have := hfeas i j; linarith)
  have e1 : ∑ i, (q i - if i ∈ s then δ else 0) = ∑ i, q i - s.card * δ := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ j, (p j + if j ∈ N then δ else 0) = ∑ j, p j + N.card * δ := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [e1, e2] at key
  have hc : (N.card : ℝ) < s.card := by exact_mod_cast hlt
  nlinarith

theorem row_bound {A G : Type} [Fintype G] (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j) (i : A) (z : G → ℝ)
    (hz1 : ∑ j, z j = 1) (hz0 : ∀ j, 0 ≤ z j) :
    α i * ∑ j, u i j * z j ≤ q i + ∑ j, p j * z j := by
  calc α i * ∑ j, u i j * z j = ∑ j, (α i * u i j) * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, (q i + p j) * z j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hfeas i j) (hz0 j))
    _ = q i * ∑ j, z j + ∑ j, p j * z j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = q i + ∑ j, p j * z j := by rw [hz1, mul_one]

theorem strong_le {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x) :
    ∑ i, q i + ∑ j, p j ≤ weightedWelfare α u x := by
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i => univ.filter (fun j => α i * u i j = q i + p j))).mp (hall_tight α u p q hfeas hopt)
  have hcard : Fintype.card A = Fintype.card G := by
    have h1 : ∑ i, ∑ j, x i j = (Fintype.card A : ℝ) := by
      rw [Finset.sum_congr rfl (fun i _ => hx.1 i)]; simp
    have h2 : ∑ j, ∑ i, x i j = (Fintype.card G : ℝ) := by
      rw [Finset.sum_congr rfl (fun j _ => hx.2.1 j)]; simp
    rw [Finset.sum_comm] at h1
    exact_mod_cast h1.symm.trans h2
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
  let y : A → G → ℝ := fun i j => if f i = j then 1 else 0
  have hy : IsFracPerfectMatching y := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp [y]
    · intro j
      obtain ⟨i0, hi0⟩ := hfbij.2 j
      rw [Finset.sum_eq_single i0]
      · simp [y, hi0]
      · intro b _ hb
        simp only [y]
        rw [if_neg]
        intro h
        exact hb (hfinj (h.trans hi0.symm))
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro i j
      simp only [y]
      split_ifs <;> norm_num
  have hWy : weightedWelfare α u y = ∑ i, q i + ∑ j, p j := by
    unfold weightedWelfare
    have hrow : ∀ i, α i * ∑ j, u i j * y i j = q i + p (f i) := by
      intro i
      have hfi := hf i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfi
      have hs : ∑ j, u i j * y i j = u i (f i) := by
        simp only [y, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [hs]
      exact hfi
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_add_distrib, hfbij.sum_comp p]
  have := hW y hy
  linarith

theorem budget_eq {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x)
    (i : A) :
    α i * ∑ j, u i j * x i j - q i = ∑ j, p j * x i j := by
  have hle : ∀ a ∈ (univ : Finset A), α a * ∑ j, u a j * x a j - q a ≤ ∑ j, p j * x a j := by
    intro a _
    have := row_bound α u p q hfeas a (x a) (hx.1 a) (fun j => hx.2.2 a j)
    linarith
  have hS := strong_le α u p q x hx hfeas hopt hW
  have hsum1 : ∑ a, (α a * ∑ j, u a j * x a j - q a) = weightedWelfare α u x - ∑ a, q a := by
    unfold weightedWelfare
    rw [Finset.sum_sub_distrib]
  have hsum2 : ∑ a, ∑ j, p j * x a j = ∑ j, p j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum, hx.2.1 j, mul_one]
  have heq : ∑ a, (α a * ∑ j, u a j * x a j - q a) = ∑ a, ∑ j, p j * x a j := by
    apply le_antisymm (Finset.sum_le_sum hle)
    rw [hsum1, hsum2]; linarith
  exact (Finset.sum_eq_sum_iff_of_le hle).mp heq i (Finset.mem_univ i)

theorem row_bound_le {A G : Type} [Fintype G] (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j) (i : A) (z : G → ℝ) (hq : 0 ≤ q i)
    (hz1 : ∑ j, z j ≤ 1) (hz0 : ∀ j, 0 ≤ z j) :
    α i * ∑ j, u i j * z j ≤ q i + ∑ j, p j * z j := by
  calc α i * ∑ j, u i j * z j = ∑ j, (α i * u i j) * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, (q i + p j) * z j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hfeas i j) (hz0 j))
    _ = q i * ∑ j, z j + ∑ j, p j * z j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ q i + ∑ j, p j * z j := by
        have := mul_le_of_le_one_right hq hz1
        linarith

theorem tight_of_pos {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x)
    (i : A) (j : G) (hj : 0 < x i j) : α i * u i j = q i + p j := by
  have hb := budget_eq α u p q x hx hfeas hopt hW i
  have hid : ∑ k, x i k * (q i + p k - α i * u i k) =
      q i * ∑ k, x i k + ∑ k, p k * x i k - α i * ∑ k, u i k * x i k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hzero : ∑ k, x i k * (q i + p k - α i * u i k) = 0 := by
    rw [hid, hx.1 i]; linarith
  have hnn : ∀ k ∈ (Finset.univ : Finset G), 0 ≤ x i k * (q i + p k - α i * u i k) := by
    intro k _
    have := hfeas i k
    exact mul_nonneg (hx.2.2 i k) (by linarith)
  have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hk with h | h
  · linarith
  · linarith

def OptB {G : Type} [Fintype G] (p u : G → ℝ) (t : ℝ) (y : G → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1 ∧ ∑ j, p j * y j ≤ t ∧
    ∀ y' : G → ℝ, (∀ j, 0 ≤ y' j) → ∑ j, y' j ≤ 1 → ∑ j, p j * y' j ≤ t →
      ∑ j, u j * y' j ≤ ∑ j, u j * y j

theorem opt_own {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x)
    (hα : ∀ i, 0 < α i) (hq : ∀ i, 0 ≤ q i) (i : A) :
    OptB p (u i) (∑ j, p j * x i j) (x i) := by
  unfold OptB
  refine ⟨fun j => hx.2.2 i j, le_of_eq (hx.1 i), le_rfl, ?_⟩
  intro y' hy0 hy1 hyc
  have h1 := row_bound_le α u p q hfeas i y' (hq i) hy1 hy0
  have h2 := budget_eq α u p q x hx hfeas hopt hW i
  have h3 : α i * ∑ j, u i j * y' j ≤ α i * ∑ j, u i j * x i j := by linarith
  exact le_of_mul_le_mul_left h3 (hα i)

theorem card_eq {A G : Type} [Fintype A] [Fintype G] (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x) : Fintype.card A = Fintype.card G := by
  have h1 : ∑ i, ∑ j, x i j = (Fintype.card A : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hx.1 i)]; simp
  have h2 : ∑ j, ∑ i, x i j = (Fintype.card G : ℝ) := by
    rw [Finset.sum_congr rfl (fun j _ => hx.2.1 j)]; simp
  rw [Finset.sum_comm] at h1
  exact_mod_cast h1.symm.trans h2

end Aux_CM

namespace Aux_CM

theorem stepValue_bounds (ε a b : ℝ) (hε : 0 < ε) (ℓ : ℕ) :
    min a b ≤ stepValue ε a b ℓ ∧ stepValue ε a b ℓ ≤ max a b := by
  unfold stepValue stepCount
  split_ifs with h1 h2
  · have h3 : (ℓ : ℝ) < |b - a| / ε := Nat.lt_ceil.mp h1
    rw [abs_of_nonneg (by linarith)] at h3
    have h4 : (ℓ : ℝ) * ε < b - a := by rwa [lt_div_iff₀ hε] at h3
    have h5 : (0:ℝ) ≤ ℓ * ε := mul_nonneg (Nat.cast_nonneg _) hε.le
    constructor
    · rw [min_eq_left h2]; linarith
    · rw [max_eq_right h2]; linarith
  · have h3 : (ℓ : ℝ) < |b - a| / ε := Nat.lt_ceil.mp h1
    push_neg at h2
    rw [abs_of_neg (by linarith)] at h3
    have h4 : (ℓ : ℝ) * ε < -(b - a) := by rwa [lt_div_iff₀ hε] at h3
    have h5 : (0:ℝ) ≤ ℓ * ε := mul_nonneg (Nat.cast_nonneg _) hε.le
    constructor
    · rw [min_eq_right h2.le]; linarith
    · rw [max_eq_left h2.le]; linarith
  · exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem chain_bounds {n : ℕ} (σ : Equiv.Perm (Fin n)) (ε : ℝ) (hε : 0 < ε) (a b : Fin n → ℝ)
    (v : Fin n → ℝ) (hv : v ∈ interpChain σ ε a b) (t : Fin n) :
    min (a t) (b t) ≤ v t ∧ v t ≤ max (a t) (b t) := by
  unfold interpChain at hv
  have hv' := List.mem_of_mem_dropLast hv
  rw [List.mem_flatMap] at hv'
  obtain ⟨m, _, hm⟩ := hv'
  rw [List.mem_map] at hm
  obtain ⟨ℓ, _, rfl⟩ := hm
  dsimp only
  split_ifs
  · exact ⟨min_le_right _ _, le_max_right _ _⟩
  · exact stepValue_bounds ε (a t) (b t) hε (ℓ + 1)
  · exact ⟨min_le_left _ _, le_max_left _ _⟩

theorem interp_bounds {n : ℕ} (u : Fin n → Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (ord : Fin n → Fin n → Equiv.Perm (Fin n)) (rev : Fin n → Fin n → Bool)
    (v : Fin n → ℝ) (hv : v ∈ interpVectors u ε ord rev) (t : Fin n) :
    ∃ i i', min (u i t) (u i' t) ≤ v t ∧ v t ≤ max (u i t) (u i' t) := by
  unfold interpVectors at hv
  rw [List.mem_flatMap] at hv
  obtain ⟨i, _, hi⟩ := hv
  rw [List.mem_flatMap] at hi
  obtain ⟨i', _, hi'⟩ := hi
  split_ifs at hi' with hr
  · obtain ⟨h1, h2⟩ := chain_bounds _ ε hε _ _ v hi' t
    exact ⟨i', i, h1, h2⟩
  · obtain ⟨h1, h2⟩ := chain_bounds _ ε hε _ _ v hi' t
    exact ⟨i, i', h1, h2⟩

theorem nd_facts {n : ℕ} (P : ModParams n) (hadm : P.Admissible) (a : P.Agent)
    (ha : ¬ P.IsDummy a) :
    (∀ r : Fin n × Fin P.k, 0 ≤ P.util a (Sum.inl r) ∧ P.util a (Sum.inl r) ≤ 1 ∧
      P.util a (Sum.inl r) ≤ ∑ ρ, P.u ρ r.1) ∧
    (∀ g, P.util a (Sum.inr g) = 2) := by
  obtain ⟨_, hu, _, _, hε, _, _, _⟩ := hadm
  rcases a with c | (m | dm)
  · refine ⟨fun r => ⟨(hu c.1 r.1).1, (hu c.1 r.1).2, ?_⟩, fun g => rfl⟩
    show P.u c.1 r.1 ≤ ∑ ρ, P.u ρ r.1
    exact Finset.single_le_sum (f := fun ρ => P.u ρ r.1) (fun ρ _ => (hu ρ r.1).1)
      (Finset.mem_univ c.1)
  · refine ⟨fun r => ?_, fun g => rfl⟩
    show 0 ≤ P.interp.get m r.1 ∧ P.interp.get m r.1 ≤ 1 ∧ P.interp.get m r.1 ≤ ∑ ρ, P.u ρ r.1
    obtain ⟨i, i', h1, h2⟩ := interp_bounds P.u P.ε hε P.ord P.rev (P.interp.get m)
      (List.get_mem P.interp m) r.1
    have hi := hu i r.1
    have hi' := hu i' r.1
    have hs1 : P.u i r.1 ≤ ∑ ρ, P.u ρ r.1 :=
      Finset.single_le_sum (f := fun ρ => P.u ρ r.1) (fun ρ _ => (hu ρ r.1).1) (Finset.mem_univ i)
    have hs2 : P.u i' r.1 ≤ ∑ ρ, P.u ρ r.1 :=
      Finset.single_le_sum (f := fun ρ => P.u ρ r.1) (fun ρ _ => (hu ρ r.1).1) (Finset.mem_univ i')
    exact ⟨le_trans (le_min hi.1 hi'.1) h1, le_trans h2 (max_le hi.2 hi'.2),
      le_trans h2 (max_le hs1 hs2)⟩
  · exact absurd trivial ha

theorem util_le {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ)
    (hadm : P.Admissible) (hx : IsFracPerfectMatching x) (hEF : IsEnvyFree P.util x)
    (hn : 2 ≤ n) (i : P.Agent) (hi : ¬ P.IsDummy i) :
    ∑ j, P.util i j * x i j ≤ 8 / 5 := by
  obtain ⟨hreg, hawe⟩ := nd_facts P hadm i hi
  obtain ⟨_, hu, hk0, _, _, _, _, _⟩ := hadm
  have hsplit : ∀ F : P.Good → ℝ, ∑ j, F j = ∑ r, F (Sum.inl r) + ∑ g, F (Sum.inr g) :=
    fun F => Fintype.sum_sum_type F
  have hutil_rr : ∀ (c r : Fin n × Fin P.k), P.util (Sum.inl c) (Sum.inl r) = P.u c.1 r.1 :=
    fun _ _ => rfl
  have hutil_ra : ∀ (c : Fin n × Fin P.k) (g : Fin (P.k / n)), P.util (Sum.inl c) (Sum.inr g) = 2 :=
    fun _ _ => rfl
  have hrow : ∀ a, ∑ r, x a (Sum.inl r) + ∑ g, x a (Sum.inr g) = 1 :=
    fun a => (hsplit (x a)).symm.trans (hx.1 a)
  -- upper bound for real agents
  have hUc : ∀ c : Fin n × Fin P.k,
      ∑ j, P.util (Sum.inl c) j * x (Sum.inl c) j ≤ 1 + ∑ g, x (Sum.inl c) (Sum.inr g) := by
    intro c
    rw [hsplit]
    have h1 : ∑ r, P.util (Sum.inl c) (Sum.inl r) * x (Sum.inl c) (Sum.inl r) ≤
        ∑ r, x (Sum.inl c) (Sum.inl r) := Finset.sum_le_sum (fun r _ => by
          rw [hutil_rr]; exact mul_le_of_le_one_left (hx.2.2 _ _) (hu c.1 r.1).2)
    have h2 : ∑ g, P.util (Sum.inl c) (Sum.inr g) * x (Sum.inl c) (Sum.inr g) =
        2 * ∑ g, x (Sum.inl c) (Sum.inr g) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun g _ => by rw [hutil_ra])
    have := hrow (Sum.inl c)
    linarith
  -- decomposition for i
  obtain ⟨Ui, hUi⟩ : ∃ U, U = ∑ r, P.util i (Sum.inl r) * x i (Sum.inl r) := ⟨_, rfl⟩
  obtain ⟨Ai, hAi⟩ : ∃ A, A = ∑ g, x i (Sum.inr g) := ⟨_, rfl⟩
  have hUtot : ∑ j, P.util i j * x i j = Ui + 2 * Ai := by
    rw [hsplit, hUi, hAi, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun g _ => by rw [hawe])
  have hUi_le : Ui ≤ 1 - Ai := by
    have h1 : ∑ r, P.util i (Sum.inl r) * x i (Sum.inl r) ≤ ∑ r, x i (Sum.inl r) :=
      Finset.sum_le_sum (fun r _ => mul_le_of_le_one_left (hx.2.2 _ _) (hreg r).2.1)
    have := hrow i
    rw [← hAi] at this
    linarith
  -- envy-freeness of real agents towards i
  have hEFc : ∀ c : Fin n × Fin P.k,
      ∑ r, P.u c.1 r.1 * x i (Sum.inl r) + 2 * Ai ≤ 1 + ∑ g, x (Sum.inl c) (Sum.inr g) := by
    intro c
    have e := hEF (Sum.inl c) i
    rw [hsplit] at e
    have h2 : ∑ g, P.util (Sum.inl c) (Sum.inr g) * x i (Sum.inr g) = 2 * Ai := by
      rw [hAi, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun g _ => by rw [hutil_ra])
    have h1 : ∑ r, P.util (Sum.inl c) (Sum.inl r) * x i (Sum.inl r) =
        ∑ r, P.u c.1 r.1 * x i (Sum.inl r) :=
      Finset.sum_congr rfl (fun r _ => by rw [hutil_rr])
    have := hUc c
    linarith
  have hsumc := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin n × Fin P.k))) => hEFc c)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsumc
  -- left: double sum
  have hcol_u : ∀ t, ∑ c : Fin n × Fin P.k, P.u c.1 t = (P.k : ℝ) * ∑ ρ, P.u ρ t := by
    intro t
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    simp
  have hleft : (P.k : ℝ) * Ui ≤ ∑ c : Fin n × Fin P.k, ∑ r, P.u c.1 r.1 * x i (Sum.inl r) := by
    rw [Finset.sum_comm, hUi, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    rw [← Finset.sum_mul, hcol_u]
    have h1 := (hreg r).2.2
    have h2 := hx.2.2 i (Sum.inl r)
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    have : (P.k : ℝ) * P.util i (Sum.inl r) ≤ (P.k : ℝ) * ∑ ρ, P.u ρ r.1 :=
      mul_le_mul_of_nonneg_left h1 hk
    nlinarith
  -- right: awesome mass of real agents
  have hright : ∑ c : Fin n × Fin P.k, ∑ g, x (Sum.inl c) (Sum.inr g) ≤ ((P.k / n : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    have : ∀ g : Fin (P.k / n), ∑ c : Fin n × Fin P.k, x (Sum.inl c) (Sum.inr g) ≤ 1 := by
      intro g
      have h := hx.2.1 (Sum.inr g)
      rw [Fintype.sum_sum_type] at h
      have hnn : 0 ≤ ∑ b : Fin P.interp.length ⊕ Fin (P.k / n - P.interp.length),
          x (Sum.inr b) (Sum.inr g) := Finset.sum_nonneg (fun b _ => hx.2.2 _ _)
      linarith
    calc ∑ g : Fin (P.k / n), ∑ c : Fin n × Fin P.k, x (Sum.inl c) (Sum.inr g)
        ≤ ∑ g : Fin (P.k / n), (1 : ℝ) := Finset.sum_le_sum (fun g _ => this g)
      _ = ((P.k / n : ℕ) : ℝ) := by simp
  have hconst1 : ∑ _c : Fin n × Fin P.k, (2 * Ai) = (n : ℝ) * P.k * (2 * Ai) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul]
  have hconst2 : ∑ _c : Fin n × Fin P.k, (1 : ℝ) = (n : ℝ) * P.k := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, mul_one]
  rw [hconst1, hconst2] at hsumc
  -- arithmetic
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((P.k / n : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hK] at hright
  have hnK : (n : ℝ) * K ≤ P.k := by
    rw [hK]; exact_mod_cast Nat.mul_div_le P.k n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < P.k := by exact_mod_cast hk0
  have hK0 : 0 ≤ K := by rw [hK]; exact Nat.cast_nonneg _
  have h2K : 2 * K ≤ P.k := by nlinarith
  rw [hUtot]
  by_contra hcon
  push_neg at hcon
  have hA6 : 3 / 5 < Ai := by linarith
  have hmain : (P.k : ℝ) * Ui + (n : ℝ) * P.k * (2 * Ai) ≤ (n : ℝ) * P.k + K := by linarith
  -- k*(Ui + 2Ai) > 8/5 k
  have h1 : (P.k : ℝ) * (8 / 5) < (P.k : ℝ) * (Ui + 2 * Ai) := mul_lt_mul_of_pos_left hcon hkpos
  have h3 : ((n : ℝ) - 1) * P.k * (3 / 5) ≤ ((n : ℝ) - 1) * P.k * Ai := by
    apply mul_le_mul_of_nonneg_left hA6.le
    apply mul_nonneg <;> linarith
  have hnk : 2 * (P.k : ℝ) ≤ n * P.k := by nlinarith
  linarith
end Aux_CM

namespace Aux_CM

theorem alpha_le {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q)
    (hR : P.IsRescaled x α q) (hn : 2 ≤ n) (i : P.Agent) (hi : ¬ P.IsDummy i) :
    α i ≤ 5 * (n : ℝ) ^ 2 := by
  obtain ⟨hadm, hx, hEF, _, hα, hW, hD, hp, hq⟩ := hC
  obtain ⟨hfeas, hopt⟩ := hD
  have hU := fun a ha => util_le P x hadm hx hEF hn a ha
  have hnd := fun a ha => nd_facts P hadm a ha
  obtain ⟨_, hu, hk0, hdvd, _, _, _, _⟩ := hadm
  have hb : ∀ a, α a * ∑ j, P.util a j * x a j - q a = ∑ j, p j * x a j :=
    fun a => budget_eq α P.util p q x hx hfeas hopt hW a
  have htight : ∀ a j, 0 < x a j → α a * P.util a j = q a + p j :=
    fun a j hj => tight_of_pos α P.util p q x hx hfeas hopt hW a j hj
  have hkn : 0 < P.k / n := Nat.div_pos (Nat.le_of_dvd hk0 hdvd) (by omega)
  -- (a) dummies hold no awesome good
  have hdum : ∀ (dm : Fin (P.k / n - P.interp.length)) (g : Fin (P.k / n)),
      x (Sum.inr (Sum.inr dm)) (Sum.inr g) = 0 := by
    intro dm g
    by_contra hne
    have hpos : 0 < x (Sum.inr (Sum.inr dm)) (Sum.inr g) :=
      lt_of_le_of_ne (hx.2.2 _ _) (Ne.symm hne)
    have hmin : ∀ j, p (Sum.inr g) ≤ p j := by
      intro j
      have h1 := htight (Sum.inr (Sum.inr dm)) (Sum.inr g) hpos
      have h2 := hfeas (Sum.inr (Sum.inr dm)) j
      have e1 : P.util (Sum.inr (Sum.inr dm)) (Sum.inr g) = P.d := rfl
      have e2 : P.util (Sum.inr (Sum.inr dm)) j = P.d := rfl
      rw [e1] at h1
      rw [e2] at h2
      linarith
    let c0 : Fin n × Fin P.k := (⟨0, by omega⟩, ⟨0, hk0⟩)
    have hN : ¬ P.IsDummy (Sum.inl c0) := fun h => h
    obtain ⟨r, hr⟩ : ∃ r, 0 < x (Sum.inl c0) (Sum.inl r) := by
      by_contra hcon
      push_neg at hcon
      have hR0 : ∑ r, x (Sum.inl c0) (Sum.inl r) = 0 :=
        Finset.sum_eq_zero (fun r _ => le_antisymm (hcon r) (hx.2.2 _ _))
      have hrow := (Fintype.sum_sum_type (x (Sum.inl c0))).symm.trans (hx.1 (Sum.inl c0))
      have hUN := hU (Sum.inl c0) hN
      rw [Fintype.sum_sum_type] at hUN
      have h1 : ∑ r, P.util (Sum.inl c0) (Sum.inl r) * x (Sum.inl c0) (Sum.inl r) = 0 :=
        Finset.sum_eq_zero (fun r _ => by rw [le_antisymm (hcon r) (hx.2.2 _ _), mul_zero])
      have h2 : ∑ g, P.util (Sum.inl c0) (Sum.inr g) * x (Sum.inl c0) (Sum.inr g) =
          2 * ∑ g, x (Sum.inl c0) (Sum.inr g) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun g _ => by rw [(hnd _ hN).2])
      linarith
    have h1 := htight (Sum.inl c0) (Sum.inl r) hr
    have h2 := hfeas (Sum.inl c0) (Sum.inr g)
    rw [(hnd _ hN).2] at h2
    have h3 := ((hnd _ hN).1 r).2.1
    have h4 := hmin (Sum.inl r)
    have h5 := hα (Sum.inl c0)
    nlinarith
  -- (b) cheapest awesome good has price ≤ n^2 + 1
  obtain ⟨gs, _, hgs⟩ := Finset.exists_min_image Finset.univ
    (fun g : Fin (P.k / n) => p (Sum.inr g)) ⟨⟨0, hkn⟩, Finset.mem_univ _⟩
  have hS : ∑ g : Fin (P.k / n), p (Sum.inr g) =
      ∑ a, ∑ g : Fin (P.k / n), p (Sum.inr g) * x a (Sum.inr g) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun g _ => by rw [← Finset.mul_sum, hx.2.1 (Sum.inr g), mul_one])
  have hper : ∀ a, ∑ g : Fin (P.k / n), p (Sum.inr g) * x a (Sum.inr g) ≤ 1 := by
    have hnd_case : ∀ a, ¬ P.IsDummy a →
        ∑ g : Fin (P.k / n), p (Sum.inr g) * x a (Sum.inr g) ≤ 1 := by
      intro a ha
      have h1 : ∑ g : Fin (P.k / n), p (Sum.inr g) * x a (Sum.inr g) ≤ ∑ j, p j * x a j := by
        rw [Fintype.sum_sum_type]
        have : 0 ≤ ∑ r : Fin n × Fin P.k, p (Sum.inl r) * x a (Sum.inl r) :=
          Finset.sum_nonneg (fun r _ => mul_nonneg (hp _) (hx.2.2 _ _))
        linarith
      have h2 := hR.1 a ha
      have e : P.budget x α q a = ∑ j, p j * x a j := hb a
      linarith
    intro a
    rcases a with c | (m | dm)
    · exact hnd_case _ (fun h => h)
    · exact hnd_case _ (fun h => h)
    · rw [Finset.sum_eq_zero (fun g _ => by rw [hdum dm g, mul_zero])]
      norm_num
  have hcardA : Fintype.card P.Agent = n * P.k + P.k / n := by
    rw [card_eq x hx]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have htot : ∑ g : Fin (P.k / n), p (Sum.inr g) ≤ (n : ℝ) * P.k + ((P.k / n : ℕ) : ℝ) := by
    rw [hS]
    have := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset P.Agent)) => hper a)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcardA, Nat.cast_add,
      Nat.cast_mul] at this
    exact this
  have hlow : ((P.k / n : ℕ) : ℝ) * p (Sum.inr gs) ≤ ∑ g : Fin (P.k / n), p (Sum.inr g) := by
    have := Finset.sum_le_sum (fun g (hg : g ∈ (Finset.univ : Finset (Fin (P.k / n)))) => hgs g hg)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((P.k / n : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hK] at htot hlow
  have hkK : (P.k : ℝ) = K * n := by
    rw [hK]; exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast hkn
  have hps : p (Sum.inr gs) ≤ (n : ℝ) ^ 2 + 1 := by
    have h1 : K * p (Sum.inr gs) ≤ K * ((n : ℝ) ^ 2 + 1) := by
      rw [hkK] at htot
      nlinarith
    exact le_of_mul_le_mul_left h1 hKpos
  -- (c) α bound
  have h1 := hfeas i (Sum.inr gs)
  rw [(hnd i hi).2] at h1
  have h2 := hb i
  have h3 : 0 ≤ ∑ j, p j * x i j := Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (hx.2.2 i j))
  have h4 := hU i hi
  have h5 : α i * ∑ j, P.util i j * x i j ≤ α i * (8 / 5) :=
    mul_le_mul_of_nonneg_left h4 (hα i).le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  linarith

end Aux_CM

namespace Aux_CM

theorem same_type_budget {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (i i' : P.Agent)
    (h : P.SameAgentType i i') : P.budget x α q i = P.budget x α q i' := by
  obtain ⟨_, hx, hEF, _, _, hW, hD, _, _⟩ := hC
  obtain ⟨hfeas, hopt⟩ := hD
  have hu : P.util i = P.util i' := funext h
  have e1 := hEF i i'
  have e2 := hEF i' i
  rw [← hu] at e2
  have hU : ∑ j, P.util i j * x i j = ∑ j, P.util i j * x i' j := le_antisymm e2 e1
  have r1 := row_bound α P.util p q hfeas i (x i') (hx.1 i') (fun j => hx.2.2 i' j)
  have r2 := row_bound α P.util p q hfeas i' (x i) (hx.1 i) (fun j => hx.2.2 i j)
  have c1 := budget_eq α P.util p q x hx hfeas hopt hW i
  have c2 := budget_eq α P.util p q x hx hfeas hopt hW i'
  rw [← hu] at r2 c2
  rw [hU] at c1 r2
  show α i * ∑ j, P.util i j * x i j - q i = α i' * ∑ j, P.util i' j * x i' j - q i'
  rw [← hu, hU]
  linarith

theorem same_type_n1 {n : ℕ} (P : ModParams n) (hadm : P.Admissible) (hn : n < 2)
    (i i' : P.Agent) (hi : ¬ P.IsDummy i) (hi' : ¬ P.IsDummy i') : P.SameAgentType i i' := by
  have hsub : ∀ a b : Fin n, a = b := fun a b => Fin.ext (by
    have := a.isLt
    have := b.isLt
    omega)
  have key : ∀ a : P.Agent, ¬ P.IsDummy a → ∀ (r : Fin n × Fin P.k) (ρ : Fin n),
      P.util a (Sum.inl r) = P.u ρ r.1 := by
    intro a ha r ρ
    obtain ⟨_, _, _, _, hε, _, _, _⟩ := hadm
    rcases a with c | (m | dm)
    · show P.u c.1 r.1 = P.u ρ r.1
      rw [hsub c.1 ρ]
    · show P.interp.get m r.1 = P.u ρ r.1
      obtain ⟨j, j', h1, h2⟩ := interp_bounds P.u P.ε hε P.ord P.rev (P.interp.get m)
        (List.get_mem P.interp m) r.1
      rw [hsub j ρ, hsub j' ρ, min_self] at h1
      rw [hsub j ρ, hsub j' ρ, max_self] at h2
      linarith
    · exact absurd trivial ha
  intro g
  rcases g with r | g
  · rw [key i hi r r.1, key i' hi' r r.1]
  · rw [(nd_facts P hadm i hi).2, (nd_facts P hadm i' hi').2]

theorem half19 {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q)
    (hR : P.IsRescaled x α q) (i i' : P.Agent) (hi : ¬ P.IsDummy i)
    (g₀ : P.Good) (hsame : ∀ g, ¬ P.SameGoodType g g₀ → P.util i g = P.util i' g)
    (hclose : ∀ g, P.SameGoodType g g₀ → |P.util i g - P.util i' g| ≤ P.ε) (hn : 2 ≤ n) :
    P.budget x α q i - P.budget x α q i' ≤ 5 * (n : ℝ) ^ 2 * P.ε := by
  have hα18 := alpha_le P x α p q hC hR hn i hi
  obtain ⟨hadm, hx, hEF, _, hα, hW, hD, hp, hq⟩ := hC
  obtain ⟨hfeas, hopt⟩ := hD
  have hεpos : 0 < P.ε := hadm.2.2.2.2.1
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = P.util i g₀ - P.util i' g₀ := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : P.Good → ℝ, w = fun g => if P.SameGoodType g g₀ then 1 else 0 :=
    ⟨_, rfl⟩
  have hdiff : ∀ g, P.util i g = P.util i' g + δ * w g := by
    intro g
    by_cases hg : P.SameGoodType g g₀
    · rw [hwdef]
      simp only [if_pos hg, mul_one]
      rw [hδ, hg i, hg i']
      ring
    · rw [hwdef]
      simp only [if_neg hg, mul_zero, add_zero]
      exact hsame g hg
  have hδε : |δ| ≤ P.ε := by
    have := hclose g₀ (by intro a; rfl)
    rw [hδ]
    exact this
  have hdot : ∀ z : P.Good → ℝ,
      ∑ j, P.util i j * z j = ∑ j, P.util i' j * z j + δ * ∑ j, w j * z j := by
    intro z
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [hdiff j]; ring)
  have hw : ∀ j, 0 ≤ w j ∧ w j ≤ 1 := by
    intro j
    rw [hwdef]
    dsimp only
    split_ifs <;> norm_num
  have hm : ∀ a, 0 ≤ ∑ j, w j * x a j ∧ ∑ j, w j * x a j ≤ 1 := by
    intro a
    constructor
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j).1 (hx.2.2 a j))
    · calc ∑ j, w j * x a j ≤ ∑ j, x a j :=
            Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (hx.2.2 a j) (hw j).2)
        _ = 1 := hx.1 a
  have e1 := hEF i' i
  have hd1 := hdot (x i)
  have hd2 := hdot (x i')
  have hgap : ∑ j, P.util i j * x i j - ∑ j, P.util i j * x i' j ≤ P.ε := by
    have hmi := hm i
    have hmi' := hm i'
    have hthis : δ * (∑ j, w j * x i j - ∑ j, w j * x i' j) ≤ P.ε := by
      have h1 : δ * (∑ j, w j * x i j - ∑ j, w j * x i' j) ≤
          |δ| * |∑ j, w j * x i j - ∑ j, w j * x i' j| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |∑ j, w j * x i j - ∑ j, w j * x i' j| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have h3 : |δ| * |∑ j, w j * x i j - ∑ j, w j * x i' j| ≤ P.ε * 1 :=
        mul_le_mul hδε h2 (abs_nonneg _) hεpos.le
      linarith
    linarith
  have hr := row_bound α P.util p q hfeas i (x i') (hx.1 i') (fun j => hx.2.2 i' j)
  have hb1 := budget_eq α P.util p q x hx hfeas hopt hW i
  have hb2 := budget_eq α P.util p q x hx hfeas hopt hW i'
  have e : P.budget x α q i - P.budget x α q i' =
      (α i * ∑ j, P.util i j * x i j - q i) - (α i' * ∑ j, P.util i' j * x i' j - q i') := rfl
  rw [e, hb1, hb2]
  have hmul : α i * (∑ j, P.util i j * x i j - ∑ j, P.util i j * x i' j) ≤ α i * P.ε :=
    mul_le_mul_of_nonneg_left hgap (hα i).le
  have hαε : α i * P.ε ≤ 5 * (n : ℝ) ^ 2 * P.ε := mul_le_mul_of_nonneg_right hα18 hεpos.le
  linarith

end Aux_CM


end CardinalMatching

open CardinalMatching in
theorem solution {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q)
    (hR : P.IsRescaled x α q) (i i' : P.Agent) (hi : ¬ P.IsDummy i) (hi' : ¬ P.IsDummy i')
    (g₀ : P.Good) (hsame : ∀ g, ¬ P.SameGoodType g g₀ → P.util i g = P.util i' g)
    (hclose : ∀ g, P.SameGoodType g g₀ → |P.util i g - P.util i' g| ≤ P.ε) :
    |P.budget x α q i - P.budget x α q i'| ≤ 5 * (n : ℝ) ^ 2 * P.ε := by
  have hεpos : 0 < P.ε := hC.1.2.2.2.2.1
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have heq := Aux_CM.same_type_budget P x α p q hC i i'
      (Aux_CM.same_type_n1 P hC.1 hn i i' hi hi')
    rw [heq, sub_self, abs_zero]
    exact mul_nonneg (by positivity) hεpos.le
  · rw [abs_sub_le_iff]
    refine ⟨Aux_CM.half19 P x α p q hC hR i i' hi g₀ hsame hclose hn,
      Aux_CM.half19 P x α p q hC hR i' i hi' g₀ (fun g hg => (hsame g hg).symm)
        (fun g hg => by rw [abs_sub_comm]; exact hclose g hg) hn⟩
