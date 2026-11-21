-- Prove2me | solution 1 for CardinalMatching.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:04:46.569181+00:00
-- url     : https://prove2.me/submissions/8fe12563-cbd3-478e-9586-1c65cd1da5a7

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

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


end CardinalMatching

open CardinalMatching in
theorem solution {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (hn : 2 ≤ n)
    (i : P.Agent) (hi : ¬ P.IsDummy i) :
    ∑ j, P.util i j * x i j ≤ 8 / 5 ∧ ∃ j, ∑ j', P.util i j' * x i j' < P.util i j := by
  obtain ⟨hadm, hx, hEF, _⟩ := hC
  have h := Aux_CM.util_le P x hadm hx hEF hn i hi
  have hnd := (Aux_CM.nd_facts P hadm i hi).2
  refine ⟨h, ?_⟩
  obtain ⟨_, _, hk0, hdvd, _⟩ := hadm
  have hkn : 0 < P.k / n := Nat.div_pos (Nat.le_of_dvd hk0 hdvd) (by omega)
  refine ⟨Sum.inr ⟨0, hkn⟩, ?_⟩
  rw [hnd]
  linarith
