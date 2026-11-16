-- Prove2me | solution 1 for DirKECC1549.Main.lemma_5_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-15T16:27:22.663358+00:00
-- url     : https://prove2.me/submissions/84b6fa6b-1384-4d89-9ea5-7261d2e79df1

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3Cost
import Theorems.Thm_DirKECC1549_Main_sec2_maxflow_mincut
import Theorems.Thm_DirKECC1549_Main_walks_in_scc
import Theorems.Thm_DirKECC1549_Main_induced_walk_lift

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Main.CostAux

open DirKECC1549.Main

/-! ## Exponents -/

theorem eps_pos (k : ℕ) : 0 < eps k := by unfold eps; positivity

theorem eps_le_one (k : ℕ) : eps k ≤ 1 := by
  unfold eps; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)

theorem eps_le_half (k : ℕ) (hk : 2 ≤ k) : eps k ≤ 1 / 2 := by
  unfold eps
  apply one_div_le_one_div_of_le (by norm_num)
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)

theorem eps_pred (k : ℕ) (hk : 2 ≤ k) : eps (k - 1) = 2 * eps k := by
  unfold eps
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 by omega, show j + 1 - 1 = j by omega, pow_succ]
  field_simp

theorem eps_anti (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) : eps k ≤ eps j := by
  unfold eps
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-! ## Powers of `n` -/

theorem one_le_rpow' (x e : ℝ) (hx : 1 ≤ x) (he : 0 ≤ e) : 1 ≤ x ^ e := Real.one_le_rpow hx he

theorem rpow_le_self (x e : ℝ) (hx : 1 ≤ x) (he : e ≤ 1) : x ^ e ≤ x := by
  calc x ^ e ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx he
    _ = x := Real.rpow_one x

theorem rpow_mono_exp (x a b : ℝ) (hx : 1 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

/-! ## Combinatorial constants -/

theorem fact_bound (k : ℕ) (hk : 2 ≤ k) : 2 ^ k * (k + 1).factorial * (k + 1) ≤ 4 * k ^ (3 * k) := by
  have h1 : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  have h2 : 2 ^ k ≤ k ^ k := Nat.pow_le_pow_left hk k
  have h3 : k + 1 ≤ 2 * k := by omega
  have h4 : k ^ (2 * k + 2) ≤ k ^ (3 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  calc 2 ^ k * (k + 1).factorial * (k + 1) = 2 ^ k * k.factorial * ((k + 1) * (k + 1)) := by
        rw [Nat.factorial_succ]; ring
    _ ≤ k ^ k * k ^ k * ((2 * k) * (2 * k)) := by
        gcongr
    _ = 4 * k ^ (2 * k + 2) := by ring
    _ ≤ 4 * k ^ (3 * k) := by gcongr

theorem rec_bound (k : ℕ) (hk : 2 ≤ k) : 2 * ((2 * k - 1) * (k - 1) ^ (3 * (k - 1))) ≤ k ^ (3 * k) := by
  have h1 : (k - 1) ^ (3 * (k - 1)) ≤ k ^ (3 * (k - 1)) := Nat.pow_le_pow_left (by omega) _
  have h2 : 4 ≤ k * k := by nlinarith
  have h3 : k ^ (3 * k) = k ^ (3 * (k - 1)) * (k * k * k) := by
    rw [show 3 * k = 3 * (k - 1) + 3 by omega, pow_add]; ring
  rw [h3]
  calc 2 * ((2 * k - 1) * (k - 1) ^ (3 * (k - 1))) ≤ 2 * ((2 * k) * k ^ (3 * (k - 1))) := by
        gcongr; omega
    _ = k ^ (3 * (k - 1)) * (4 * k) := by ring
    _ ≤ k ^ (3 * (k - 1)) * (k * k * k) := by gcongr

theorem pow_self_mono (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) : j ^ (3 * j) ≤ k ^ (3 * k) :=
  le_trans (Nat.pow_le_pow_left hjk _) (Nat.pow_le_pow_right (by omega) (by omega))

/-! ## Walks and cuts -/

variable {n m : ℕ}

theorem walk_append (D : Fin m → Fin n × Fin n) {a b c : Fin n} {p q : List (Fin m)}
    (hp : IsWalk D a p b) (hq : IsWalk D b q c) : IsWalk D a (p ++ q) c := by
  induction hp with
  | nil => simpa using hq
  | cons e p he _ ih => exact IsWalk.cons e (p ++ q) he (ih hq)

theorem reach_trans (D : Fin m → Fin n × Fin n) {a b c : Fin n} (h1 : Reach D a b)
    (h2 : Reach D b c) : Reach D a c := by
  obtain ⟨p, hp⟩ := h1; obtain ⟨q, hq⟩ := h2; exact ⟨p ++ q, walk_append D hp hq⟩

theorem sc_refl (D : Fin m → Fin n × Fin n) (a : Fin n) : StronglyConn D a a :=
  ⟨⟨[], IsWalk.nil a⟩, ⟨[], IsWalk.nil a⟩⟩

theorem sc_symm (D : Fin m → Fin n × Fin n) {a b : Fin n} (h : StronglyConn D a b) :
    StronglyConn D b a := ⟨h.2, h.1⟩

theorem sc_trans (D : Fin m → Fin n × Fin n) {a b c : Fin n} (h1 : StronglyConn D a b)
    (h2 : StronglyConn D b c) : StronglyConn D a c :=
  ⟨reach_trans D h1.1 h2.1, reach_trans D h2.2 h1.2⟩

/-- A walk from inside `S` to outside `S` uses an edge leaving `S`. -/
theorem walk_exits (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) {a b : Fin n}
    {p : List (Fin m)} (hp : IsWalk D a p b) (ha : a ∈ S) (hb : b ∉ S) :
    (outEdges D S).Nonempty := by
  induction hp with
  | nil => exact absurd ha hb
  | cons e p he _ ih =>
    by_cases h2 : (D e).2 ∈ S
    · exact ih h2 hb
    · exact ⟨e, by simp [outEdges, he ▸ ha, h2]⟩

theorem outCount_rev (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) :
    outCount (Rev D) S = outCount D Sᶜ := by
  unfold outCount outEdges Rev
  congr 1; ext e; simp [and_comm]

/-- In a strongly connected graph, `λ(z, r) ≥ 1` for `z ≠ r`, in `D` and in `Dᴿ`. -/
theorem lam_pos (D : Fin m → Fin n × Fin n) (hsc : IsStronglyConnected D) (z r : Fin n)
    (hzr : z ≠ r) : 1 ≤ lam D z r ∧ 1 ≤ lam (Rev D) z r := by
  constructor
  · obtain ⟨-, ⟨S, ⟨hz, hr⟩, hS⟩, -⟩ := sec2_maxflow_mincut D z r hzr
    rw [← hS]
    obtain ⟨p, hp⟩ := (hsc z r).1
    exact Finset.card_pos.2 (walk_exits D S hp hz hr)
  · obtain ⟨-, ⟨S, ⟨hz, hr⟩, hS⟩, -⟩ := sec2_maxflow_mincut (Rev D) z r hzr
    rw [← hS]; show 1 ≤ outCount (Rev D) S; rw [outCount_rev]
    obtain ⟨p, hp⟩ := (hsc r z).1
    exact Finset.card_pos.2 (walk_exits D Sᶜ hp (by simpa using hr) (by simpa using hz))

/-! ## Strongly connected components -/

theorem mem_scc {D : Fin m → Fin n × Fin n} {u v : Fin n} : v ∈ sccOf D u ↔ StronglyConn D u v := by
  simp [sccOf]

theorem scc_eq (D : Fin m → Fin n × Fin n) {u v : Fin n} (h : StronglyConn D u v) :
    sccOf D u = sccOf D v := by
  ext x; simp only [mem_scc]
  exact ⟨fun hx => sc_trans D (sc_symm D h) hx, fun hx => sc_trans D h hx⟩

theorem scc_disj (D : Fin m → Fin n × Fin n) (u v : Fin n) (h : sccOf D u ≠ sccOf D v) :
    Disjoint (sccOf D u) (sccOf D v) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  apply h
  rw [scc_eq D (mem_scc.1 hxu), scc_eq D (mem_scc.1 hxv)]

theorem posIn_vertexOf (S : Finset (Fin n)) (i : Fin S.card) (h : vertexOf S i ∈ S) :
    posIn S (vertexOf S i) h = i := by
  have e : (⟨vertexOf S i, h⟩ : S) = S.orderIsoOfFin rfl i := Subtype.ext rfl
  unfold posIn; rw [e]; exact OrderIso.symm_apply_apply _ _

theorem vertexOf_mem (S : Finset (Fin n)) (i : Fin S.card) : vertexOf S i ∈ S :=
  (S.orderIsoOfFin rfl i).2

/-- The subgraph induced by a strongly connected component is strongly connected. -/
theorem induced_scc_sc (D : Fin m → Fin n × Fin n) (u : Fin n) :
    IsStronglyConnected (induced D (sccOf D u)) := by
  set S := sccOf D u
  have key : ∀ i j : Fin S.card, Reach (induced D S) i j := by
    intro i j
    have hx := vertexOf_mem S i
    have hy := vertexOf_mem S j
    have sx : StronglyConn D u (vertexOf S i) := mem_scc.1 hx
    have sy : StronglyConn D u (vertexOf S j) := mem_scc.1 hy
    obtain ⟨p, hp⟩ := reach_trans D sx.2 sy.1
    obtain ⟨q, -, hq⟩ := induced_walk_lift D S _ _ hx hy p hp (walks_in_scc D u _ _ sx sy p hp)
    rw [posIn_vertexOf, posIn_vertexOf] at hq
    exact ⟨q, hq⟩
  exact fun i j => ⟨key i j, key j i⟩

/-- The components partition the vertices, and their induced edge sets are disjoint. -/
theorem scc_sums (D : Fin m → Fin n × Fin n) :
    ∑ S ∈ univ.image (sccOf D), (S.card + (inducedEdges D S).card) ≤ n + m := by
  set 𝒮 := univ.image (sccOf D)
  have hdisj : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint S S' := by
    intro S hS S' hS' hne
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hS
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hS'
    exact scc_disj D u v hne
  have h1 : ∑ S ∈ 𝒮, S.card ≤ n := by
    rw [← Finset.card_biUnion hdisj]
    exact le_trans (Finset.card_le_univ _) (by simp)
  have h2 : ∑ S ∈ 𝒮, (inducedEdges D S).card ≤ m := by
    rw [← Finset.card_biUnion]
    · exact le_trans (Finset.card_le_univ _) (by simp)
    · intro S hS S' hS' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he he'
      simp only [inducedEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
      exact Finset.disjoint_left.1 (hdisj S hS S' hS' hne) he.1 he'.1
  rw [Finset.sum_add_distrib]; omega

/-! ## `Δ` -/

theorem delta_facts (n m k : ℕ) (hk : 2 ≤ k) (p : ℝ) (hp : p = (n : ℝ) ^ eps k) (hp1 : 1 ≤ p) :
    (m : ℝ) / p ≤ alg3Delta n m k ∧ (alg3Delta n m k : ℝ) ≤ k + m / p ∧
      (1 : ℝ) ≤ alg3Delta n m k := by
  have h0 : 0 ≤ (m : ℝ) / p := by positivity
  unfold alg3Delta
  rw [← hp]
  rw [Nat.cast_max]
  refine ⟨le_trans (Nat.le_ceil _) (le_max_right _ _), ?_, ?_⟩
  · apply max_le
    · have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      linarith
    · have := Nat.ceil_lt_add_one h0
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      linarith
  · exact le_trans (by exact_mod_cast (by omega : 1 ≤ k - 1)) (le_max_left _ _)

/-! ## The main-case inequality -/

theorem main_alg (K K1 X p Q Q1 F nR mR Δ zG zR T0 SG SR kR : ℝ) (hk : 2 ≤ kR)
    (hX1 : 1 ≤ X) (hp1 : 1 ≤ p) (hQ : p * Q = nR) (hQ1 : Q1 * p = Q) (hpQ : p ≤ Q)
    (hpX : p ≤ X) (hm0 : 0 ≤ mR) (hmX : mR + nR + 1 ≤ 2 * X) (hmX' : mR ≤ X)
    (hΔ : Δ ≤ kR + mR / p) (hΔ0 : 0 ≤ Δ)
    (hzG0 : 0 ≤ zG) (hzR0 : 0 ≤ zR) (hzG : zG ≤ (kR - 1) * p) (hzR : zR ≤ (kR - 1) * p)
    (hF0 : 0 ≤ F) (hF : F * (kR + 1) ≤ 4 * K) (hk2 : kR ^ 2 ≤ K)
    (hK1 : 2 * (2 * kR - 1) * K1 ≤ K) (hK10 : 0 ≤ K1) (hQ10 : 0 ≤ Q1) (hn0 : 0 ≤ nR)
    (hT0 : T0 ≤ 64 * K1 * X * Q1) (hSG : SG ≤ zG * (64 * K1 * X * Q1))
    (hSR : SR ≤ zR * (64 * K1 * X * Q1)) :
    K * (mR + nR + 1) + F * nR * Δ + (zG + zR) * (kR + 1) * (mR + nR + 1) + T0 + SG + SR ≤
      48 * (K * X * Q) := by
  have hQ1' : 1 ≤ Q := le_trans hp1 hpQ
  have hQ0 : 0 ≤ Q := by linarith
  have hK0 : 0 ≤ K := le_trans (by positivity) hk2
  have hX0 : 0 ≤ X := by linarith
  have hKX : K * X ≤ K * X * Q := le_mul_of_one_le_right (by positivity) hQ1'
  -- local work
  have a1 : K * (mR + nR + 1) ≤ 2 * (K * X * Q) := by
    have := mul_le_mul_of_nonneg_left hmX hK0
    linarith
  -- Lemma 1
  have hnmp : nR * (mR / p) = mR * Q := by
    rw [← hQ]; field_simp
  have hnXQ : nR ≤ X * Q := by rw [← hQ]; exact mul_le_mul_of_nonneg_right hpX hQ0
  have a2 : F * nR * Δ ≤ 4 * (K * X * Q) := by
    have e1 : F * nR * Δ ≤ F * nR * (kR + mR / p) := by
      apply mul_le_mul_of_nonneg_left hΔ; positivity
    have e2 : kR * nR ≤ kR * (X * Q) := mul_le_mul_of_nonneg_left hnXQ (by linarith)
    have e2' : mR * Q ≤ X * Q := mul_le_mul_of_nonneg_right hmX' hQ0
    have e3 : F * nR * (kR + mR / p) = F * (kR * nR + mR * Q) := by rw [← hnmp]; ring
    have e4 : F * (kR * nR + mR * Q) ≤ F * ((kR + 1) * (X * Q)) := by
      apply mul_le_mul_of_nonneg_left _ hF0; linarith
    have e5 : F * ((kR + 1) * (X * Q)) = (F * (kR + 1)) * (X * Q) := by ring
    have e6 : (F * (kR + 1)) * (X * Q) ≤ (4 * K) * (X * Q) :=
      mul_le_mul_of_nonneg_right hF (by positivity)
    have e7 : (4 * K) * (X * Q) = 4 * (K * X * Q) := by ring
    linarith
  -- Lemma 3 and refinements
  have a3 : (zG + zR) * (kR + 1) * (mR + nR + 1) ≤ 4 * (K * X * Q) := by
    have h1 : (zG + zR) * (kR + 1) ≤ (2 * (kR - 1) * p) * (kR + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have e1 : (zG + zR) * (kR + 1) * (mR + nR + 1) ≤ (2 * (kR - 1) * p) * (kR + 1) * (2 * X) :=
      mul_le_mul h1 hmX (by linarith) (by
        have : 0 ≤ kR - 1 := by linarith
        positivity)
    have e2 : (2 * (kR - 1) * p) * (kR + 1) * (2 * X) = 4 * (kR ^ 2 - 1) * (p * X) := by ring
    have hpXQ : p * X ≤ Q * X := mul_le_mul_of_nonneg_right hpQ hX0
    have e3 : 4 * (kR ^ 2 - 1) * (p * X) ≤ 4 * K * (Q * X) :=
      mul_le_mul (by linarith) hpXQ (by positivity) (by positivity)
    have e4 : 4 * K * (Q * X) = 4 * (K * X * Q) := by ring
    linarith
  -- recursion
  have a4 : T0 + SG + SR ≤ 32 * (K * X * Q) := by
    set R := 64 * K1 * X * Q1 with hR
    have hR0 : 0 ≤ R := by positivity
    have e0 : (1 + zG + zR) * R = R + zG * R + zR * R := by ring
    have e1 : T0 + SG + SR ≤ (1 + zG + zR) * R := by rw [e0]; linarith
    have e2 : (1 + zG + zR) ≤ (2 * kR - 1) * p := by nlinarith
    have e3 : (1 + zG + zR) * R ≤ ((2 * kR - 1) * p) * R := mul_le_mul_of_nonneg_right e2 hR0
    have e4 : ((2 * kR - 1) * p) * R = 32 * (2 * (2 * kR - 1) * K1) * (X * Q) := by
      rw [hR, ← hQ1]; ring
    have e5 : 32 * (2 * (2 * kR - 1) * K1) * (X * Q) ≤ 32 * K * (X * Q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    have e6 : 32 * K * (X * Q) = 32 * (K * X * Q) := by ring
    linarith
  have hKXQ : 0 ≤ K * X * Q := by positivity
  linarith

/-! ## The bound function -/

noncomputable def Bd (k m n : ℕ) : ℝ := (k : ℝ) ^ (3 * k) * ((m + n : ℕ) : ℝ) * (n : ℝ) ^ (1 - eps k)

theorem Bd_nonneg (k m n : ℕ) : 0 ≤ Bd k m n := by
  unfold Bd; have : 0 ≤ (n : ℝ) ^ (1 - eps k) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

theorem Bd_mono (j k m n : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (hn : 1 ≤ n) : Bd j m n ≤ Bd k m n := by
  unfold Bd
  have h1 : ((j : ℝ) ^ (3 * j)) ≤ (k : ℝ) ^ (3 * k) := by exact_mod_cast pow_self_mono j k hj hjk
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ^ (1 - eps j) ≤ (n : ℝ) ^ (1 - eps k) :=
    rpow_mono_exp _ _ _ hn1 (by linarith [eps_anti j k hj hjk])
  have h3 : 0 ≤ (n : ℝ) ^ (1 - eps j) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ ((m + n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc (j : ℝ) ^ (3 * j) * ((m + n : ℕ) : ℝ) * (n : ℝ) ^ (1 - eps j)
      ≤ (k : ℝ) ^ (3 * k) * ((m + n : ℕ) : ℝ) * (n : ℝ) ^ (1 - eps k) := by gcongr

theorem base_le (k m n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k ^ (3 * k) * (m + n + 1) : ℕ) : ℝ) ≤ 2 * Bd k m n := by
  unfold Bd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ : 1 ≤ (n : ℝ) ^ (1 - eps k) := Real.one_le_rpow hn1 (by linarith [eps_le_one k])
  have hX : ((m + n + 1 : ℕ) : ℝ) ≤ 2 * ((m + n : ℕ) : ℝ) := by
    push_cast; have : (1 : ℝ) ≤ n := hn1; linarith
  have hK : 0 ≤ (k : ℝ) ^ (3 * k) := by positivity
  have hX0 : 0 ≤ ((m + n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((k ^ (3 * k) * (m + n + 1) : ℕ) : ℝ) = (k : ℝ) ^ (3 * k) * ((m + n + 1 : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (k : ℝ) ^ (3 * k) * (2 * ((m + n : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hX hK
    _ = 2 * ((k : ℝ) ^ (3 * k) * ((m + n : ℕ) : ℝ) * 1) := by ring
    _ ≤ 2 * ((k : ℝ) ^ (3 * k) * ((m + n : ℕ) : ℝ) * (n : ℝ) ^ (1 - eps k)) := by gcongr

/-! ## The induction -/

set_option maxHeartbeats 2000000 in
theorem cost_aux {n₀ m₀ : ℕ} (G₀ : Fin m₀ → Fin n₀ × Fin n₀) (k₀ : ℕ) (P₀ : Fin n₀ → Fin n₀ → Prop)
    (T₀' : ℕ) (h : Alg3CostRun n₀ m₀ G₀ k₀ P₀ T₀') :
    1 ≤ k₀ → 1 ≤ n₀ → (T₀' : ℝ) ≤ 64 * Bd k₀ m₀ n₀ ∧
      (IsStronglyConnected G₀ → (T₀' : ℝ) ≤ 48 * Bd k₀ m₀ n₀) := by
  induction h with
  | @base n m G k hb =>
    intro hk hn
    have := base_le k m n hk hn
    have := Bd_nonneg k m n
    constructor <;> [skip; intro _] <;> linarith
  | @split n m G k runs cost hb hsc _ ih =>
    intro hk hn
    refine ⟨?_, fun h => absurd h hsc⟩
    set 𝒮 := univ.image (sccOf G)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set Q := (n : ℝ) ^ (1 - eps k)
    have hQ0 : 0 ≤ Q := Real.rpow_nonneg (by linarith) _
    have hK0 : 0 ≤ (k : ℝ) ^ (3 * k) := by positivity
    have hS : ∀ S ∈ 𝒮, (cost S : ℝ) ≤
        48 * ((k : ℝ) ^ (3 * k) * Q * ((S.card + (inducedEdges G S).card : ℕ) : ℝ)) := by
      intro S hSm
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hSm
      have hcard : 1 ≤ (sccOf G u).card :=
        Finset.card_pos.2 ⟨u, CostAux.mem_scc.2 (sc_refl G u)⟩
      have := ((ih u hk hcard).2 (induced_scc_sc G u))
      refine le_trans this ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      unfold Bd
      have hle : ((sccOf G u).card : ℝ) ≤ n := by
        exact_mod_cast le_trans (Finset.card_le_univ _) (by simp)
      have h2 : ((sccOf G u).card : ℝ) ^ (1 - eps k) ≤ Q :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith [eps_le_one k])
      have h3 : 0 ≤ (((inducedEdges G (sccOf G u)).card + (sccOf G u).card : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      calc (k : ℝ) ^ (3 * k) * (((inducedEdges G (sccOf G u)).card + (sccOf G u).card : ℕ) : ℝ) *
            ((sccOf G u).card : ℝ) ^ (1 - eps k)
          ≤ (k : ℝ) ^ (3 * k) * (((inducedEdges G (sccOf G u)).card + (sccOf G u).card : ℕ) : ℝ) *
            Q := by gcongr
        _ = (k : ℝ) ^ (3 * k) * Q * (((sccOf G u).card + (inducedEdges G (sccOf G u)).card : ℕ) : ℝ) := by
            push_cast; ring
    have hsum : (∑ S ∈ 𝒮, (cost S : ℝ)) ≤ 48 * ((k : ℝ) ^ (3 * k) * Q * ((n + m : ℕ) : ℝ)) := by
      calc (∑ S ∈ 𝒮, (cost S : ℝ))
          ≤ ∑ S ∈ 𝒮, 48 * ((k : ℝ) ^ (3 * k) * Q * ((S.card + (inducedEdges G S).card : ℕ) : ℝ)) :=
            Finset.sum_le_sum hS
        _ = 48 * ((k : ℝ) ^ (3 * k) * Q *
              ((∑ S ∈ 𝒮, (S.card + (inducedEdges G S).card) : ℕ) : ℝ)) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]; push_cast; ring
        _ ≤ 48 * ((k : ℝ) ^ (3 * k) * Q * ((n + m : ℕ) : ℝ)) := by
            gcongr; exact_mod_cast scc_sums G
    have hb2 := base_le k m n hk hn
    have hB : (k : ℝ) ^ (3 * k) * Q * ((n + m : ℕ) : ℝ) = Bd k m n := by
      unfold Bd; rw [show n + m = m + n by ring]; ring
    rw [hB] at hsum
    have := Bd_nonneg k m n
    push_cast at hb2 ⊢
    have e : ((k ^ (3 * k) * (m + n + 1) : ℕ) : ℝ) = (k : ℝ) ^ (3 * k) * ((m : ℝ) + n + 1) := by
      push_cast; ring
    push_cast at e
    linarith
  | @main n m G k Pk1 P r ZG ZR qG qR FG FR QG QR T₀ TG TR hb hsc _ hL1 hL2G hL2R hqG _ hqR _
      ih0 ihG ihR =>
    intro hk hn
    have hk2 : 2 ≤ k := by omega
    have hn2 : 2 ≤ n := by omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    set p := (n : ℝ) ^ eps k with hpdef
    set Q := (n : ℝ) ^ (1 - eps k) with hQdef
    set Q1 := (n : ℝ) ^ (1 - eps (k - 1)) with hQ1def
    have he1 := eps_le_one k
    have heh := eps_le_half k hk2
    have hep := eps_pos k
    have hp1 : 1 ≤ p := Real.one_le_rpow hn1 hep.le
    have hpQ : p * Q = n := by
      rw [hpdef, hQdef, ← Real.rpow_add hn0]; simp
    have hQ1p : Q1 * p = Q := by
      rw [hQ1def, hpdef, hQdef, ← Real.rpow_add hn0, eps_pred k hk2]; ring_nf
    have hpleQ : p ≤ Q := rpow_mono_exp _ _ _ hn1 (by linarith)
    have hpn : p ≤ n := rpow_le_self _ _ hn1 he1
    set X := ((m + n : ℕ) : ℝ) with hXdef
    have hXn : (n : ℝ) ≤ X := by rw [hXdef]; push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hXm : (m : ℝ) ≤ X := by rw [hXdef]; push_cast; linarith
    obtain ⟨hD1, hD2, hD3⟩ := delta_facts n m k hk2 p rfl hp1
    -- hitting sets are small
    have hz : ∀ Z : Finset (Fin n), ∀ D : Fin m → Fin n × Fin n,
        Lemma2Guarantee D r k (alg3Delta n m k) Z → (Z.card : ℝ) ≤ ((k : ℝ) - 1) * p := by
      intro Z D hZ
      have h1 := hZ.2.1
      have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        linarith
      have h2 : (m : ℝ) / (alg3Delta n m k : ℝ) ≤ p := by
        rw [div_le_iff₀ (by linarith)]
        rw [div_le_iff₀ (by linarith)] at hD1
        linarith
      have h3 : ((k : ℝ) - 1) * m / (alg3Delta n m k : ℝ) ≤ ((k : ℝ) - 1) * p := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 hk1
      linarith
    -- recursive calls
    have hrec : ∀ j, 1 ≤ j → j ≤ k - 1 → Bd j m n ≤ Bd (k - 1) m n :=
      fun j hj hjk => Bd_mono j (k - 1) m n hj hjk hn
    have hBd1 : Bd (k - 1) m n = ((k - 1 : ℕ) : ℝ) ^ (3 * (k - 1)) * X * Q1 := by unfold Bd; rfl
    have hT0 : (T₀ : ℝ) ≤ 64 * (((k - 1 : ℕ) : ℝ) ^ (3 * (k - 1))) * X * Q1 := by
      have := (ih0 (by omega) hn).1; rw [hBd1] at this; linarith
    set M := 64 * (((k - 1 : ℕ) : ℝ) ^ (3 * (k - 1))) * X * Q1 with hM
    have hsumG : ((∑ z ∈ ZG.filter (fun z => qG z < k), TG z : ℕ) : ℝ) ≤ (ZG.card : ℝ) * M := by
      push_cast
      calc (∑ z ∈ ZG.filter (fun z => qG z < k), (TG z : ℝ))
          ≤ ∑ z ∈ ZG.filter (fun z => qG z < k), M := by
            apply Finset.sum_le_sum
            intro z hzf
            obtain ⟨hzZ, hzq⟩ := Finset.mem_filter.1 hzf
            have hzr : z ≠ r := fun h => hL2G.1 (h ▸ hzZ)
            have hq1 : 1 ≤ qG z := by
              rw [(hqG z hzZ).1]; exact le_min (by omega) (lam_pos G hsc z r hzr).1
            have := (ihG z hzZ hzq (by omega) hn).1
            have := hrec (k - qG z) (by omega) (by omega)
            rw [hBd1] at this; rw [hM]; nlinarith
        _ = ((ZG.filter (fun z => qG z < k)).card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (ZG.card : ℝ) * M := by
            apply mul_le_mul_of_nonneg_right _ (by rw [hM]; positivity)
            exact_mod_cast Finset.card_filter_le _ _
    have hsumR : ((∑ z ∈ ZR.filter (fun z => qR z < k), TR z : ℕ) : ℝ) ≤ (ZR.card : ℝ) * M := by
      push_cast
      calc (∑ z ∈ ZR.filter (fun z => qR z < k), (TR z : ℝ))
          ≤ ∑ z ∈ ZR.filter (fun z => qR z < k), M := by
            apply Finset.sum_le_sum
            intro z hzf
            obtain ⟨hzZ, hzq⟩ := Finset.mem_filter.1 hzf
            have hzr : z ≠ r := fun h => hL2R.1 (h ▸ hzZ)
            have hq1 : 1 ≤ qR z := by
              rw [(hqR z hzZ).1]; exact le_min (by omega) (lam_pos G hsc z r hzr).2
            have := (ihR z hzZ hzq (by omega) hn).1
            have := hrec (k - qR z) (by omega) (by omega)
            rw [hBd1] at this; rw [hM]; nlinarith
        _ = ((ZR.filter (fun z => qR z < k)).card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (ZR.card : ℝ) * M := by
            apply mul_le_mul_of_nonneg_right _ (by rw [hM]; positivity)
            exact_mod_cast Finset.card_filter_le _ _
    -- constants
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hF : ((2 ^ k * (k + 1).factorial : ℕ) : ℝ) * ((k : ℝ) + 1) ≤ 4 * (k : ℝ) ^ (3 * k) := by
      have := fact_bound k hk2; exact_mod_cast this
    have hk2' : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ (3 * k) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
    have hK1 : 2 * (2 * (k : ℝ) - 1) * ((k - 1 : ℕ) : ℝ) ^ (3 * (k - 1)) ≤ (k : ℝ) ^ (3 * k) := by
      have h := rec_bound k hk2
      have h' : (2 : ℝ) * (((2 * k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (3 * (k - 1))) ≤
          (k : ℝ) ^ (3 * k) := by exact_mod_cast h
      have e : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [e] at h'; linarith
    have key := main_alg ((k : ℝ) ^ (3 * k)) (((k - 1 : ℕ) : ℝ) ^ (3 * (k - 1))) X p Q Q1
      ((2 ^ k * (k + 1).factorial : ℕ) : ℝ) n m (alg3Delta n m k) ZG.card ZR.card T₀
      ((∑ z ∈ ZG.filter (fun z => qG z < k), TG z : ℕ) : ℝ)
      ((∑ z ∈ ZR.filter (fun z => qR z < k), TR z : ℕ) : ℝ) k hkR
      (by rw [hXdef]; push_cast; linarith) hp1 hpQ hQ1p hpleQ (by linarith) (Nat.cast_nonneg _)
      (by rw [hXdef]; push_cast; linarith) hXm hD2 (by linarith) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (hz ZG G hL2G) (hz ZR (Rev G) hL2R) (Nat.cast_nonneg _) hF hk2' hK1
      (by positivity) (Real.rpow_nonneg (by linarith) _) (by linarith) hT0 hsumG hsumR
    have hBd : Bd k m n = (k : ℝ) ^ (3 * k) * X * Q := by unfold Bd; rfl
    have hB0 := Bd_nonneg k m n
    rw [hBd] at hB0
    push_cast at key ⊢
    rw [hBd]
    constructor
    · linarith
    · intro _; linarith

end DirKECC1549.Main.CostAux

open DirKECC1549.Main DirKECC1549.Main.CostAux in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (G : Fin m → Fin n × Fin n) (k : ℕ)
      (P : Fin n → Fin n → Prop) (T : ℕ), 1 ≤ k → 1 ≤ n → Alg3CostRun n m G k P T →
      (T : ℝ) ≤ C * (k : ℝ) ^ (3 * k) * ((m + n : ℕ) : ℝ) * (n : ℝ) ^ (1 - eps k) := by
  refine ⟨64, by norm_num, fun n m G k P T hk hn h => ?_⟩
  have := (cost_aux G k P T h hk hn).1
  unfold Bd at this
  linarith
