-- Prove2me | solution 1 for BertsimasBrown2009.thm4_5_bounded_polytope_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:23:01.256995+00:00
-- url     : https://prove2.me/submissions/5f7ddabc-727e-4770-aae3-b8a62fd0fc50

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting

open RiskUncSets.InnerApprox Finset

/-- Telescoping bound, lower-left part. -/
theorem ph84_tel1 (Q C : ℕ → ℝ) (hQ : Monotone Q) (hC : Antitone C) (j : ℕ) :
    ∀ i, j ≤ i → ∑ k ∈ Ico j i, (Q (k+1) - Q k) * C k ≤ (Q i - Q j) * C j := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ i hji ih =>
    rw [Finset.sum_Ico_succ_top hji]
    have h1 : 0 ≤ Q (i+1) - Q i := sub_nonneg.mpr (hQ (Nat.le_succ i))
    have h2 : C i ≤ C j := hC hji
    have := mul_le_mul_of_nonneg_left h2 h1
    nlinarith

theorem ph84_tel2 (Q C : ℕ → ℝ) (hQ : Monotone Q) (hC : Antitone C) (i : ℕ) :
    ∀ j, i ≤ j → (Q j - Q i) * C j ≤ ∑ k ∈ Ico i j, (Q (k+1) - Q k) * C k := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [Finset.sum_Ico_succ_top hij]
    have h1 : 0 ≤ Q (j+1) - Q j := sub_nonneg.mpr (hQ (Nat.le_succ j))
    have h0 : 0 ≤ Q j - Q i := sub_nonneg.mpr (hQ hij)
    have h2 : C (j+1) ≤ C j := hC (Nat.le_succ j)
    have := mul_le_mul_of_nonneg_left h2 h1
    have := mul_le_mul_of_nonneg_left h2 h0
    nlinarith

/-- Core: explicit dual for sorted data (Monge cost). -/
theorem ph84_core {N : ℕ} (Q C : Fin N → ℝ) (hQ : Monotone Q) (hC : Antitone C) :
    ∃ u v : Fin N → ℝ, ∑ i, u i + ∑ j, v j = ∑ k, Q k * C k ∧
      ∀ i j, u i + v j ≤ Q i * C j := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, 0, by simp, fun i => i.elim0⟩
  let e : ℕ → Fin N := fun n => ⟨min n (N-1), by omega⟩
  have he : Monotone e := fun a b h => by
    simp only [e, Fin.mk_le_mk]; omega
  have hei : ∀ i : Fin N, e i.val = i := fun i => by
    ext; simp only [e]; omega
  set Q' : ℕ → ℝ := fun n => Q (e n)
  set C' : ℕ → ℝ := fun n => C (e n)
  have hQ' : Monotone Q' := hQ.comp he
  have hC' : Antitone C' := hC.comp_monotone he
  let u : Fin N → ℝ := fun i => ∑ k ∈ range i.val, (Q' (k+1) - Q' k) * C' k
  refine ⟨u, fun j => Q j * C j - u j, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib]; ring
  · intro i j
    have hQi : Q' i.val = Q i := by simp [Q', hei]
    have hQj : Q' j.val = Q j := by simp [Q', hei]
    have hCj : C' j.val = C j := by simp [C', hei]
    show u i + (Q j * C j - u j) ≤ Q i * C j
    rcases le_total j.val i.val with h | h
    · have hs : u i - u j = ∑ k ∈ Ico j.val i.val, (Q' (k+1) - Q' k) * C' k := by
        simp only [u]
        exact (Finset.sum_Ico_eq_sub _ h).symm
      have := ph84_tel1 Q' C' hQ' hC' j.val i.val h
      rw [hQi, hQj, hCj] at this
      nlinarith
    · have hs : u j - u i = ∑ k ∈ Ico i.val j.val, (Q' (k+1) - Q' k) * C' k := by
        simp only [u]
        exact (Finset.sum_Ico_eq_sub _ h).symm
      have := ph84_tel2 Q' C' hQ' hC' i.val j.val h
      rw [hQi, hQj, hCj] at this
      nlinarith

theorem bb86_dual {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (b : ℝ)
    (x : Fin n → ℝ) :
    (∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x) ↔
      ∃ y₁ y₂ : Fin N → ℝ, b ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
        ∀ i j, y₁ i + y₂ j ≤ q i * (a j ⬝ᵥ x) := by
  set c : Fin N → ℝ := fun j => a j ⬝ᵥ x with hc
  have hval : ∀ σ : Equiv.Perm (Fin N),
      (∑ i, q (σ i) • a i) ⬝ᵥ x = ∑ i, q (σ i) * c i := by
    intro σ
    rw [sum_dotProduct]
    simp [c, smul_dotProduct]
  constructor
  · intro h
    let τ := Tuple.sort q
    let π := Tuple.sort (fun j => -c j)
    have hτ : Monotone (q ∘ τ) := Tuple.monotone_sort q
    have hπ : Antitone (c ∘ π) := by
      intro i j hij
      have := Tuple.monotone_sort (fun j => -c j) hij
      simp only [Function.comp] at this ⊢; linarith
    obtain ⟨u, v, hsum, hle⟩ := ph84_core (q ∘ τ) (c ∘ π) hτ hπ
    refine ⟨fun i => u (τ.symm i), fun j => v (π.symm j), ?_, ?_⟩
    · have hb := h _ (subset_convexHull ℝ _ ⟨π.symm.trans τ, rfl⟩)
      rw [hval] at hb
      have e1 : ∑ i, u (τ.symm i) = ∑ i, u i := Equiv.sum_comp τ.symm u
      have e2 : ∑ j, v (π.symm j) = ∑ j, v j := Equiv.sum_comp π.symm v
      have e3 : ∑ i, q ((π.symm.trans τ) i) * c i = ∑ k, (q ∘ τ) k * (c ∘ π) k := by
        rw [← Equiv.sum_comp π]
        simp
      rw [e1, e2, hsum, ← e3]; exact hb
    · intro i j
      have := hle (τ.symm i) (π.symm j)
      simpa [c] using this
  · rintro ⟨y₁, y₂, hb, hy⟩ a' ha'
    have hconv : Convex ℝ {z : Fin n → ℝ | b ≤ z ⬝ᵥ x} := by
      exact convex_halfSpace_ge (f := fun z : Fin n → ℝ => z ⬝ᵥ x)
        (by constructor <;> intros <;> simp [add_dotProduct, smul_dotProduct]) b
    refine (convexHull_min ?_ hconv) ha'
    rintro _ ⟨σ, rfl⟩
    show b ≤ _
    rw [hval]
    have e1 : ∑ i, y₁ (σ i) = ∑ i, y₁ i := Equiv.sum_comp σ y₁
    calc b ≤ ∑ i, y₁ i + ∑ j, y₂ j := hb
      _ = ∑ i, (y₁ (σ i) + y₂ i) := by rw [Finset.sum_add_distrib, e1]
      _ ≤ ∑ i, q (σ i) * c i := Finset.sum_le_sum fun i _ => hy (σ i) i

theorem convex_polytope {n m : ℕ} {u : Fin m → Fin n → ℝ} {v : Fin m → ℝ} : Convex ℝ (polytope u v) := by
  intro x hx y hy s t hs ht hst k
  have := hx k; have := hy k
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have e : v k = s * v k + t * v k := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hx k) hs, mul_le_mul_of_nonneg_left (hy k) ht]


/-- LP (15) feasibility ⟺ permutohull containment. -/
theorem bb86_key {N n m : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) (lam : ℝ) :
    LP15Feasible q a u v lam ↔ permutohull (mix q lam) a ⊆ polytope u v := by
  constructor
  · rintro ⟨q', s, t, rfl, hv, hst⟩ p hp k
    have := (bb86_dual (mix q lam) a (v k) (u k)).mpr ⟨s k, t k, by
      rw [← Finset.sum_add_distrib]; exact hv k, fun i j => by
        rw [dotProduct_comm, mul_comm]; exact hst k i j⟩ p hp
    rw [dotProduct_comm]; exact this
  · intro h
    have hk : ∀ k, ∃ y₁ y₂ : Fin N → ℝ, v k ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
        ∀ i j, y₁ i + y₂ j ≤ mix q lam i * (a j ⬝ᵥ u k) := fun k =>
      (bb86_dual (mix q lam) a (v k) (u k)).mp (fun p hp => by
        rw [dotProduct_comm]; exact h hp k)
    choose s t hs ht using hk
    refine ⟨mix q lam, s, t, rfl, fun k => by rw [Finset.sum_add_distrib]; exact hs k, fun k i j => ?_⟩
    have h1 := ht k i j
    rw [dotProduct_comm (a j) (u k)] at h1
    linarith [mul_comm (mix q lam i) (u k ⬝ᵥ a j)]

/-- permutohull is invariant under permuting the weight vector. -/
theorem bb86_perm {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (σ0 : Equiv.Perm (Fin N)) :
    permutohull (fun i => q (σ0 i)) a = permutohull q a := by
  unfold permutohull
  congr 1
  ext p
  constructor
  · rintro ⟨σ, rfl⟩; exact ⟨σ.trans σ0, rfl⟩
  · rintro ⟨σ, rfl⟩; exact ⟨σ.trans σ0.symm, by simp⟩

theorem bb86_mix_sum {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : ∑ i, q i = 1) (lam : ℝ) :
    ∑ i, mix q lam i = 1 := by
  simp only [mix, Finset.sum_add_distrib, ← Finset.mul_sum, hq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp
  try ring

/-- the sample mean lies in every permutohull of a probability-sum weight. -/
theorem bb86_mean_mem {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : ∑ i, q i = 1)
    (a : Fin N → Fin n → ℝ) : sampleMean a ∈ permutohull q a := by
  have : NeZero N := ⟨hN.ne'⟩
  let p : Fin N → Fin n → ℝ := fun r => ∑ i, q ((Equiv.addRight r) i) • a i
  have hp : ∀ r, p r ∈ permutohull q a := fun r => subset_convexHull ℝ _ ⟨Equiv.addRight r, rfl⟩
  have hsum : sampleMean a = ∑ r, (1 / (N : ℝ)) • p r := by
    unfold sampleMean
    simp only [p, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_smul, ← Finset.mul_sum]
    have : ∑ r : Fin N, q ((Equiv.addRight r) i) = 1 := by
      rw [← hq]
      exact Equiv.sum_comp (Equiv.addLeft i) q
    rw [this, mul_one]
  rw [hsum]
  apply (convex_convexHull ℝ _).sum_mem
  · intro _ _; positivity
  · simp [Finset.card_univ]; try field_simp
  · intro r _; exact hp r

theorem bb86_mono {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : ∑ i, q i = 1)
    (a : Fin N → Fin n → ℝ) {μ L : ℝ} (hμ : 0 ≤ μ) (hμL : μ ≤ L) :
    permutohull (mix q μ) a ⊆ permutohull (mix q L) a := by
  rcases eq_or_lt_of_le (hμ.trans hμL) with hL | hL
  · have : μ = L := by linarith
    rw [this]
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨σ, rfl⟩
  set θ := μ / L
  have hθ0 : 0 ≤ θ := div_nonneg hμ hL.le
  have hθ1 : θ ≤ 1 := (div_le_one hL).mpr hμL
  have hmean := bb86_mean_mem hN (mix q L) (bb86_mix_sum hN q hq L) a
  have hgen : (∑ i, mix q L (σ i) • a i) ∈ permutohull (mix q L) a :=
    subset_convexHull ℝ _ ⟨σ, rfl⟩
  have e : (∑ i, mix q μ (σ i) • a i) = θ • (∑ i, mix q L (σ i) • a i) + (1 - θ) • sampleMean a := by
    unfold sampleMean
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    simp only [mix, θ]
    field_simp; ring
  show (∑ i, mix q μ (σ i) • a i) ∈ _
  rw [e]
  exact (convex_convexHull ℝ _) hgen hmean hθ0 (by linarith) (by ring)

theorem solution {N n m : ℕ} (hN : 0 < N)
    (qh : Fin N → ℝ) (hqh : qh ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ)
    (hbdd : Bornology.IsBounded (polytope u v)) (hmean : sampleMean a ∈ polytope u v)
    (lamStar : ℝ) (hopt : IsGreatest {lam | LP15Feasible qh a u v lam} lamStar) :
    permutohull (mix qh lamStar) a ⊆ polytope u v ∧
    (∀ lam : ℝ, permutohull (mix qh lam) a ⊆ polytope u v →
      permutohull (mix qh lam) a ⊆ permutohull (mix qh lamStar) a) ∧
    ((N : ℝ) * (⨅ i, qh i) < 1 →
      (mix qh lamStar ∈ restrictedSimplex N ↔
        lamStar ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i))) := by
  obtain ⟨⟨⟨hq0, hq1⟩, hanti⟩, σ0, hσ0⟩ := hqh
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- symmetry: mix (-λ) is a permutation of mix λ
  have hneg : ∀ lam, permutohull (mix qh (-lam)) a = permutohull (mix qh lam) a := by
    intro lam
    rw [← bb86_perm (mix qh lam) a σ0]
    congr 1
    funext i
    simp only [mix]
    have := congrFun hσ0 i
    rw [this]; ring
  have habs : ∀ lam, permutohull (mix qh |lam|) a = permutohull (mix qh lam) a := by
    intro lam
    rcases abs_cases lam with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hneg]
  have hfeas : ∀ lam, permutohull (mix qh lam) a ⊆ polytope u v → |lam| ≤ lamStar := by
    intro lam h
    apply hopt.2
    show LP15Feasible qh a u v |lam|
    rw [bb86_key, habs]; exact h
  have h0 : 0 ≤ lamStar := by
    have := hfeas 0 (by
      apply convexHull_min _ (convex_polytope)
      rintro _ ⟨σ, rfl⟩
      have : (∑ i, mix qh 0 (σ i) • a i) = sampleMean a := by
        unfold sampleMean; simp [mix]
      show (∑ i, mix qh 0 (σ i) • a i) ∈ _
      rw [this]; exact hmean)
    simpa using this
  refine ⟨(bb86_key qh a u v lamStar).mp hopt.1, ?_, ?_⟩
  · intro lam h
    rw [← habs lam]
    exact bb86_mono hN qh hq1 a (abs_nonneg lam) (hfeas lam h)
  · intro hlt
    -- the infimum is the last entry
    set j : Fin N := ⟨N - 1, by omega⟩
    have hinf : (⨅ i, qh i) = qh j := by
      apply le_antisymm (ciInf_le (Set.finite_range qh).bddBelow j)
      haveI : Nonempty (Fin N) := ⟨j⟩
      exact le_ciInf (fun i => hanti (show i ≤ j by simp only [Fin.le_def, j]; omega))
    rw [hinf] at hlt ⊢
    have hpos : 0 < 1 - (N : ℝ) * qh j := by linarith
    constructor
    · rintro ⟨⟨hm0, _⟩, _⟩
      have := hm0 j
      simp only [mix] at this
      rw [le_div_iff₀ hpos]
      have e : lamStar * (1 - N * qh j) = 1 - N * (lamStar * qh j + (1 - lamStar) * (1 / N)) := by
        field_simp; ring
      rw [e]
      nlinarith
    · intro hle
      rw [le_div_iff₀ hpos] at hle
      refine ⟨⟨fun i => ?_, bb86_mix_sum hN qh hq1 lamStar⟩, ?_⟩
      · have hij : qh j ≤ qh i := hanti (show i ≤ j by simp only [Fin.le_def, j]; omega)
        simp only [mix]
        have : 0 ≤ lamStar * qh j + (1 - lamStar) * (1 / N) := by
          have e : lamStar * qh j + (1 - lamStar) * (1 / N) = (1 - lamStar * (1 - N * qh j)) / N := by
            field_simp; ring
          rw [e]; apply div_nonneg <;> linarith
        nlinarith [mul_le_mul_of_nonneg_left hij h0]
      · intro i i' hii'
        simp only [mix]
        nlinarith [mul_le_mul_of_nonneg_left (hanti hii') h0]
