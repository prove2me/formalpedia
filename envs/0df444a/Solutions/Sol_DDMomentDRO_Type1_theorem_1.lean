-- Prove2me | solution 1 for DDMomentDRO.Type1.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:54:34.7168+00:00
-- url     : https://prove2.me/submissions/f67f307e-921d-4122-82bb-a74f3a3cb9f1

import Mathlib
import Definitions.Def_DDMomentDRO_Type1_Setting


namespace DualityKit

open Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

-- K0: pointwise duality to joint minimization
theorem isLeast_add_isGreatest_iff {X : Type*} (S : Set X) (g : X → ℝ)
    (W D : X → Set ℝ) (h : ∀ x ∈ S, ∃ w, IsGreatest (W x) w ∧ IsLeast (D x) w) (q : ℝ) :
    IsLeast {v | ∃ x ∈ S, ∃ w, IsGreatest (W x) w ∧ v = g x + w} q ↔
      IsLeast {v | ∃ x ∈ S, ∃ d ∈ D x, v = g x + d} q := by
  have key : ∀ x ∈ S, ∀ w, IsGreatest (W x) w → IsLeast (D x) w := by
    intro x hx w hw
    obtain ⟨w', hw', hd'⟩ := h x hx
    rw [hw.unique hw']
    exact hd'
  constructor
  · rintro ⟨⟨x, hx, w, hw, rfl⟩, hlow⟩
    refine ⟨⟨x, hx, w, (key x hx w hw).1, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', d', hd', rfl⟩
    obtain ⟨w', hw', hdw'⟩ := h x' hx'
    have h1 := hlow ⟨x', hx', w', hw', rfl⟩
    have h2 := hdw'.2 hd'
    linarith
  · rintro ⟨⟨x, hx, d, hd, rfl⟩, hlow⟩
    obtain ⟨w, hw, hdw⟩ := h x hx
    have h1 := hdw.2 hd
    have h2 := hlow ⟨x, hx, w, hdw.1, rfl⟩
    refine ⟨⟨x, hx, w, hw, by linarith⟩, ?_⟩
    rintro _ ⟨x', hx', w', hw', rfl⟩
    exact hlow ⟨x', hx', w', (key x' hx' w' hw').1, rfl⟩

section aux1cone
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [Fintype G] [DecidableEq G] (u : G → F)

def aux1_coneS (s : Finset G) : Set F :=
  {x | ∃ c : G → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ x = ∑ k, c k • u k}

omit [FiniteDimensional ℝ F] [DecidableEq G] in
lemma aux1_sum_sub_eq (s : Finset G) (c : G → ℝ) (hc : ∀ k ∉ s, c k = 0) :
    ∑ k : s, c k • u k = ∑ k, c k • u k := by
  rw [Finset.sum_coe_sort s (fun k => c k • u k)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by rw [hc k hk, zero_smul])

omit [FiniteDimensional ℝ F] in
lemma aux1_coneS_LI_closed (s : Finset G) (hli : LinearIndependent ℝ (fun k : s => u k)) :
    IsClosed (aux1_coneS u s) := by
  set Λ := Fintype.linearCombination ℝ (fun k : s => u k) with hΛ
  have hker : LinearMap.ker Λ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hΛ, Fintype.linearCombination_apply] at hc
    funext k
    exact Fintype.linearIndependent_iff.1 hli c hc k
  have heq : aux1_coneS u s = Λ '' {c | ∀ k, 0 ≤ c k} := by
    ext x
    constructor
    · rintro ⟨c, hc0, hcs, rfl⟩
      refine ⟨fun k => c k, fun k => hc0 k, ?_⟩
      rw [hΛ, Fintype.linearCombination_apply]
      exact aux1_sum_sub_eq u s c hcs
    · rintro ⟨c, hc0, rfl⟩
      refine ⟨fun k => if h : k ∈ s then c ⟨k, h⟩ else 0, fun k => ?_, fun k hk => ?_, ?_⟩
      · by_cases h : k ∈ s
        · simp only [h, dif_pos]; exact hc0 _
        · simp [h]
      · simp [hk]
      · rw [hΛ, Fintype.linearCombination_apply,
          ← aux1_sum_sub_eq u s _ (fun k hk => by simp [hk])]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp
  have hQ : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext; simp
  rw [heq, hQ]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _
    (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k))

omit [FiniteDimensional ℝ F] in
lemma aux1_cara_step (s : Finset G) (hdep : ¬ LinearIndependent ℝ (fun k : s => u k)) :
    aux1_coneS u s ⊆ ⋃ k ∈ s, aux1_coneS u (s.erase k) := by
  rintro x ⟨c, hc0, hcs, rfl⟩
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  set a0 : G → ℝ := fun k => if h : k ∈ s then g ⟨k, h⟩ else 0 with ha0
  have ha0s : ∀ k ∉ s, a0 k = 0 := fun k hk => by simp [ha0, hk]
  have ha0sum : ∑ k, a0 k • u k = 0 := by
    rw [← aux1_sum_sub_eq u s a0 ha0s, ← hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ha0]
  have ha0i : a0 i ≠ 0 := by simpa [ha0] using hi
  obtain ⟨a, has, hasum, k1, hk1⟩ : ∃ a : G → ℝ, (∀ k ∉ s, a k = 0) ∧ ∑ k, a k • u k = 0 ∧
      ∃ k1, 0 < a k1 := by
    rcases lt_or_gt_of_ne ha0i with h | h
    · refine ⟨-a0, fun k hk => by simp [ha0s k hk], ?_, i, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, ha0sum]
    · exact ⟨a0, ha0s, ha0sum, i, h⟩
  have hk1s : k1 ∈ s := by by_contra h; rw [has k1 h] at hk1; exact lt_irrefl _ hk1
  set P := s.filter (fun k => 0 < a k) with hP
  have hPne : P.Nonempty := ⟨k1, Finset.mem_filter.2 ⟨hk1s, hk1⟩⟩
  obtain ⟨k0, hk0P, hmin⟩ := Finset.exists_min_image P (fun k => c k / a k) hPne
  have hk0 := Finset.mem_filter.1 hk0P
  set t := c k0 / a k0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 k0) hk0.2.le
  refine Set.mem_biUnion hk0.1 ⟨fun k => c k - t * a k, fun k => ?_, fun k hk => ?_, ?_⟩
  · by_cases hak : 0 < a k
    · by_cases hks : k ∈ s
      · have := hmin k (Finset.mem_filter.2 ⟨hks, hak⟩)
        rw [div_le_div_iff₀ hk0.2 hak] at this
        have : t * a k ≤ c k := by
          rw [ht, div_mul_eq_mul_div, div_le_iff₀ hk0.2]; linarith
        linarith
      · rw [has k hks] at hak; exact absurd hak (lt_irrefl _)
    · push Not at hak
      nlinarith [hc0 k]
  · rcases Finset.mem_erase.not.1 hk |> not_and_or.1 with h | h
    · push Not at h; subst h
      show c k - t * a k = 0
      rw [ht, div_mul_cancel₀ _ hk0.2.ne', sub_self]
    · show c k - t * a k = 0
      rw [hcs k h, has k h]; ring
  · simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hasum, smul_zero,
      sub_zero]

lemma aux1_coneS_closed : ∀ s : Finset G, IsClosed (aux1_coneS u s) := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hli : LinearIndependent ℝ (fun k : s => u k)
    · exact aux1_coneS_LI_closed u s hli
    · have heq : aux1_coneS u s = ⋃ k ∈ s, aux1_coneS u (s.erase k) := by
        refine Set.Subset.antisymm (aux1_cara_step u s hli) ?_
        refine Set.iUnion₂_subset fun k _ => ?_
        rintro x ⟨c, hc0, hcs, rfl⟩
        exact ⟨c, hc0, fun j hj => hcs j (fun h => hj (Finset.mem_of_mem_erase h)), rfl⟩
      rw [heq]
      exact isClosed_biUnion_finset fun k hk => ih _ (Finset.erase_ssubset hk)

end aux1cone

-- K1: closedness of finitely generated cones
/-- Finitely generated cones are closed (the missing Mathlib fact). -/
theorem isClosed_finite_cone {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (u : κ → F) :
    IsClosed {w | ∃ c : κ → ℝ, 0 ≤ c ∧ w = ∑ k, c k • u k} := by
  classical
  have h := aux1_coneS_closed u Finset.univ
  convert h using 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, fun k hk => absurd (Finset.mem_univ k) hk, rfl⟩
  · rintro ⟨c, hc, -, rfl⟩; exact ⟨c, hc, rfl⟩


lemma aux1_linear_pi {α : Type*} [Fintype α] [DecidableEq α] (L : (α → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) :
    L p = ∑ i, p i * L (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ L p]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

lemma aux1_prod_decomp {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (L : (α → ℝ) × (β → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) (q : β → ℝ) :
    L (p, q) = ∑ i, p i * L (Pi.single i 1, 0) + ∑ j, q j * L (0, Pi.single j 1) := by
  have h1 : L (p, q) = (L ∘ₗ LinearMap.inl ℝ _ _) p + (L ∘ₗ LinearMap.inr ℝ _ _) q := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [h1, aux1_linear_pi, aux1_linear_pi]
  rfl

-- K1: Farkas alternative
/-- Farkas, mixed inequality/equality system, functional form. -/
theorem LP.farkas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) :
    (¬ ∃ x : E, (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j) ↔
      ∃ (y : ι → ℝ) (z : κ → ℝ), 0 ≤ y ∧
        ∑ i, y i • a i + ∑ j, z j • e j = 0 ∧ y ⬝ᵥ b + z ⬝ᵥ d < 0 := by
  classical
  constructor
  · intro hno
    set bas := Module.finBasis ℝ E
    let M : E →ₗ[ℝ] (ι → ℝ) × (κ → ℝ) := (LinearMap.pi a).prod (LinearMap.pi e)
    have hMx : ∀ x, M x = (fun i => a i x, fun j => e j x) := fun x => rfl
    let u : ι ⊕ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → (ι → ℝ) × (κ → ℝ) :=
      fun g => match g with
        | Sum.inl i => (Pi.single i 1, 0)
        | Sum.inr (Sum.inl k) => M (bas k)
        | Sum.inr (Sum.inr k) => -M (bas k)
    set S := {w | ∃ c : ι ⊕ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → ℝ,
      0 ≤ c ∧ w = ∑ g, c g • u g} with hS
    have hcl : IsClosed S := isClosed_finite_cone u
    have hcv : Convex ℝ S := by
      rintro w1 ⟨c1, h1, rfl⟩ w2 ⟨c2, h2, rfl⟩ s t hs ht _
      refine ⟨s • c1 + t • c2, fun g => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact add_nonneg (mul_nonneg hs (h1 g)) (mul_nonneg ht (h2 g))
      · simp [add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
    have hzero : (0 : (ι → ℝ) × (κ → ℝ)) ∈ S := ⟨0, le_rfl, by simp⟩
    have hsmul : ∀ w ∈ S, ∀ t : ℝ, 0 ≤ t → t • w ∈ S := by
      rintro w ⟨c, hc, rfl⟩ t ht
      refine ⟨t • c, fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ht (hc g)
      · simp [Finset.smul_sum, mul_smul]
    have hgen : ∀ g, u g ∈ S := by
      intro g
      refine ⟨Pi.single g 1, fun h => ?_, ?_⟩
      · by_cases hh : h = g
        · subst hh; simp
        · simp [Pi.single_apply, hh]
      · rw [Finset.sum_eq_single g (fun h _ hh => by simp [Pi.single_apply, hh])
          (fun h => absurd (Finset.mem_univ g) h)]
        simp
    have hM : ∀ x, M x ∈ S := by
      intro x
      refine ⟨fun g => match g with
        | Sum.inl _ => 0
        | Sum.inr (Sum.inl k) => (bas.repr x k)⁺
        | Sum.inr (Sum.inr k) => (bas.repr x k)⁻, fun g => ?_, ?_⟩
      · rcases g with i | k | k
        · exact le_rfl
        · exact posPart_nonneg _
        · exact negPart_nonneg _
      · symm
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [u, zero_smul, Finset.sum_const_zero, zero_add, smul_neg]
        rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        simp_rw [← sub_smul, posPart_sub_negPart, ← map_smul]
        rw [← map_sum, bas.sum_repr]
    have hnot : (b, d) ∉ S := by
      rintro ⟨c, hc, hbd⟩
      set x := ∑ k, (c (Sum.inr (Sum.inl k)) - c (Sum.inr (Sum.inr k))) • bas k with hx
      have hsum : ∑ g, c g • u g = (fun i => c (Sum.inl i), 0) + M x := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [u, smul_neg]
        rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]
        have hMx' : M x = ∑ k, c (Sum.inr (Sum.inl k)) • M (bas k) -
            ∑ k, c (Sum.inr (Sum.inr k)) • M (bas k) := by
          rw [hx]
          simp only [sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_smul]
        rw [hMx']
        congr 1
        ext i
        · rw [Prod.fst_sum, Finset.sum_apply]; simp [Pi.single_apply]
        · rw [Prod.snd_sum]; simp
      rw [hsum] at hbd
      apply hno
      refine ⟨x, fun i => ?_, fun j => ?_⟩
      · have := congrFun (congrArg Prod.fst hbd) i
        rw [hMx] at this
        simp only [Prod.fst_add, Pi.add_apply] at this
        have h0 : (0:ℝ) ≤ c (Sum.inl i) := hc (Sum.inl i)
        linarith
      · have := congrFun (congrArg Prod.snd hbd) j
        rw [hMx] at this
        simp only [Prod.snd_add, Pi.add_apply, Prod.snd_zero, Pi.zero_apply, zero_add] at this
        exact this.symm
    obtain ⟨Fl, s, hFw, hFb⟩ := geometric_hahn_banach_point_closed hcv hcl hnot
    have hs0 : s < 0 := by simpa using hFb 0 hzero
    have hFnn : ∀ w ∈ S, 0 ≤ Fl w := by
      intro w hw
      by_contra hneg
      push Not at hneg
      have hmem := hsmul w hw (s / Fl w) (div_nonneg_of_nonpos hs0.le hneg.le)
      have := hFb _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
      exact lt_irrefl _ this
    have hFM : ∀ x, Fl (M x) = 0 := by
      intro x
      have h1 := hFnn _ (hM x)
      have h2 := hFnn _ (hM (-x))
      rw [map_neg, map_neg] at h2
      linarith
    have hdec := aux1_prod_decomp (Fl : (ι → ℝ) × (κ → ℝ) →L[ℝ] ℝ).toLinearMap
    refine ⟨fun i => Fl (Pi.single i 1, 0), fun j => Fl (0, Pi.single j 1),
      fun i => hFnn _ (hgen (Sum.inl i)), ?_, ?_⟩
    · ext x
      have := hFM x
      rw [hMx] at this
      have h2 := hdec (fun i => a i x) (fun j => e j x)
      simp only [ContinuousLinearMap.coe_coe] at h2
      rw [this] at h2
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply]
      rw [h2]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · have h2 := hdec b d
      simp only [ContinuousLinearMap.coe_coe] at h2
      have : Fl (b, d) < 0 := hFw.trans hs0
      rw [h2] at this
      simp only [dotProduct]
      convert this using 2 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rintro ⟨y, z, hy, hsum, hneg⟩ ⟨x, hax, hex⟩
    have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply, hex] at h
    have hle : ∑ i, y i * a i x ≤ ∑ i, y i * b i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
    simp only [dotProduct] at hneg
    linarith


-- K2: primal feasible set
/-- Primal: maximize `c x` subject to `a i x ≤ b i`, `e j x = d j` (`x` free in `E`). -/
def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

-- K2: dual feasible set
/-- Dual: `y ≥ 0`, `z` free, `Σ yᵢ aᵢ + Σ zⱼ eⱼ = c`; objective `y ⬝ᵥ b + z ⬝ᵥ d` (minimize). -/
def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

-- K2: weak duality
theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith


/-- The dual constraint map `(y, z) ↦ Σ yᵢ aᵢ + Σ zⱼ eⱼ`. -/
def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

/-- The dual objective `(y, z) ↦ y ⬝ᵥ b + z ⬝ᵥ d`. -/
def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

-- K2: strong duality with attainment
/-- Both feasible ⇒ both optima attained and equal. (No constraint qualification needed.) -/
theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

-- K2: bounded primal gives dual feasibility
/-- Primal feasible and bounded ⇒ dual feasible. -/
theorem LP.dualFeas_nonempty_of_bddAbove
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) : (LP.DualFeas a e c).Nonempty := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨yz, hyz, -⟩ := aux1_alt a b e d c hP (M + 1) fun x hx => by
    have := hM ⟨x, hx, rfl⟩
    linarith
  exact ⟨yz, hyz⟩

-- K2: infeasible primal gives unbounded dual
/-- Primal infeasible, dual feasible ⇒ dual unbounded below. -/
theorem LP.not_bddBelow_dual_of_infeasible
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : LP.Feas a b e d = ∅)
    (hD : (LP.DualFeas a e c).Nonempty) :
    ¬ BddBelow ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) := by
  rintro ⟨L, hL⟩
  obtain ⟨y0, z0, hy0, hsum0, hneg0⟩ := (LP.farkas a b e d).1 (by
    rintro ⟨x, hx⟩
    have : x ∈ LP.Feas a b e d := hx
    rw [hP] at this
    exact this)
  obtain ⟨yz, hy, hsum⟩ := hD
  have hLle : L ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := hL ⟨yz, ⟨hy, hsum⟩, rfl⟩
  set g := y0 ⬝ᵥ b + z0 ⬝ᵥ d with hg
  set t := (yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d - L + 1) / (-g) with ht
  have hgpos : 0 < -g := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hgpos.le
  have htg : t * g = -(yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d - L + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff hgpos.ne']; ring
  have hmem : (yz.1 + t • y0, yz.2 + t • z0) ∈ LP.DualFeas a e c := by
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : (0:ℝ) ≤ yz.1 i := hy i
      have h2 : (0:ℝ) ≤ y0 i := hy0 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, ← Finset.smul_sum]
      calc _ = (∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j) +
            t • (∑ i, y0 i • a i + ∑ j, z0 j • e j) := by rw [smul_add]; abel
        _ = c := by rw [hsum, hsum0, smul_zero, add_zero]
  have := hL ⟨_, hmem, rfl⟩
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at this
  have : L ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d + t * g := by rw [hg]; linarith
  linarith

-- K2: EReal value form
/-- EReal value form: equal unless both sides are infeasible (then `⊥ ≠ ⊤`). -/
theorem LP.ereal_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (h : (LP.Feas a b e d).Nonempty ∨ (LP.DualFeas a e c).Nonempty) :
    ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) =
      ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) := by
  by_cases hP : (LP.Feas a b e d).Nonempty <;> by_cases hD : (LP.DualFeas a e c).Nonempty
  · obtain ⟨v, ⟨⟨x, hx, hxv⟩, hvub⟩, ⟨⟨yz, hyz, hyzv⟩, hvlb⟩⟩ :=
      LP.strong_duality a b e d c hP hD
    have hL : ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) = (v : EReal) := by
      refine le_antisymm (iSup₂_le fun x' hx' => EReal.coe_le_coe_iff.2 (hvub ⟨x', hx', rfl⟩)) ?_
      exact le_iSup₂_of_le x hx (by rw [hxv])
    have hR : ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) = (v : EReal) := by
      refine le_antisymm ?_ (le_iInf₂ fun yz' hyz' => EReal.coe_le_coe_iff.2
        (hvlb ⟨yz', hyz', rfl⟩))
      exact iInf₂_le_of_le yz hyz (by rw [← hyzv])
    rw [hL, hR]
  · have hR : ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) = ⊤ := by
      refine iInf₂_eq_top.2 fun yz hyz => absurd ⟨yz, hyz⟩ hD
    rw [hR, EReal.eq_top_iff_forall_lt]
    intro r
    have hnb : ¬ BddAbove (c '' LP.Feas a b e d) := fun hb =>
      hD (LP.dualFeas_nonempty_of_bddAbove a b e d c hP hb)
    rw [not_bddAbove_iff] at hnb
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := hnb r
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlt) (le_iSup₂_of_le x hx le_rfl)
  · have hL : ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) = ⊥ := by
      refine iSup₂_eq_bot.2 fun x hx => absurd ⟨x, hx⟩ hP
    rw [hL, eq_comm, EReal.eq_bot_iff_forall_lt]
    intro r
    have hnb := LP.not_bddBelow_dual_of_infeasible a b e d c
      (Set.not_nonempty_iff_eq_empty.1 hP) hD
    rw [not_bddBelow_iff] at hnb
    obtain ⟨_, ⟨yz, hyz, rfl⟩, hlt⟩ := hnb r
    exact lt_of_le_of_lt (iInf₂_le_of_le yz hyz le_rfl) (EReal.coe_lt_coe_iff.2 hlt)
  · exact absurd h (by tauto)


/-- The functional `v ↦ u ⬝ᵥ v`. -/
def aux1_dotL {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun v := u ⬝ᵥ v
  map_add' v w := dotProduct_add u v w
  map_smul' t v := by simp [dotProduct_smul]

lemma aux1_dotL_apply {n : Type*} [Fintype n] (u v : n → ℝ) : aux1_dotL u v = u ⬝ᵥ v := rfl

lemma aux1_dotL_inj {n : Type*} [Fintype n] {u w : n → ℝ} (h : aux1_dotL u = aux1_dotL w) :
    u = w := by
  classical
  funext j
  have := congrArg (fun φ : Module.Dual ℝ (n → ℝ) => φ (Pi.single j 1)) h
  simpa [aux1_dotL_apply, dotProduct_single] using this

lemma aux1_sum_dotL {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (y : m → ℝ) :
    ∑ i, y i • aux1_dotL (A i) = aux1_dotL (Aᵀ *ᵥ y) := by
  ext v
  rw [LinearMap.sum_apply, aux1_dotL_apply, mulVec_transpose, ← dotProduct_mulVec]
  simp only [LinearMap.smul_apply, smul_eq_mul, aux1_dotL_apply, dotProduct]
  rfl

lemma aux1_matFeas {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ)
    (x : n → ℝ) :
    x ∈ LP.Feas (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim) ↔
      A *ᵥ x ≤ b :=
  ⟨fun h i => h.1 i, fun h => ⟨fun i => h i, fun j => j.elim⟩⟩

lemma aux1_matDual {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : n → ℝ)
    (yz : (m → ℝ) × (Empty → ℝ)) :
    yz ∈ LP.DualFeas (fun i => aux1_dotL (A i)) (fun j : Empty => j.elim) (aux1_dotL c) ↔
      0 ≤ yz.1 ∧ Aᵀ *ᵥ yz.1 = c := by
  simp only [LP.DualFeas, Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    aux1_sum_dotL]
  exact and_congr Iff.rfl ⟨aux1_dotL_inj, fun h => by rw [h]⟩

-- K2 (matrix corollary): strong duality for `max c⬝x, A x ≤ b`
theorem LP.strong_duality_matrix {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ c ⬝ᵥ x = b ⬝ᵥ y ∧
      (∀ x', A *ᵥ x' ≤ b → c ⬝ᵥ x' ≤ c ⬝ᵥ x) := by
  obtain ⟨x0, hx0⟩ := hP
  obtain ⟨y0, hy0, hy0c⟩ := hD
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, hub⟩, ⟨⟨yz, hyz, hyzv⟩, -⟩⟩ :=
    LP.strong_duality (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim)
      (aux1_dotL c) ⟨x0, (aux1_matFeas A b x0).2 hx0⟩
      ⟨(y0, fun j => j.elim), (aux1_matDual A c _).2 ⟨hy0, hy0c⟩⟩
  obtain ⟨hy, hyc⟩ := (aux1_matDual A c yz).1 hyz
  refine ⟨x, yz.1, (aux1_matFeas A b x).1 hx, hy, hyc, ?_, fun x' hx' => ?_⟩
  · rw [aux1_dotL_apply] at hxv
    have h0 : yz.2 ⬝ᵥ (fun j : Empty => j.elim) = 0 := by simp [dotProduct]
    simp only [h0, add_zero] at hyzv
    rw [hxv, ← hyzv, dotProduct_comm]
  · have := hub ⟨x', (aux1_matFeas A b x').2 hx', rfl⟩
    rw [← hxv] at this
    exact this

-- K2 (matrix corollary): bounded polyhedron gives dual feasibility
/-- A nonempty bounded polyhedron has a feasible dual for every cost. -/
theorem LP.exists_dual_of_isBounded {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (hne : {x | A *ᵥ x ≤ b}.Nonempty)
    (hbd : Bornology.IsBounded {x | A *ᵥ x ≤ b}) (c : n → ℝ) :
    ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbd
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨yz, hyz⟩ := LP.dualFeas_nonempty_of_bddAbove (fun i => aux1_dotL (A i)) b
    (fun j : Empty => j.elim) (fun j => j.elim) (aux1_dotL c)
    ⟨x0, (aux1_matFeas A b x0).2 hx0⟩ (by
      refine ⟨∑ i, |c i| * R, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hxR := hR x ((aux1_matFeas A b x).1 hx)
      rw [aux1_dotL_apply, dotProduct]
      refine Finset.sum_le_sum fun i _ => ?_
      calc c i * x i ≤ |c i * x i| := le_abs_self _
        _ = |c i| * |x i| := abs_mul _ _
        _ ≤ |c i| * R := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at this
          linarith)
  exact ⟨yz.1, (aux1_matDual A c yz).1 hyz⟩

-- K2-aux: functionals on `n → ℝ` are dot products
theorem Module.Dual.exists_dotProduct_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (n → ℝ)) : ∃ u : n → ℝ, ∀ v, φ v = u ⬝ᵥ v := by
  refine ⟨fun i => φ (Pi.single i 1), fun v => ?_⟩
  rw [aux1_linear_pi φ v, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

-- K2-aux: functionals on matrices are trace pairings
theorem Module.Dual.exists_trace_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (Matrix n n ℝ)) : ∃ Y : Matrix n n ℝ, ∀ A, φ A = (Yᵀ * A).trace := by
  refine ⟨Matrix.of fun i j => φ (Matrix.single i j 1), fun A => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  have hs : ∀ i j, Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
    intro i j; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [map_sum, hs, map_smul, smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end DualityKit

namespace RRAux_DDMomentDRO_Type1_theorem_1

open Matrix

variable {K m : ℕ}

def lf (w : Fin K → ℝ) : Module.Dual ℝ (Fin K → ℝ) where
  toFun p := w ⬝ᵥ p
  map_add' p q := dotProduct_add w p q
  map_smul' c p := by simp [dotProduct_smul]

@[simp] lemma lf_apply (w p : Fin K → ℝ) : lf w p = w ⬝ᵥ p := rfl

lemma sum_smul_lf {ι : Type*} [Fintype ι] (y : ι → ℝ) (w : ι → Fin K → ℝ) :
    ∑ i, y i • lf (w i) = lf (∑ i, y i • w i) := by
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, lf_apply, smul_eq_mul, dotProduct, Finset.sum_apply,
    Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

lemma lf_inj {w w' : Fin K → ℝ} (h : lf w = lf w') : w = w' := by
  funext k
  have := congrArg (fun φ => φ (Pi.single k 1)) h
  simpa [dotProduct_single] using this

abbrev Idx (K m : ℕ) := Fin K ⊕ Fin K ⊕ Fin m ⊕ Fin m ⊕ Fin K

def wv (F : Fin K → Fin m → ℝ) : Idx K m → Fin K → ℝ
  | .inl k => -Pi.single k 1
  | .inr (.inl k) => Pi.single k 1
  | .inr (.inr (.inl s)) => -(fun k => F k s)
  | .inr (.inr (.inr (.inl s))) => fun k => F k s
  | .inr (.inr (.inr (.inr k))) => -Pi.single k 1

def bv (lo hi : Fin m → ℝ) (pL pU : Fin K → ℝ) : Idx K m → ℝ
  | .inl k => -pL k
  | .inr (.inl k) => pU k
  | .inr (.inr (.inl s)) => -lo s
  | .inr (.inr (.inr (.inl s))) => hi s
  | .inr (.inr (.inr (.inr _))) => 0

lemma mom_eq (F : Fin K → Fin m → ℝ) (p : Fin K → ℝ) (s : Fin m) :
    (fun k => F k s) ⬝ᵥ p = (∑ k, p k • F k) s := by
  simp [dotProduct, Finset.sum_apply, mul_comm]

lemma feas_iff (F : Fin K → Fin m → ℝ) (lo hi : Fin m → ℝ) (pL pU : Fin K → ℝ)
    (p : Fin K → ℝ) :
    p ∈ DualityKit.LP.Feas (fun i => lf (wv F i)) (bv lo hi pL pU)
        (fun j : Empty => j.elim) (fun j => j.elim) ↔
      (pL ≤ p ∧ p ≤ pU ∧ lo ≤ ∑ k, p k • F k ∧ ∑ k, p k • F k ≤ hi ∧ ∀ k, 0 ≤ p k) := by
  constructor
  · rintro ⟨h, -⟩
    refine ⟨fun k => ?_, fun k => ?_, fun s => ?_, fun s => ?_, fun k => ?_⟩
    · have := h (.inl k); simp [wv, bv] at this; linarith
    · have := h (.inr (.inl k)); simpa [wv, bv] using this
    · have := h (.inr (.inr (.inl s))); simp only [lf_apply, wv, bv, neg_dotProduct,
        mom_eq] at this; linarith
    · have := h (.inr (.inr (.inr (.inl s)))); simp only [lf_apply, wv, bv, mom_eq] at this
      exact this
    · have := h (.inr (.inr (.inr (.inr k)))); simp [wv, bv] at this; linarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, fun j => j.elim⟩
    rintro (k | k | s | s | k)
    · simp [wv, bv]; exact h1 k
    · simpa [wv, bv] using h2 k
    · simp only [lf_apply, wv, bv, neg_dotProduct, mom_eq]; linarith [h3 s]
    · simp only [lf_apply, wv, bv, mom_eq]; exact h4 s
    · simp [wv, bv]; exact h5 k

lemma sum_wv (F : Fin K → Fin m → ℝ) (y : Idx K m → ℝ) (k : Fin K) :
    (∑ i, y i • wv F i) k = -y (.inl k) + y (.inr (.inl k))
      - ∑ s, y (.inr (.inr (.inl s))) * F k s + ∑ s, y (.inr (.inr (.inr (.inl s)))) * F k s
      - y (.inr (.inr (.inr (.inr k)))) := by
  simp [Finset.sum_apply, Fintype.sum_sum_type, wv, Pi.single_apply, Finset.sum_neg_distrib]
  ring

lemma obj_eq (lo hi : Fin m → ℝ) (pL pU : Fin K → ℝ) (y : Idx K m → ℝ) :
    y ⬝ᵥ bv lo hi pL pU = -((fun s => y (.inr (.inr (.inl s)))) ⬝ᵥ lo)
      + (fun s => y (.inr (.inr (.inr (.inl s))))) ⬝ᵥ hi
      - (fun k => y (.inl k)) ⬝ᵥ pL + (fun k => y (.inr (.inl k))) ⬝ᵥ pU := by
  simp [dotProduct, Fintype.sum_sum_type, bv, Finset.sum_neg_distrib]
  ring

lemma dot_empty (z w : Empty → ℝ) : z ⬝ᵥ w = 0 := by simp [dotProduct]

lemma dualfeas_iff (F : Fin K → Fin m → ℝ) (Q : Fin K → ℝ)
    (yz : (Idx K m → ℝ) × (Empty → ℝ)) :
    yz ∈ DualityKit.LP.DualFeas (fun i => lf (wv F i)) (fun j : Empty => j.elim) (lf Q) ↔
      0 ≤ yz.1 ∧ ∀ k, -yz.1 (.inl k) + yz.1 (.inr (.inl k))
      - ∑ s, yz.1 (.inr (.inr (.inl s))) * F k s + ∑ s, yz.1 (.inr (.inr (.inr (.inl s)))) * F k s
      - yz.1 (.inr (.inr (.inr (.inr k)))) = Q k := by
  unfold DualityKit.LP.DualFeas
  simp only [Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero, sum_smul_lf]
  refine and_congr Iff.rfl ⟨fun h k => ?_, fun h => ?_⟩
  · rw [← sum_wv, lf_inj h]
  · congr 1; funext k; rw [sum_wv, h k]

lemma pointwise (F : Fin K → Fin m → ℝ) (Q : Fin K → ℝ) (lo hi : Fin m → ℝ)
    (pL pU : Fin K → ℝ)
    (hne : {p : Fin K → ℝ | pL ≤ p ∧ p ≤ pU ∧ lo ≤ ∑ k, p k • F k ∧ ∑ k, p k • F k ≤ hi ∧
      ∀ k, 0 ≤ p k}.Nonempty) :
    ∃ w, IsGreatest {v | ∃ p : Fin K → ℝ, (pL ≤ p ∧ p ≤ pU ∧ lo ≤ ∑ k, p k • F k ∧
        ∑ k, p k • F k ≤ hi ∧ ∀ k, 0 ≤ p k) ∧ v = ∑ k, p k * Q k} w ∧
      IsLeast {d | ∃ (α β : Fin m → ℝ) (γl γu : Fin K → ℝ),
        (0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γl ∧ 0 ≤ γu ∧ ∀ k, Q k ≤ (β - α) ⬝ᵥ F k - γl k + γu k) ∧
        d = -(α ⬝ᵥ lo) + β ⬝ᵥ hi - γl ⬝ᵥ pL + γu ⬝ᵥ pU} w := by
  have hP : (DualityKit.LP.Feas (fun i => lf (wv F i)) (bv lo hi pL pU)
      (fun j : Empty => j.elim) (fun j => j.elim)).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, (feas_iff F lo hi pL pU p).2 hp⟩
  -- dual point from dual-feasible quadruple
  have hmk : ∀ (α β : Fin m → ℝ) (γl γu : Fin K → ℝ),
      (0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γl ∧ 0 ≤ γu ∧ ∀ k, Q k ≤ (β - α) ⬝ᵥ F k - γl k + γu k) →
      ∃ yz ∈ DualityKit.LP.DualFeas (fun i => lf (wv F i)) (fun j : Empty => j.elim) (lf Q),
        yz.1 ⬝ᵥ bv lo hi pL pU + yz.2 ⬝ᵥ (fun j : Empty => j.elim) =
          -(α ⬝ᵥ lo) + β ⬝ᵥ hi - γl ⬝ᵥ pL + γu ⬝ᵥ pU := by
    rintro α β γl γu ⟨hα, hβ, hγl, hγu, hk⟩
    let y : Idx K m → ℝ := fun i => match i with
      | .inl k => γl k
      | .inr (.inl k) => γu k
      | .inr (.inr (.inl s)) => α s
      | .inr (.inr (.inr (.inl s))) => β s
      | .inr (.inr (.inr (.inr k))) => (β - α) ⬝ᵥ F k - γl k + γu k - Q k
    refine ⟨(y, fun j => j.elim), (dualfeas_iff F Q _).2 ⟨?_, fun k => ?_⟩, ?_⟩
    · rintro (k | k | s | s | k)
      · exact hγl k
      · exact hγu k
      · exact hα s
      · exact hβ s
      · show (0 : ℝ) ≤ (β - α) ⬝ᵥ F k - γl k + γu k - Q k
        linarith [hk k]
    · show -γl k + γu k - ∑ s, α s * F k s + ∑ s, β s * F k s
        - ((β - α) ⬝ᵥ F k - γl k + γu k - Q k) = Q k
      simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    · rw [dot_empty, add_zero, obj_eq]

  have hD : (DualityKit.LP.DualFeas (fun i => lf (wv F i)) (fun j : Empty => j.elim)
      (lf Q)).Nonempty := by
    obtain ⟨yz, hyz, -⟩ := hmk 0 0 0 (fun k => max (Q k) 0)
      ⟨le_rfl, le_rfl, le_rfl, fun k => le_max_right _ _, fun k => by simp⟩
    exact ⟨yz, hyz⟩
  obtain ⟨v, hG, hL⟩ := DualityKit.LP.strong_duality (fun i => lf (wv F i)) (bv lo hi pL pU)
    (fun j : Empty => j.elim) (fun j => j.elim) (lf Q) hP hD
  refine ⟨v, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨p, hp, hv⟩ := hG.1
    refine ⟨p, (feas_iff F lo hi pL pU p).1 hp, ?_⟩
    rw [← hv]; simp [dotProduct, mul_comm]
  · rintro _ ⟨p, hp, rfl⟩
    have := hG.2 ⟨p, (feas_iff F lo hi pL pU p).2 hp, rfl⟩
    simpa [dotProduct, mul_comm] using this
  · obtain ⟨yz, hyz, hv⟩ := hL.1
    obtain ⟨hy, hk⟩ := (dualfeas_iff F Q yz).1 hyz
    refine ⟨fun s => yz.1 (.inr (.inr (.inl s))), fun s => yz.1 (.inr (.inr (.inr (.inl s)))),
      fun k => yz.1 (.inl k), fun k => yz.1 (.inr (.inl k)),
      ⟨fun s => hy _, fun s => hy _, fun k => hy _, fun k => hy _, fun k => ?_⟩, ?_⟩
    · have h1 := hk k
      have h2 := hy (.inr (.inr (.inr (.inr k))))
      simp only [Pi.zero_apply] at h2
      simp only [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      linarith
    · rw [← hv]
      beta_reduce
      rw [dot_empty, add_zero, obj_eq]
  · rintro _ ⟨α, β, γl, γu, hF, rfl⟩
    obtain ⟨yz, hyz, hobj⟩ := hmk α β γl γu hF
    rw [← hobj]
    exact hL.2 ⟨yz, hyz, rfl⟩

end RRAux_DDMomentDRO_Type1_theorem_1

open DDMomentDRO.Type1 in
theorem solution {I J K m : ℕ}
    (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ)
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (hne : ∀ x y, (x, y) ∈ S → (amb1 ξ e l u pl pu x).Nonempty) :
    ∀ q : ℝ, IsLeast (stageVals S g (amb1 ξ e l u pl pu) Qn) q ↔
      IsLeast (dualVals1 S g Qn ξ e l u pl pu) q := by
  intro q
  have key := DualityKit.isLeast_add_isGreatest_iff S (fun z => g z.1 z.2)
    (fun z => wcVal (amb1 ξ e l u pl pu) Qn z.1)
    (fun z => {d | ∃ α β γl γu, DualFeas1 Qn ξ e z.1 α β γl γu ∧
      d = dualObj1 l u pl pu z.1 α β γl γu})
    (fun z hz => RRAux_DDMomentDRO_Type1_theorem_1.pointwise (fun k => momentFn e (ξ k))
      (Qn z.1) (l z.1) (u z.1) (pl z.1) (pu z.1) (hne z.1 z.2 hz)) q
  have e1 : stageVals S g (amb1 ξ e l u pl pu) Qn =
      {v | ∃ z ∈ S, ∃ w, IsGreatest (wcVal (amb1 ξ e l u pl pu) Qn z.1) w ∧
        v = g z.1 z.2 + w} := by
    ext v
    constructor
    · rintro ⟨x, y, w, hS, hw, rfl⟩
      exact ⟨(x, y), hS, w, hw, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, w, hw, rfl⟩
      exact ⟨x, y, w, hS, hw, rfl⟩
  have e2 : dualVals1 S g Qn ξ e l u pl pu =
      {v | ∃ z ∈ S, ∃ d ∈ {d | ∃ α β γl γu, DualFeas1 Qn ξ e z.1 α β γl γu ∧
        d = dualObj1 l u pl pu z.1 α β γl γu}, v = g z.1 z.2 + d} := by
    ext v
    constructor
    · rintro ⟨x, y, α, β, γl, γu, hS, hF, rfl⟩
      exact ⟨(x, y), hS, _, ⟨α, β, γl, γu, hF, rfl⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, d, ⟨α, β, γl, γu, hF, rfl⟩, rfl⟩
      exact ⟨x, y, α, β, γl, γu, hS, hF, rfl⟩
  rw [e1, e2]
  exact key

#print axioms solution
