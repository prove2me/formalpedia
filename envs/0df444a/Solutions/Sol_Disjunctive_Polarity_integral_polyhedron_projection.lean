-- Prove2me | solution 1 for Disjunctive.Polarity.integral_polyhedron_projection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:46:18.444659+00:00
-- url     : https://prove2.me/submissions/568216cd-8374-4354-a823-92daf1687f44

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_WeylPolyhedra_Shared_Representable

open Matrix Module Disjunctive.Polarity

lemma ip_rep_mono {n : ℕ} {T S : Finset (Fin n → ℝ)} (h : T ⊆ S) {x : Fin n → ℝ}
    (hx : WeylPolyhedra.Shared.Representable T x) : WeylPolyhedra.Shared.Representable S x := by
  classical
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨fun v => if v ∈ T then c v else 0, fun s _ => ?_, ?_⟩
  · dsimp only
    split_ifs with h'
    · exact hc s h'
    · exact le_rfl
  rw [← Finset.sum_subset h (fun v _ hv => by simp [hv])]
  exact Finset.sum_congr rfl fun v hv => by simp [hv]

lemma ip_cara {n : ℕ} (x : Fin n → ℝ) : ∀ (k : ℕ) (S : Finset (Fin n → ℝ)), S.card = k →
    WeylPolyhedra.Shared.Representable S x →
    ∃ T ⊆ S, LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ WeylPolyhedra.Shared.Representable T x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hk ⟨c, hc0, hx⟩
  by_cases hli : LinearIndependent ℝ (fun t : S => (t : Fin n → ℝ))
  · exact ⟨S, subset_rfl, hli, c, hc0, hx⟩
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  classical
  let G : (Fin n → ℝ) → ℝ := fun v => if h : v ∈ S then g ⟨v, h⟩ else 0
  have hG : ∑ s ∈ S, G s • s = 0 := by
    rw [← hg, ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun s _ => by simp [G, s.2]
  have hGi : G i ≠ 0 := by simpa [G, i.2] using hi
  obtain ⟨H, hH, s1, hs1, hpos⟩ : ∃ H : (Fin n → ℝ) → ℝ, ∑ s ∈ S, H s • s = 0 ∧
      ∃ s1 ∈ S, 0 < H s1 := by
    rcases lt_or_gt_of_ne hGi with h | h
    · refine ⟨fun v => - G v, ?_, i, i.2, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, hG]
    · exact ⟨G, hG, i, i.2, h⟩
  let P := S.filter (fun s => 0 < H s)
  obtain ⟨s0, hs0P, hmin⟩ := P.exists_min_image (fun s => c s / H s)
    ⟨s1, by simp [P, hs1, hpos]⟩
  have hs0 : s0 ∈ S ∧ 0 < H s0 := by simpa [P] using hs0P
  set t := c s0 / H s0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 s0 hs0.1) hs0.2.le
  let c' : (Fin n → ℝ) → ℝ := fun s => c s - t * H s
  have hc' : ∀ s ∈ S, 0 ≤ c' s := by
    intro s hs
    by_cases hHs : 0 < H s
    · have := hmin s (by simp [P, hs, hHs])
      rw [le_div_iff₀ hHs] at this
      simp only [c']; linarith
    · push Not at hHs
      have := hc0 s hs
      simp only [c']; nlinarith
  have hc's0 : c' s0 = 0 := by
    simp only [c', t]; rw [div_mul_cancel₀ _ hs0.2.ne']; ring
  have hx' : x = ∑ s ∈ S.erase s0, c' s • s := by
    rw [Finset.sum_erase S (by simp [hc's0])]
    simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hH, hx]
    simp
  obtain ⟨T, hTS, hTli, hTr⟩ := ih _ (by rw [← hk]; exact Finset.card_erase_lt_of_mem hs0.1)
    (S.erase s0) rfl ⟨c', fun s hs => hc' s (Finset.mem_of_mem_erase hs), hx'⟩
  exact ⟨T, hTS.trans (Finset.erase_subset _ _), hTli, hTr⟩

lemma ip_cone_indep_closed {n : ℕ} (T : Finset (Fin n → ℝ))
    (hT : LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ))) :
    IsClosed {x | WeylPolyhedra.Shared.Representable T x} := by
  classical
  let L : (T → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Fintype.linearCombination ℝ (fun t : T => (t : Fin n → ℝ))
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have := Fintype.linearIndependent_iff.1 hT m (by simpa [L, Fintype.linearCombination_apply] using hm)
    funext i; exact this i
  have hset : {x | WeylPolyhedra.Shared.Representable T x} = L '' {c | ∀ i, 0 ≤ c i} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => c i, fun i => hc i i.2, ?_⟩
      simp only [L, Fintype.linearCombination_apply]
      exact Finset.sum_coe_sort T (fun s => c s • s)
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun v => if h : v ∈ T then c ⟨v, h⟩ else 0, fun s hs => by simp [hs, hc], ?_⟩
      simp only [L, Fintype.linearCombination_apply]
      rw [← Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl fun s _ => by simp [s.2]
  rw [hset]
  apply (LinearMap.isClosedEmbedding_of_injective hL).isClosedMap
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

lemma ip_cone_closed {n : ℕ} (S : Finset (Fin n → ℝ)) :
    IsClosed {x | WeylPolyhedra.Shared.Representable S x} := by
  classical
  let F : Finset (Finset (Fin n → ℝ)) := S.powerset.filter
      (fun T : Finset (Fin n → ℝ) => LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)))
  have : {x | WeylPolyhedra.Shared.Representable S x} = ⋃ T ∈ F, {x | WeylPolyhedra.Shared.Representable T x} := by
    ext x
    simp only [F, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      obtain ⟨T, hTS, hli, hr⟩ := ip_cara x _ S rfl h
      exact ⟨T, ⟨hTS, hli⟩, hr⟩
    · rintro ⟨T, ⟨hTS, _⟩, hr⟩
      exact ip_rep_mono hTS hr
  rw [this]
  exact isClosed_biUnion_finset fun T hT => ip_cone_indep_closed T (Finset.mem_filter.1 hT).2


lemma ip_gen_cone_closed {m : ℕ} {ι : Type} [Fintype ι] (g : ι → (Fin m → ℝ)) :
    IsClosed {y : Fin m → ℝ | ∃ c : ι → ℝ, 0 ≤ c ∧ y = ∑ i, c i • g i} := by
  classical
  have : {y : Fin m → ℝ | ∃ c : ι → ℝ, 0 ≤ c ∧ y = ∑ i, c i • g i} =
      {y | WeylPolyhedra.Shared.Representable (Finset.univ.image g) y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun s => ∑ i ∈ Finset.univ.filter (fun i => g i = s), c i,
        fun s _ => Finset.sum_nonneg fun i _ => hc i, ?_⟩
      conv_lhs => rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
        (t := Finset.univ.image g) (g := g)
        (fun i _ => Finset.mem_image_of_mem g (Finset.mem_univ i))]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    · rintro ⟨c, hc, rfl⟩
      set k : ι → ℝ := fun i => ((Finset.univ.filter (fun j => g j = g i)).card : ℝ) with hk
      have hkpos : ∀ i, 0 < k i := fun i => by
        simp only [hk]; exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩
      refine ⟨fun i => c (g i) / k i,
        fun i => div_nonneg (hc _ (Finset.mem_image_of_mem g (Finset.mem_univ i))) (hkpos i).le, ?_⟩
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image g)
        (g := g) (fun i _ => Finset.mem_image_of_mem g (Finset.mem_univ i))]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hfib : ∀ i ∈ Finset.univ.filter (fun i => g i = s),
          (c (g i) / k i) • g i = (c s / ((Finset.univ.filter (fun j => g j = s)).card : ℝ)) • s := by
        intro i hi
        have hi' : g i = s := (Finset.mem_filter.mp hi).2
        simp only [hk, hi']
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      have hpos : 0 < ((Finset.univ.filter (fun j => g j = s)).card : ℝ) := by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
        exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩
      field_simp
  rw [this]
  exact ip_cone_closed _

theorem solution {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (hInt : IsIntegralPair (Poly2 A B b)) :
    IsIntegral (ProjOntoX (Poly2 A B b)) := by
  classical
  -- the projection is a preimage of a finitely generated cone
  let g : Fin p ⊕ Fin p ⊕ Fin m → (Fin m → ℝ) :=
    Sum.elim (fun j i => A i j) (Sum.elim (fun j i => -A i j) (fun k => Pi.single k 1))
  have hProj : ProjOntoX (Poly2 A B b) =
      (fun x => b - B.mulVec x) ⁻¹' {y | ∃ c : Fin p ⊕ Fin p ⊕ Fin m → ℝ, 0 ≤ c ∧
        y = ∑ i, c i • g i} := by
    ext x
    simp only [ProjOntoX, Poly2, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨Sum.elim (fun j => max (u j) 0) (Sum.elim (fun j => max (-u j) 0)
        (fun k => (b - B.mulVec x - A.mulVec u) k)), ?_, ?_⟩
      · rintro (j | j | k)
        · simp
        · simp
        · have := hu k
          simp only [Pi.add_apply] at this
          simp only [Sum.elim_inr, Pi.zero_apply, Pi.sub_apply]
          linarith
      · funext i
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, g, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, mulVec, dotProduct]
        have : ∀ j, max (u j) 0 * A i j + max (-u j) 0 * -A i j = A i j * u j := by
          intro j
          rcases le_total (u j) 0 with h | h
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
        rw [← add_assoc, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun j _ => this j]
        ring
    · rintro ⟨c, hc, hcx⟩
      refine ⟨fun j => c (Sum.inl j) - c (Sum.inr (Sum.inl j)), fun i => ?_⟩
      have hi := congrFun hcx i
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, g, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply] at hi
      have hk := hc (Sum.inr (Sum.inr i))
      simp only [Pi.zero_apply] at hk
      simp only [Pi.add_apply, mulVec, dotProduct] at hi ⊢
      have e : ∑ j, A i j * (c (Sum.inl j) - c (Sum.inr (Sum.inl j))) =
          ∑ j, c (Sum.inl j) * A i j + ∑ j, c (Sum.inr (Sum.inl j)) * -A i j := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      rw [e]
      linarith
  have hclosed : IsClosed (ProjOntoX (Poly2 A B b)) := by
    rw [hProj]
    exact (ip_gen_cone_closed g).preimage (by fun_prop)
  have hconv : Convex ℝ (ProjOntoX (Poly2 A B b)) := by
    rintro x1 ⟨u1, hu1⟩ x2 ⟨u2, hu2⟩ s t hs ht hst
    refine ⟨s • u1 + t • u2, ?_⟩
    simp only [Poly2, Set.mem_setOf_eq] at hu1 hu2 ⊢
    intro i
    have h1 := hu1 i
    have h2 := hu2 i
    simp only [Pi.add_apply, mulVec_add, mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have e : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  have hsnd : ProjOntoX (Poly2 A B b) = Prod.snd '' (Poly2 A B b) := by
    ext x; simp [ProjOntoX]
  apply le_antisymm
  · -- `Proj(cl conv IP) ⊆ cl conv IX`
    intro x hx
    rw [hsnd, hInt] at hx
    have h1 : Prod.snd '' closure (convexHull ℝ
        {ux ∈ Poly2 A B b | (∀ i, ∃ k : ℤ, ux.1 i = (k : ℝ)) ∧ ∀ j, ∃ k : ℤ, ux.2 j = (k : ℝ)}) ⊆
        closure (Prod.snd '' convexHull ℝ
        {ux ∈ Poly2 A B b | (∀ i, ∃ k : ℤ, ux.1 i = (k : ℝ)) ∧ ∀ j, ∃ k : ℤ, ux.2 j = (k : ℝ)}) :=
      image_closure_subset_closure_image continuous_snd
    refine closure_mono ?_ (h1 hx)
    rw [show (Prod.snd : (Fin p → ℝ) × (Fin q → ℝ) → (Fin q → ℝ)) =
      (LinearMap.snd ℝ (Fin p → ℝ) (Fin q → ℝ)) from rfl, LinearMap.image_convexHull]
    apply convexHull_mono
    rintro _ ⟨ux, ⟨hux, -, hint⟩, rfl⟩
    exact ⟨⟨ux.1, hux⟩, hint⟩
  · exact closure_minimal (convexHull_min (fun x hx => hx.1) hconv) hclosed

#print axioms solution
