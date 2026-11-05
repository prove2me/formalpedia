-- Prove2me | solution 1 for DRConvexOpt.Reform.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:12:13.759822+00:00
-- url     : https://prove2.me/submissions/beda2daa-a777-46bd-9a7d-889a0082dfa6

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

open MeasureTheory Matrix DRConvexOpt.Reform
open scoped Pointwise

namespace DRCOLem1Aux

lemma tdot {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    (Mᵀ *ᵥ y) ⬝ᵥ z = (M *ᵥ z) ⬝ᵥ y := by
  rw [mulVec_transpose, dotProduct_comm (M *ᵥ z), dotProduct_mulVec]

/-- Conic duality with dual attainment under Slater's condition. -/
lemma conic_farkas {nP nQ m : ℕ} (C : Matrix (Fin m) (Fin nP) ℝ) (D : Matrix (Fin m) (Fin nQ) ℝ)
    (c : Fin m → ℝ) (K : Set (Fin m → ℝ)) (hK : IsProperCone K)
    (ω0 : (Fin nP → ℝ) × (Fin nQ → ℝ)) (hω0 : c - (C *ᵥ ω0.1 + D *ᵥ ω0.2) ∈ interior K)
    (a : Fin nP → ℝ) (g : Fin nQ → ℝ) (r : ℝ)
    (hfeas : ∀ ω : (Fin nP → ℝ) × (Fin nQ → ℝ), c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ K →
      a ⬝ᵥ ω.1 + g ⬝ᵥ ω.2 ≤ r) :
    ∃ φ, φ ∈ dualCone K ∧ c ⬝ᵥ φ ≤ r ∧ Cᵀ *ᵥ φ = a ∧ Dᵀ *ᵥ φ = g := by
  obtain ⟨hKc, hK0, hKadd, hKsmul, -, -⟩ := hK
  set M : (Fin nP → ℝ) × (Fin nQ → ℝ) → Fin m → ℝ := fun ω => C *ᵥ ω.1 + D *ᵥ ω.2 with hM
  set obj : (Fin nP → ℝ) × (Fin nQ → ℝ) → ℝ := fun ω => a ⬝ᵥ ω.1 + g ⬝ᵥ ω.2 with hobj
  have hconvK : Convex ℝ K := fun x hx y hy s t hs ht _ =>
    hKadd _ (hKsmul _ hx s hs) _ (hKsmul _ hy t ht)
  have hconvI : Convex ℝ (interior K) := hconvK.interior
  have hIadd : ∀ p ∈ interior K, ∀ k ∈ K, p + k ∈ interior K := by
    intro p hp k hk
    have : (fun q => q + k) '' interior K ⊆ interior K := by
      apply interior_maximal
      · rintro _ ⟨q, hq, rfl⟩; exact hKadd _ (interior_subset hq) _ hk
      · exact (isOpenMap_add_right k) _ isOpen_interior
    exact this ⟨p, hp, rfl⟩
  have hIsmul : ∀ p ∈ interior K, ∀ t : ℝ, 0 < t → t • p ∈ interior K := by
    intro p hp t ht
    have h1 : t • interior K ⊆ interior K := by
      rw [← interior_smul₀ ht.ne']
      exact interior_mono (fun _ ⟨q, hq, e⟩ => e ▸ hKsmul q hq t ht.le)
    exact h1 ⟨p, hp, rfl⟩
  have hMlin : ∀ (s t : ℝ) ω1 ω2, M (s • ω1 + t • ω2) = s • M ω1 + t • M ω2 := by
    intro s t ω1 ω2
    simp only [hM, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
      mulVec_smul, smul_add]
    abel
  have hobjlin : ∀ (s t : ℝ) ω1 ω2, obj (s • ω1 + t • ω2) = s * obj ω1 + t * obj ω2 := by
    intro s t ω1 ω2
    simp only [hobj, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    ring
  -- the two convex sets
  let S : Set ((Fin m → ℝ) × ℝ) :=
    {p | ∃ ω k, k ∈ K ∧ c - p.1 - M ω - k ∈ interior K ∧ p.2 < obj ω}
  let T : Set ((Fin m → ℝ) × ℝ) := {p | p.1 = 0 ∧ r ≤ p.2}
  have hSopen : IsOpen S := by
    have : S = ⋃ ω, ⋃ k ∈ K, ((fun p : (Fin m → ℝ) × ℝ => c - p.1 - M ω - k) ⁻¹' interior K ∩
        {p | p.2 < obj ω}) := by
      ext p
      simp only [S, Set.mem_iUnion, exists_prop, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq]
    rw [this]
    refine isOpen_iUnion fun ω => isOpen_biUnion fun k _ =>
      (isOpen_interior.preimage (by fun_prop)).inter (isOpen_lt continuous_snd continuous_const)
  have hSconv : Convex ℝ S := by
    rintro p1 ⟨ω1, k1, hk1, h1, h1'⟩ p2 ⟨ω2, k2, hk2, h2, h2'⟩ s t hs ht hst
    refine ⟨s • ω1 + t • ω2, s • k1 + t • k2, hconvK hk1 hk2 hs ht hst, ?_, ?_⟩
    · have e : c - (s • p1 + t • p2).1 - M (s • ω1 + t • ω2) - (s • k1 + t • k2) =
          s • (c - p1.1 - M ω1 - k1) + t • (c - p2.1 - M ω2 - k2) := by
        rw [hMlin]
        have hc : c = s • c + t • c := by rw [← add_smul, hst, one_smul]
        conv_lhs => rw [hc]
        simp only [Prod.fst_add, Prod.smul_fst, smul_sub]
        abel
      rw [e]; exact hconvI h1 h2 hs ht hst
    · rw [hobjlin]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rcases hs.eq_or_lt with hs0 | hs0
      · subst hs0; have : t = 1 := by linarith
        subst this; simpa using h2'
      · nlinarith [mul_lt_mul_of_pos_left h1' hs0, mul_le_mul_of_nonneg_left h2'.le ht]
  have hTconv : Convex ℝ T := by
    rintro p1 ⟨h1, h1'⟩ p2 ⟨h2, h2'⟩ s t hs ht hst
    refine ⟨?_, ?_⟩
    · show s • p1.1 + t • p2.1 = 0
      rw [h1, h2]; simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have : r = s * r + t * r := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1' hs, mul_le_mul_of_nonneg_left h2' ht]
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    rintro p ⟨ω, k, hk, h1, h2⟩ ⟨hp1, hp2⟩
    rw [hp1, sub_zero] at h1
    have hfe : c - M ω ∈ K := by
      have := hKadd _ (interior_subset h1) _ hk
      simpa using this
    have := hfeas ω hfe
    simp only [hobj] at h2
    linarith
  obtain ⟨f, u, hfS, hfT⟩ := geometric_hahn_banach_open hSconv hSopen hTconv hdisj
  -- coordinates of the separating functional
  let ψ : Fin m → ℝ := fun k => f (Pi.single k 1, 0)
  set θ : ℝ := f (0, 1) with hθ
  have hrep : ∀ y s, f (y, s) = ψ ⬝ᵥ y + θ * s := by
    intro y s
    have e : ((y, s) : (Fin m → ℝ) × ℝ) =
        ∑ k, y k • ((Pi.single k (1 : ℝ) : Fin m → ℝ), (0 : ℝ)) + s • ((0 : Fin m → ℝ), (1 : ℝ)) := by
      ext j
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [e, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, dotProduct, ψ, θ]
    have hc : ∀ k, y k * f (Pi.single k 1, 0) = f (Pi.single k 1, 0) * y k := fun k => mul_comm _ _
    simp only [hc]; ring
  -- `θ ≥ 0` and `u ≤ θ r`
  have hTu : ∀ s, r ≤ s → u ≤ θ * s := by
    intro s hs
    have := hfT (0, s) ⟨rfl, hs⟩
    rwa [hrep, dotProduct_zero, zero_add] at this
  have hθnn : 0 ≤ θ := by
    by_contra hneg
    push Not at hneg
    have := hTu (max r ((u - 1) / θ)) (le_max_left _ _)
    have h2 : θ * max r ((u - 1) / θ) ≤ θ * ((u - 1) / θ) :=
      mul_le_mul_of_nonpos_left (le_max_right _ _) hneg.le
    rw [mul_div_cancel₀ _ hneg.ne] at h2
    linarith
  have hSu : ∀ ω k, k ∈ K → ∀ q ∈ interior K, ∀ δ > 0,
      ψ ⬝ᵥ (c - M ω - k - q) + θ * (obj ω - δ) < u := by
    intro ω k hk q hq δ hδ
    have := hfS (c - M ω - k - q, obj ω - δ) ⟨ω, k, hk, by rw [show c - (c - M ω - k - q) - M ω - k = q by abel]; exact hq,
      by show obj ω - δ < obj ω; linarith⟩
    rwa [hrep] at this
  have hu : u ≤ θ * r := hTu r le_rfl
  -- `θ > 0`, using the Slater point
  have hθpos : 0 < θ := by
    rcases hθnn.eq_or_lt with h0 | h0
    · exfalso
      have := hfS (0, obj ω0 - 1) ⟨ω0, 0, hK0, by simpa [hM] using hω0, by simp⟩
      rw [hrep, dotProduct_zero, ← h0, zero_mul, zero_add] at this
      rw [← h0, zero_mul] at hu
      linarith
    · exact h0
  set k0 := c - M ω0 with hk0
  have hk0I : k0 ∈ interior K := by simpa [hk0, hM] using hω0
  -- `ψ ∈ K⋆`
  have hψK : ∀ k ∈ K, 0 ≤ ψ ⬝ᵥ k := by
    intro k hk
    by_contra hneg
    push Not at hneg
    set Mb := θ * r - θ * (obj 0 - 1) - ψ ⬝ᵥ (c - M 0 - k0) with hMb
    set n : ℝ := |Mb| / (-(ψ ⬝ᵥ k)) with hn
    have hnpos : 0 ≤ n := div_nonneg (abs_nonneg _) (by linarith)
    have := hSu 0 (n • k) (hKsmul _ hk n hnpos) k0 hk0I 1 one_pos
    have e : ψ ⬝ᵥ (c - M 0 - n • k - k0) = ψ ⬝ᵥ (c - M 0 - k0) - n * (ψ ⬝ᵥ k) := by
      simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]; ring
    rw [e] at this
    have hnk : n * (-(ψ ⬝ᵥ k)) = |Mb| := div_mul_cancel₀ _ (by linarith)
    have := le_abs_self Mb
    nlinarith
  -- the Lagrangian inequality
  have hlag : ∀ ω, ψ ⬝ᵥ (c - M ω) + θ * obj ω ≤ θ * r := by
    intro ω
    by_contra hgt
    push Not at hgt
    set gap := ψ ⬝ᵥ (c - M ω) + θ * obj ω - θ * r with hgap
    have hgap0 : 0 < gap := by linarith
    set ε := min 1 (gap / (2 * (|ψ ⬝ᵥ k0| + θ + 1))) with hε
    have hden : 0 < 2 * (|ψ ⬝ᵥ k0| + θ + 1) := by positivity
    have hε0 : 0 < ε := lt_min one_pos (div_pos hgap0 hden)
    have hεle : ε ≤ gap / (2 * (|ψ ⬝ᵥ k0| + θ + 1)) := min_le_right _ _
    have := hSu ω 0 hK0 (ε • k0) (hIsmul _ hk0I ε hε0) ε hε0
    have e : ψ ⬝ᵥ (c - M ω - 0 - ε • k0) = ψ ⬝ᵥ (c - M ω) - ε * (ψ ⬝ᵥ k0) := by
      simp only [sub_zero, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [e] at this
    have h1 : ε * (2 * (|ψ ⬝ᵥ k0| + θ + 1)) ≤ gap := (le_div_iff₀ hden).mp hεle
    have h2 : ε * (ψ ⬝ᵥ k0) ≤ ε * |ψ ⬝ᵥ k0| := mul_le_mul_of_nonneg_left (le_abs_self _) hε0.le
    nlinarith
  -- the linear part must vanish
  have hlin : ∀ ω, θ * obj ω - ψ ⬝ᵥ M ω = 0 := by
    have hb : ∀ ω, θ * obj ω - ψ ⬝ᵥ M ω ≤ θ * r - ψ ⬝ᵥ c := by
      intro ω; have := hlag ω; rw [dotProduct_sub] at this; linarith
    have hscale : ∀ (t : ℝ) ω, θ * obj (t • ω) - ψ ⬝ᵥ M (t • ω) = t * (θ * obj ω - ψ ⬝ᵥ M ω) := by
      intro t ω
      have h1 := hobjlin t 0 ω 0
      have h2 := hMlin t 0 ω 0
      simp only [zero_smul, add_zero] at h1 h2
      rw [h1, h2]
      simp only [hobj, hM, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mulVec_zero, add_zero,
        smul_zero, mul_zero, dotProduct_smul, smul_eq_mul]
      ring
    intro ω
    by_contra hne
    set L := θ * obj ω - ψ ⬝ᵥ M ω
    set R := θ * r - ψ ⬝ᵥ c
    have := hb (((|R| + 1) / L) • ω)
    rw [hscale, div_mul_cancel₀ _ hne] at this
    have := le_abs_self R
    linarith
  -- read off the equality constraints
  refine ⟨θ⁻¹ • ψ, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
    exact mul_nonneg (inv_nonneg.mpr hθnn) (hψK k hk)
  · have := hlag 0
    simp only [hM, hobj, Prod.fst_zero, Prod.snd_zero, mulVec_zero, add_zero, sub_zero,
      dotProduct_zero, mul_zero] at this
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm, inv_mul_le_iff₀ hθpos]
    exact this
  · ext j
    have := hlin (Pi.single j 1, 0)
    simp only [hM, hobj, mulVec_zero, add_zero, dotProduct_zero] at this
    rw [dotProduct_comm ψ, ← tdot, dotProduct_single, dotProduct_single, mul_one, mul_one] at this
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  · ext j
    have := hlin (0, Pi.single j 1)
    simp only [hM, hobj, mulVec_zero, zero_add, dotProduct_zero] at this
    rw [dotProduct_comm ψ, ← tdot, dotProduct_single, dotProduct_single, mul_one, mul_one] at this
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith

end DRCOLem1Aux

open DRCOLem1Aux in
theorem solution {nP nQ nN nL m : ℕ} [NeZero nL]
    (C : Matrix (Fin m) (Fin nP) ℝ) (D : Matrix (Fin m) (Fin nQ) ℝ) (c : Fin m → ℝ)
    (K : Set (Fin m → ℝ)) (hK : IsProperCone K)
    (hslater : ∃ ω : (Fin nP → ℝ) × (Fin nQ → ℝ), c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ interior K)
    (v : PWAff nN nP nL) (x : Fin nN → ℝ) (f : Fin nP → ℝ) (g : Fin nQ → ℝ) (h : ℝ) :
    (∀ ω ∈ confSet C D c K, v.eval x ω.1 + f ⬝ᵥ ω.1 + g ⬝ᵥ ω.2 ≤ h) ↔
    ∃ φ : Fin nL → Fin m → ℝ, ∀ l, φ l ∈ dualCone K ∧ c ⬝ᵥ φ l + v.s l ⬝ᵥ x + v.t0 l ≤ h ∧
      Cᵀ *ᵥ φ l = (v.S l)ᵀ *ᵥ x + v.tv l + f ∧ Dᵀ *ᵥ φ l = g := by
  constructor
  · intro H
    obtain ⟨ω0, hω0⟩ := hslater
    have : ∀ l, ∃ φ, φ ∈ dualCone K ∧ c ⬝ᵥ φ ≤ h - v.s l ⬝ᵥ x - v.t0 l ∧
        Cᵀ *ᵥ φ = (v.S l)ᵀ *ᵥ x + v.tv l + f ∧ Dᵀ *ᵥ φ = g := by
      intro l
      refine conic_farkas C D c K hK ω0 hω0 _ g _ fun ω hω => ?_
      have h1 := H ω hω
      have h2 : (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l) ≤ v.eval x ω.1 :=
        Finset.le_sup' (fun l => (v.S l *ᵥ ω.1 + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ ω.1 + v.t0 l))
          (Finset.mem_univ l)
      simp only [add_dotProduct, tdot] at h2 ⊢
      linarith
    choose φ hφ using this
    exact ⟨φ, fun l => ⟨(hφ l).1, by linarith [(hφ l).2.1], (hφ l).2.2.1, (hφ l).2.2.2⟩⟩
  · rintro ⟨φ, hφ⟩ ω hω
    have : v.eval x ω.1 ≤ h - f ⬝ᵥ ω.1 - g ⬝ᵥ ω.2 := by
      unfold PWAff.eval
      refine Finset.sup'_le _ _ fun l _ => ?_
      obtain ⟨hd, h1, h2, h3⟩ := hφ l
      have hd' := hd _ hω
      have e2 := congrArg (· ⬝ᵥ ω.1) h2
      have e3 := congrArg (· ⬝ᵥ ω.2) h3
      simp only [add_dotProduct, tdot] at e2 e3
      simp only [sub_dotProduct, add_dotProduct] at hd'
      simp only [add_dotProduct]
      linarith
    linarith
